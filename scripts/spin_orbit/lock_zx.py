#!/usr/bin/env python3
"""LOCK-DATA DELTA-LAM-3: whitened `zdecs` rows (untrusted tooling; `KAM/SpinOrbit/Data/LockN65/ZCodeX.lean`).

`zdecs [(k, 0x…), …]` (ZCode) decodes each row literal through the intermediates `n / 256^j`. For rows of large
fixed-point coefficients those big literals share their low 64 bits massively, and the kernel's caches (which key a
large `Nat` literal by its low limb) degrade to long collision chains within one declaration: about n^2.5, and hours
for a route-E segment that decodes many such models in one `decide +kernel` (lam: Low.S62/S281/S383/…).

`whiten_text` rewrites every `zdecs [rows]` literal of a generated module as `zdecsX s [rows']`:
* `s` = the salt of the occurrence (crc32 of the enclosing definition's name and the occurrence's index, mod 2^16);
* row `r`'s byte `j` is stored XOR `zkey s r j` over the row's exact byte length (its `k` varints, trailing zero
  bytes included), so the decoding intermediates have pseudo-random low limbs; the row count and the line layout
  are unchanged.
Every row is checked here: the Python mirror of `zdecX` on the whitened row equals the mirror of `zdec` on the
original. The data stay untrusted; the kernel checks whatever `zdecsX` denotes.

    python3 lock_zx.py apply ROOT OVERLAY LIST [--out CHANGED]
        every file of LIST (paths relative to ROOT, read through its links) that changes is written, as a new file,
        to OVERLAY at the same path
    python3 lock_zx.py check ROOT LIST     rc 0 iff no file of LIST changes (an applied tree)
"""
import os
import re
import sys
import zlib

ZCODEX = "KAM.SpinOrbit.Data.LockN65.ZCodeX"
_ROW = re.compile(r"\((\s*)(\d+),(\s*)0x([0-9a-f]+)(\s*)\)")
_OPEN = re.compile(r"\bzdecs \[")
_DEF = re.compile(r"^(?:def|theorem|abbrev) (\S+)", re.M)
_IMP = re.compile(r"^public import (\S+)$", re.M)


def zkey(s, r, j):
    return (s * 167 + r * 199 + j * 131 + r * j * 59 + 97) % 256


def _unzig(v):
    return v // 2 if v % 2 == 0 else -((v + 1) // 2)


def zdec_row(k, n):
    """the mirror of `zdec k n`: the entries and the number of bytes read"""
    vals, j = [], 0
    for _ in range(k):
        acc, sh = 0, 0
        for _f in range(24):
            b = (n >> (8 * j)) & 255
            j += 1
            if b < 128:
                acc += b << sh
                break
            acc += (b - 128) << sh
            sh += 7
        vals.append(_unzig(acc))
    return vals, j


def zdecx_row(s, r, k, n):
    """the mirror of `zdecX s r k 0 n`"""
    vals, j = [], 0
    for _ in range(k):
        acc, sh = 0, 0
        for _f in range(24):
            b = ((n >> (8 * j)) & 255) ^ zkey(s, r, j)
            j += 1
            if b < 128:
                acc += b << sh
                break
            acc += (b - 128) << sh
            sh += 7
        vals.append(_unzig(acc))
    return vals


def whiten_row(s, r, k, n):
    vals, length = zdec_row(k, n)
    out = 0
    for j in range(length):
        out |= (((n >> (8 * j)) & 255) ^ zkey(s, r, j)) << (8 * j)
    assert zdecx_row(s, r, k, out) == vals, (s, r, k, hex(n))
    return out


def _close(text, i):
    depth, j = 0, i
    while True:
        c = text[j]
        if c == "[":
            depth += 1
        elif c == "]":
            if depth == 0:
                return j
            depth -= 1
        j += 1


def whiten_text(text):
    """every `zdecs [rows]` literal as `zdecsX s [rows']`; returns (text, changed). Idempotent."""
    out, pos, seen = [], 0, {}
    for m in _OPEN.finditer(text):
        if m.start() < pos:
            continue
        defs = list(_DEF.finditer(text, 0, m.start()))
        name = defs[-1].group(1) if defs else ""
        idx = seen.get(name, 0)
        seen[name] = idx + 1
        s = zlib.crc32(("%s#%d" % (name, idx)).encode()) & 0xffff
        end = _close(text, m.end())
        body = text[m.end():end]
        r = [0]

        def sub(mm):
            k, n = int(mm.group(2)), int(mm.group(4), 16)
            w = whiten_row(s, r[0], k, n)
            r[0] += 1
            return "(%s%d,%s0x%x%s)" % (mm.group(1), k, mm.group(3), w, mm.group(5))
        body2 = _ROW.sub(sub, body)
        assert not _ROW.sub("", body2).replace(",", "").strip(), "unexpected row syntax near %r" % name
        out.append(text[pos:m.start()] + "zdecsX %d [" % s + body2 + "]")
        pos = end + 1
    if not out:
        return text, False
    out.append(text[pos:])
    t = "".join(out)
    if ("public import %s\n" % ZCODEX) not in t:
        lines = t.split("\n")
        imp = [i for i, l in enumerate(lines) if l.startswith("public import ")]
        if imp:
            # right after `ZCode` (the emitters that append their imports), else at the first larger import (the
            # sorted position, in the emitters that sort them)
            zc = [i for i in imp if lines[i] == "public import KAM.SpinOrbit.Data.LockN65.ZCode"]
            at = zc[0] + 1 if zc else next((i for i in imp if lines[i] > "public import " + ZCODEX), imp[-1] + 1)
            lines.insert(at, "public import " + ZCODEX)
            t = "\n".join(lines)
    for i, line in enumerate(t.split("\n")):
        assert len(line) <= 100, (i, len(line), line)
    assert t.count("\n") <= 1500
    return t, True


def main(argv):
    if argv[0] == "check":
        root, lst = argv[1], argv[2]
        bad = [r for r in open(lst).read().split() if whiten_text(open(os.path.join(root, r)).read())[1]]
        print("changed by the transform: %d" % len(bad))
        return 1 if bad else 0
    root, overlay, lst = argv[1], argv[2], argv[3]
    outp = argv[argv.index("--out") + 1] if "--out" in argv else None
    changed = []
    for r in open(lst).read().split():
        t, ch = whiten_text(open(os.path.join(root, r)).read())
        if not ch:
            continue
        p = os.path.join(overlay, r)
        os.makedirs(os.path.dirname(p), exist_ok=True)
        if os.path.lexists(p):
            os.remove(p)                       # a new file, never through a link
        with open(p, "w") as f:
            f.write(t)
        changed.append(r)
    print("changed %d" % len(changed))
    if outp:
        with open(outp, "w") as f:
            f.write("".join(r + "\n" for r in changed))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
