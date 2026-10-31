#!/usr/bin/env python3
"""LOCK-DATA (B3 lever (a)): the lock's advice books with compact window literals (untrusted tooling).

`emit_advice_z` is `sofx_lean.emit_advice` with one change: a long window (its run-length tokens, still decoded
by `unzero`) is written as `def … : List ℤ := zdecs [(k, 0x…), …]` (`KAM/SpinOrbit/Data/LockN65/ZCode.lean`:
zigzag base-128 varints, whole entries in hex chunks of at most 40 bytes) instead of a `List ℤ` literal.  The
denoted advice is identical (measured on `AdvFull000`: elaboration 115 s -> 3.1 s, kernel decode 0.19 ms per
entry, the decoded lists equal to the literal ones by `decide +kernel`).
"""
import re

import sofx_lean as SL

ZCODE = "KAM.SpinOrbit.Data.LockN65.ZCode"
CHUNK = 40          # bytes per hex literal (one source line of <= 91 columns)
LINES = 1200        # hex lines per window definition (longer windows are split and flattened)


def varint(v):
    z = 2 * v if v >= 0 else -2 * v - 1
    b = bytearray()
    while True:
        if z < 128:
            b.append(z)
            return bytes(b)
        b.append(128 + (z & 127))
        z >>= 7


def chunks(vals):
    """(count, little-endian chunk) pairs, each chunk holding whole varints in at most CHUNK bytes."""
    out, cur, k = [], b"", 0
    for v in vals:
        e = varint(v)
        assert len(e) <= CHUNK
        if cur and len(cur) + len(e) > CHUNK:
            out.append((k, cur))
            cur, k = b"", 0
        cur += e
        k += 1
    if k:
        out.append((k, cur))
    return out


def zdecs_lines(dn, vals):
    cs = chunks(vals)
    body = ["def %s : List ℤ := zdecs [" % dn]
    for i, (k, b) in enumerate(cs):
        body.append("  (%d, 0x%x)" % (k, int.from_bytes(b, "little")) + ("," if i + 1 < len(cs) else "]"))
    return body


def decode_check(vals):
    """the Python mirror of `zdecs` on the emitted chunks (equal to `vals`)."""
    out = []
    for k, b in chunks(vals):
        n = int.from_bytes(b, "little")
        for _ in range(k):
            acc, sh = 0, 0
            for _f in range(24):
                d = n % 256
                n //= 256
                if d < 128:
                    acc += d << sh
                    break
                acc += (d - 128) << sh
                sh += 7
            out.append(acc // 2 if acc % 2 == 0 else -((acc + 1) // 2))
    return out


def emit_advice_z(tree, book_name, entries):
    """entries: [(key, adv)] (the JSON form of `sofx_gen.adv_json`).  Returns the index module."""
    files, cur, curlen = [], [], 0
    prods = []
    for pi, (key, adv) in enumerate(entries):
        pname = "%s.p%d" % (book_name, pi)
        if adv[0] == "direct":
            prods.append((key, None))
            continue
        P = adv[1]
        defs, parts = [], []
        for part, a in zip(SL_PARTS, adv[2:]):
            wins = []
            for wi, w in enumerate(a["rounded"]):
                if len(SL.tokens_rows(w)) <= 2:
                    ts = [SL.num(t) for t in w]
                    ts = [x + "," for x in ts[:-1]] + [ts[-1] + "]"]
                    ts[0] = "unzero [" + ts[0]
                    wins.append(ts)
                    continue
                assert decode_check(w) == list(w)
                cs = chunks(w)
                groups, acc = [], []
                for k, b in cs:
                    acc.append((k, b))
                    if len(acc) >= LINES:
                        groups.append(acc)
                        acc = []
                if acc:
                    groups.append(acc)
                cn = []
                start = 0
                for ci, gch in enumerate(groups):
                    n = sum(k for k, _ in gch)
                    dn = "%s.%sW%dC%d" % (pname, part, wi, ci)
                    defs.append(zdecs_lines(dn, w[start:start + n]) + [""])
                    start += n
                    cn.append(dn)
                assert start == len(w)
                if len(cn) == 1:
                    wins.append(["unzero %s" % cn[0]])
                else:
                    toks = [c + "," for c in cn[:-1]] + [cn[-1] + "])"]
                    toks[0] = "unzero (List.flatten [" + toks[0]
                    wins.append(toks)
            body = ["def %s.%s : PackedAdvice where" % (pname, part),
                    "  la := " + SL.lay(a["la"]), "  lb := " + SL.lay(a["lb"]), "  target := " + SL.lay(a["target"]),
                    "  scale := %d" % a["scale"], "  outLog := %d" % a["outLog"],
                    "  rounded := [" if wins else "  rounded := []"]
            for wi, w in enumerate(wins):
                body += SL.row_lines(w[:-1] + [w[-1] + ("," if wi + 1 < len(wins) else "]")], "    ")
            defs.append(body + [""])
            parts.append("%s.%s" % (pname, part))
        prods.append((key, (P, parts)))
        for d in defs:
            if curlen + len(d) > SL.MAXLINES and cur:
                files.append(cur)
                cur, curlen = [], 0
            cur.append(d)
            curlen += len(d)
    if cur:
        files.append(cur)
    mods, owner = [], {}
    for fi, defs in enumerate(files):
        rel = "%s%03d" % (book_name.replace(".", ""), fi)
        for d in defs:
            owner[d[0].split()[1]] = fi
        # import only the earlier parts whose definitions this part references (no chain: parts elaborate in
        # parallel lanes)
        refs = {owner[n] for d in defs for l in d[1:] for n in re.findall(r"[A-Za-z0-9_.]+", l)
                if owner.get(n, fi) != fi}
        tree.write(rel, [SL.FORMAT, ZCODE] + [mods[i] for i in sorted(refs)], "Advice book `%s`, part %d (generated)" % (book_name, fi),
                   "Packed-product advice (run-length coded windows, compact `zdecs` literals).\n"
                   "Generated by `scripts/spin_orbit/lock_zadv.py`. Do not edit.", [l for d in defs for l in d])
        mods.append(tree.module(rel))
    body = ["def %s : AdviceBook := [" % book_name]
    for i, (key, p) in enumerate(prods):
        end = "," if i + 1 < len(prods) else "]"
        k = "[" + ", ".join(str(x) for x in key) + "]"
        if p is None:
            body.append("  (%s, .direct)%s" % (k, end))
        else:
            P, parts = p
            body += SL.row_lines(["(%s, .packed %d" % (k, P)] + parts[:-1] + [parts[-1] + ")" + end], "  ")
    rel = book_name.replace(".", "")
    tree.write(rel, mods, "Advice book `%s` (generated)" % book_name,
               "Generated by `scripts/spin_orbit/lock_zadv.py`. Do not edit.", body)
    return tree.module(rel)


SL_PARTS = ("rr", "ii", "ri", "ir")
