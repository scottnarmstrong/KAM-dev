#!/usr/bin/env python3
"""V2-BULK cross-language test: the Python mirror (fiber3_bulk.py) against the Lean kernel.

The mirror computes exact values (naturals, Options, Booleans) of the Lean definitions

  gTabOk0, blkValK, blkK, hrow, rowB, walkB    KAM/CertificateSharp/V2/Fiber/Bulk.lean
  bulkSiteOk (both verdicts)                   KAM/CertificateSharp/V2/Fiber/BulkSite.lean

on fixed inputs (the toy box of Tests/BulkToy.lean and the SJS-plan frequencies), and writes them
as `decide +kernel` theorems into KAM/CertificateSharp/V2/Tests/BulkXLang.lean.  Building that module
is the test: the kernel evaluates the Lean definitions and must agree with every value.  The site
verdicts are exact (a claimed bound equal to the mirror's bound passes, one 10^-40 below fails; a
constant at the mirror's limit passes, one 10^-20 below fails), and a single fibre of `blkK` equals
`mode3K` (the landed walk's term), so a one-unit drift of either side breaks the build.

Usage:
  python3 -I scripts/certifier/fiber3_bulk_xlang.py           # rewrite the Lean module
  python3 -I scripts/certifier/fiber3_bulk_xlang.py --check   # exit 1 if the module on disk differs
"""
import math
import pathlib
import sys
from fractions import Fraction as F

HERE = pathlib.Path(__file__).resolve().parent
ROOT = HERE.parents[1]
OUT = ROOT / "KAM/CertificateSharp/V2/Tests/BulkXLang.lean"
sys.path.insert(0, str(HERE))
import fiber3 as f3  # noqa: E402
import fiber3_bulk as fb  # noqa: E402


def zl(x):
    return f"({x})" if x < 0 else f"{x}"


def opt(v):
    return "none" if v is None else f"some {v}"


def dbox_def(name, D):
    qq, C0, C1, R0, R1 = D
    return (f"def {name} : DBox2 where\n  q := {qq}\n  C0 := {zl(C0)}\n  C1 := {zl(C1)}\n"
            f"  R0 := {R0}\n  R1 := {R1}\n\n")


def qdef(name, x):
    x = F(x)
    return f"def {name} : ℚ :=\n  {x.numerator} /\n    {x.denominator}\n\n"


def box_def(name, box):
    lines = [f"def {name} : FreqBox :=\n  ["]
    for i, (c, r) in enumerate(box):
        sep = "," if i + 1 < len(box) else "]"
        lines.append(f"    ({c.numerator} /\n        {c.denominator},\n      {r.numerator} / {r.denominator}){sep}")
    return "\n".join(lines) + "\n\n"


def list_def(name, xs):
    body = ",\n    ".join(str(x) for x in xs)
    return f"def {name} : List ℕ :=\n  [{body}]\n\n"


def bulkwit_def(name, w, dname, gname):
    B = F(w["B"])
    return (f"def {name} : BulkWit where\n  N := {w['N']}\n  l := {w['l']}\n  J := {w['J']}\n  P := {w['P']}\n"
            f"  e := {w['e']}\n  D := {dname}\n  B := {B.numerator} /\n    {B.denominator}\n  gs := {gname}\n"
            f"  rn := {w['rn']}\n  rd := {w['rd']}\n  tol := {w['tol']}\n\n")


def first_run(w, accepted=True):
    """A run of the toy walk that the mirror accepted (length >= 2), or a node it rejected."""
    D, e, P, G = w["D"], w["e"], w["P"], fb.getG(w)
    found = []

    def probe(a, sg, lo, M):
        for t in range(w["l"], 0, -1):
            for i0 in range(0, M - lo + 1, 2 ** t):
                i1 = min(i0 + 2 ** t - 1, M - lo)
                if i1 == i0:
                    continue
                v = fb.blkK(D, e, P, G(t), fb.accOk(w["rn"], w["rd"], w["tol"]), a, sg, lo, i0, i1)
                if (v is not None) == accepted:
                    return (a, sg, lo, i0, i1, t, v)
        return None
    for a in range(1, w["N"]):
        r = probe(a, 1, 0, w["N"] - a)
        if r:
            return r
    raise ValueError("no run")


def cases():
    defs, out = "", []
    box, tc, tr = fb.toy_box()
    gam, b = F(77, 250000), F(1, 32)
    w, c, s, st = fb.produce_bulk_site(box, gam, b, 2)
    e, P, D, gs = w["e"], w["P"], w["D"], w["gs"]
    defs += dbox_def("xD", D) + f"def xe : ℕ := {e}\n\n" + list_def("xgs", gs)
    bad = gs[:-1] + [gs[-1] - 1]
    assert fb.gTabOk0(e, P, gs) and not fb.gTabOk0(e, P, bad)
    defs += list_def("xgsBad", bad)
    out.append(("gtab_ok", f"gTabOk0 xe {P} xgs = true"))
    out.append(("gtab_bad", f"gTabOk0 xe {P} xgsBad = false"))
    for (j0, t, lam, p) in [(1, 0, 3 * 10 ** 15, 0), (7, 3, 5 * 10 ** 16, -2), (40, 6, 10 ** 12, 11)]:
        out.append((f"val_{j0}_{t}", f"blkValK xD xe {P} {j0} {gs[t]} {lam} {zl(p)} = "
                    f"{fb.blkValK(D, e, P, j0, gs[t], lam, p)}"))
    # single fibres: blkK = mode3K
    for (a, sg, lo, i) in [(3, 1, 0, 5), (-4, -1, 1, 2), (0, 1, 1, 0), (17, -1, 1, 30)]:
        v = fb.blkK(D, e, P, gs[0], fb.acc_true, a, sg, lo, i, i)
        assert v == f3.mode3(D, e, P, a, sg * (lo + i))
        tag = f"{abs(a)}_{'p' if sg > 0 else 'm'}_{i}"
        out.append((f"fibre_{tag}", f"blkK xD xe {P} (pow2 {P}) (fun _ _ _ => true) {zl(a)} {zl(sg)} {lo} {i} {i} = "
                    f"{opt(v)}"))
        out.append((f"mode_{tag}", f"mode3K xD xe {P} {zl(a)} {zl(sg * (lo + i))} = {opt(v)}"))
    a, sg, lo, i0, i1, t, v = first_run(w, True)
    out.append(("run_acc", f"blkK xD xe {P} {gs[t]} (accOk {w['rn']} {w['rd']} {w['tol']}) {zl(a)} {zl(sg)} {lo} "
                f"{i0} {i1} = {opt(v)}"))
    a, sg, lo, i0, i1, t, v = first_run(w, False)
    out.append(("run_rej", f"blkK xD xe {P} {gs[t]} (accOk {w['rn']} {w['rd']} {w['tol']}) {zl(a)} {zl(sg)} {lo} "
                f"{i0} {i1} = {opt(v)}"))
    G = fb.getG(w)
    acc = f"{w['rn']} {w['rd']} {w['tol']}"
    for a in [0, 4, -23, 65, 66]:
        out.append((f"row_{'m' if a < 0 else ''}{abs(a)}",
                    f"rowB xD xe {P} (fun t => xgs.getD t 0) {acc} {w['N']} {w['l']} {zl(a)} = "
                    f"{opt(fb.rowB(D, e, P, G, w['rn'], w['rd'], w['tol'], w['N'], w['l'], a))}"))
    hv = fb.hrow(D, e, P, G, w["rn"], w["rd"], w["tol"], 4, -1, 1, w["N"] - 4, w["l"], 0)
    out.append(("hrow_4m", f"hrow xD xe {P} (fun t => xgs.getD t 0) {acc} 4 (-1) 1 {w['N'] - 4} {w['l']} 0 = "
                f"{opt(hv)}"))
    out.append(("walk_toy", f"walkB xD xe {P} (fun t => xgs.getD t 0) {acc} {w['N']} {w['l']} = {opt(s)}"))
    # the site, on both sides of the exact bound and of the exact constant
    bound = f3.fibBound(box, gam, b, 2, w, s)
    wexact, wlow = dict(w, B=bound), dict(w, B=bound - F(1, 10 ** 40))
    kl = f3.clockC(box) - f3.clockR(box)
    cmin2 = F(2) ** 3 * bound / kl ** 2 * (gam * b ** 2) ** 2 / (2 * F(31415, 10000)) ** 2
    cc = F(math.isqrt(int(cmin2 * 10 ** 40)) + 1, 10 ** 20)
    assert fb.bulkSiteOk(3, 2, box, gam, b, cc, wexact)
    assert not fb.bulkSiteOk(3, 2, box, gam, b, cc, wlow)
    assert not fb.bulkSiteOk(3, 2, box, gam, b, cc - F(1, 10 ** 20), wexact)
    defs += box_def("xBox", box) + bulkwit_def("xW", wexact, "xD", "xgs") + bulkwit_def("xWlow", wlow, "xD", "xgs")
    defs += qdef("xc", cc) + qdef("xcLow", cc - F(1, 10 ** 20))
    out.append(("site_exact", "bulkSiteOk 3 2 xBox (77 / 250000) (1 / 32) xc xW = true"))
    out.append(("site_low", "bulkSiteOk 3 2 xBox (77 / 250000) (1 / 32) xc xWlow = false"))
    out.append(("site_c_low", "bulkSiteOk 3 2 xBox (77 / 250000) (1 / 32) xcLow xW = false"))
    # SJS rows (q = 64, P = 128)
    sbox, W = fb.sjs_box()
    twopi = F(314159265358979323846264338327950288419716939937510, 5 * 10 ** 49)
    sb = F("2.649929802480e-03")
    Sp = 2784427957164.413 * float(f3.clockC(sbox)) ** 2
    w2, c2, s2, st2 = fb.produce_bulk_site(sbox, F(28, 10 ** 8) / twopi, sb, 2, S_est=Sp, P=128)
    defs += dbox_def("sD", w2["D"]) + f"def se : ℕ := {w2['e']}\n\n" + list_def("sgs", w2["gs"])
    G2 = fb.getG(w2)
    acc2 = f"{w2['rn']} {w2['rd']} {w2['tol']}"
    for a in [5, -400, 900]:
        v = fb.rowB(w2["D"], w2["e"], 128, G2, w2["rn"], w2["rd"], w2["tol"], w2["N"], w2["l"], a)
        out.append((f"sjs_row_{'m' if a < 0 else ''}{abs(a)}",
                    f"rowB sD se 128 (fun t => sgs.getD t 0) {acc2} {w2['N']} {w2['l']} {zl(a)} = {opt(v)}"))
    return defs, out


HEADER = '''/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.Fiber.BulkSite

/-!
# Cross-language test of the bulk walk (generated)

Written by `scripts/certifier/fiber3_bulk_xlang.py` from the Python mirror
`scripts/certifier/fiber3_bulk.py`; do not edit by hand. Each theorem is a value the mirror
computed, decided by the kernel: `gTabOk0`, `blkValK`, `blkK` on single fibres (where it equals
`mode3K`) and on runs, `hrow`, `rowB` and `walkB` on the toy box of `Tests/BulkToy.lean`,
`bulkSiteOk` on both sides of the exact bound and constant, and three rows of the SJS-plan
frequencies at `P = 128`.
-/

@[expose] public section

namespace KAM.CertificateSharp.V2.XLangBulk

open KAM.Certificate KAM.CertificateSharp KAM.CertificateSharp.V2 KAM.CertificateSharp.Fiber

'''


def wrap(stmt):
    """Break a long statement at ` = ` and then at spaces (lines <= 100)."""
    first = "    " + stmt
    if len(first) <= 100:
        return first
    lhs, rhs = stmt.rsplit(" = ", 1)
    lines, cur = [], "    "
    for tok in lhs.split(" "):
        if len(cur) + len(tok) + 1 > 100 and cur.strip():
            lines.append(cur.rstrip())
            cur = "      "
        cur += tok + " "
    lines.append(cur.rstrip())
    tail = "      = " + rhs
    if len(lines[-1]) + 3 + len(rhs) <= 100:
        lines[-1] += " = " + rhs
    else:
        lines.append(tail)
    return "\n".join(lines)


def render():
    defs, cs = cases()
    body = "".join(f"theorem xl_{c[0]} :\n{wrap(c[1])} := by\n  decide +kernel\n\n" for c in cs)
    text = HEADER + defs + body + "end KAM.CertificateSharp.V2.XLangBulk\n\nend\n"
    long = [line for line in text.splitlines() if len(line) > 100]
    assert not long, long[:3]
    return text


def main(argv):
    text = render()
    if "--check" in argv:
        cur = OUT.read_text() if OUT.exists() else ""
        if cur != text:
            print("fiber3_bulk_xlang: the Lean module differs from the mirror's values")
            return 1
        print("fiber3_bulk_xlang: the Lean module matches the mirror")
        return 0
    OUT.write_text(text)
    print("wrote", OUT.relative_to(ROOT))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
