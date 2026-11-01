#!/usr/bin/env python3
"""V2-BULK-RUNS cross-language test: the Python mirror (fiber3_bulk2.py) against the Lean kernel.

The mirror computes exact values (naturals, Options, Booleans) of the Lean definitions

  powDownK, gsumK, tentK, apK, crossCut, hnode, rowB2, walkB2   Fiber/BulkRuns.lean, Fiber/Bulk2.lean
  bulk2SiteOk (both verdicts)                                     Fiber/Bulk2Site.lean

on fixed inputs (runs that the mirror's walk accepted and rejected on the toy box of
Tests/BulkToy.lean, the toy walk, and rows of the SJS-plan frequencies at P = 128), and writes them
as `decide +kernel` theorems into KAM/CertificateSharp/V2/Tests/Bulk2XLang.lean.  Building that module
is the test.  The site verdicts are exact (a claimed bound equal to the mirror's bound passes, one
10^-40 below fails; a constant at the mirror's limit passes, one 10^-20 below fails).

Usage:
  python3 -I scripts/certifier/fiber3_bulk2_xlang.py           # rewrite the Lean module
  python3 -I scripts/certifier/fiber3_bulk2_xlang.py --check   # exit 1 if the module on disk differs
"""
import math
import pathlib
import sys
from fractions import Fraction as F

HERE = pathlib.Path(__file__).resolve().parent
ROOT = HERE.parents[1]
OUT = ROOT / "KAM/CertificateSharp/V2/Tests/Bulk2XLang.lean"
sys.path.insert(0, str(HERE))
import fiber3 as f3  # noqa: E402
import fiber3_bulk as fb  # noqa: E402
import fiber3_bulk2 as b2  # noqa: E402
import fiber3_bulk_xlang as x1  # noqa: E402

zl, opt, dbox_def, qdef, box_def = x1.zl, x1.opt, x1.dbox_def, x1.qdef, x1.box_def


def wrap(stmt, suffix=" := by"):
    """Break a statement at ` = ` and then at spaces, so that every line (with the suffix) is <= 100."""
    if len("    " + stmt + suffix) <= 100:
        return "    " + stmt
    lhs, rhs = stmt.rsplit(" = ", 1)
    lines, cur = [], "    "
    for tok in lhs.split(" "):
        if len(cur) + len(tok) + 1 > 100 and cur.strip():
            lines.append(cur.rstrip())
            cur = "      "
        cur += tok + " "
    lines.append(cur.rstrip())
    if len(lines[-1]) + 3 + len(rhs) + len(suffix) <= 100:
        lines[-1] += " = " + rhs
    else:
        lines.append("      = " + rhs)
    return "\n".join(lines)


def bulk2wit_def(name, w, dname):
    B = F(w["B"])
    return (f"def {name} : Bulk2Wit where\n  N := {w['N']}\n  l := {w['l']}\n  J := {w['J']}\n  P := {w['P']}\n"
            f"  e := {w['e']}\n  D := {dname}\n  B := {B.numerator} /\n    {B.denominator}\n"
            f"  rn := {w['rn']}\n  rd := {w['rd']}\n  tol := {w['tol']}\n  s := {w['s']}\n  fuel := {w['fuel']}\n\n")


def record_calls(w):
    """Run the toy walk with the run checks wrapped; return the recorded (args, value) per kind."""
    rec = {"tent": [], "ap": [], "cut": []}
    o_tent, o_ap, o_cut = b2.tentK, b2.apK, b2.crossCut

    def tent(*args, **kw):
        v = o_tent(*args[:10])
        rec["tent"].append((args[:10], v))
        return v

    def ap(*args, **kw):
        v = o_ap(*args[:13])
        rec["ap"].append((args[:13], v))
        return v

    def cut(*args, **kw):
        v = o_cut(*args)
        rec["cut"].append((args, v))
        return v
    b2.tentK, b2.apK, b2.crossCut = tent, ap, cut
    try:
        b2.bulk2Walk(w)
    finally:
        b2.tentK, b2.apK, b2.crossCut = o_tent, o_ap, o_cut
    return rec


def cases():
    defs, out = "", []
    box, tc, tr = fb.toy_box()
    gam, b = F(77, 250000), F(1, 32)
    w, c, s, st = b2.produce_bulk2_site(box, gam, b, 2)
    e, P, D = w["e"], w["P"], w["D"]
    defs += dbox_def("xD", D) + f"def xe : ℕ := {e}\n\n"
    for n in [0, 1, 2, 7, 64, 1000]:
        out.append((f"pdown_{n}", f"powDownK xe {P} 64 {n} = {b2.powDown(e, P, 64, n)}"))
        out.append((f"gsum_{n}", f"gsumK xe {P} {n} = {b2.gsumK(e, P, n)}"))
    rec = record_calls(w)
    acc = f"(accOk {w['rn']} {w['rd']} {w['tol']})"
    # tent runs: one accepted, one rejected
    for tag, want in (("acc", True), ("rej", False)):
        hit = next(((a_, v) for a_, v in rec["tent"] if (v is not None) == want), None)
        if hit is None:
            continue
        (D_, e_, P_, g, _, a, sg, lo, i0, i1), v = hit
        out.append((f"tent_{tag}", f"tentK xD xe {P} {g} {acc} {zl(a)} {zl(sg)} {lo} {i0} {i1} = {opt(v)}"))
    # crossing runs: receding and approaching, accepted; and one rejected
    def slope(args):
        D_, e_, P_, g, s0, rn, rd, tol, a, sg, lo, i0, i1 = args
        p = f3.nearP(D_[0], fb.colX(D_, a, sg, lo, i0))
        return b2.sgnZ(fb.colZ(D_, a, sg, p, lo, i0)) * sg * D_[2] - D_[4]
    picks = {}
    for args, v in rec["ap"]:
        if v is not None:
            picks.setdefault("rec" if slope(args) >= 0 else "app", (args, v))
        else:
            picks.setdefault("rej", (args, v))
    for tag, (args, v) in sorted(picks.items()):
        D_, e_, P_, g, s0, rn, rd, tol, a, sg, lo, i0, i1 = args
        out.append((f"ap_{tag}", f"apK xD xe {P} {g} {s0} {rn} {rd} {tol} {zl(a)} {zl(sg)} {lo} {i0} {i1} = "
                    f"{opt(v)}"))
    hit = next(((a_, v) for a_, v in rec["cut"] if v is not None), None)
    if hit is not None:
        (D_, a, sg, lo, s0, i0, i1), v = hit
        out.append(("cut", f"crossCut xD {s0} {zl(a)} {zl(sg)} {lo} {i0} {i1} = some ({v[0]}, {v[1]}, {v[2]})"))
    par = f"{w['rn']} {w['rd']} {w['tol']} {w['s']}"
    for a in [0, 4, -23, 27, 65, 66]:
        out.append((f"row_{'m' if a < 0 else ''}{abs(a)}",
                    f"rowB2 xD xe {P} {par} {w['fuel']} {w['N']} {zl(a)} = "
                    f"{opt(b2.rowB2(D, e, P, w, w['N'], w['l'], a))}"))
    out.append(("walk_toy", f"walkB2 xD xe {P} {par} {w['fuel']} {w['N']} {w['l']} = {opt(s)}"))
    bound = f3.fibBound(box, gam, b, 2, w, s)
    wexact, wlow = dict(w, B=bound), dict(w, B=bound - F(1, 10 ** 40))
    kl = f3.clockC(box) - f3.clockR(box)
    cmin2 = F(2) ** 3 * bound / kl ** 2 * (gam * b ** 2) ** 2 / (2 * F(31415, 10000)) ** 2
    cc = F(math.isqrt(int(cmin2 * 10 ** 40)) + 1, 10 ** 20)
    assert b2.bulk2SiteOk(3, 2, box, gam, b, cc, wexact)
    assert not b2.bulk2SiteOk(3, 2, box, gam, b, cc, wlow)
    assert not b2.bulk2SiteOk(3, 2, box, gam, b, cc - F(1, 10 ** 20), wexact)
    defs += box_def("xBox", box) + bulk2wit_def("xW", wexact, "xD") + bulk2wit_def("xWlow", wlow, "xD")
    defs += qdef("xc", cc) + qdef("xcLow", cc - F(1, 10 ** 20))
    out.append(("site_exact", "bulk2SiteOk 3 2 xBox (77 / 250000) (1 / 32) xc xW = true"))
    out.append(("site_low", "bulk2SiteOk 3 2 xBox (77 / 250000) (1 / 32) xc xWlow = false"))
    out.append(("site_c_low", "bulk2SiteOk 3 2 xBox (77 / 250000) (1 / 32) xcLow xW = false"))
    # SJS rows (q = 64, P = 128): a crossing row, a half-integer row, a quiet row
    sbox, W = fb.sjs_box()
    twopi = F(314159265358979323846264338327950288419716939937510, 5 * 10 ** 49)
    sb = F("2.649929802480e-03")
    Sp = 2784427957164.413 * float(f3.clockC(sbox)) ** 2
    w2, c2, s2, st2 = b2.produce_bulk2_site(sbox, F(28, 10 ** 8) / twopi, sb, 2, S_est=Sp, P=128)
    defs += dbox_def("sD", w2["D"]) + f"def se : ℕ := {w2['e']}\n\n"
    par2 = f"{w2['rn']} {w2['rd']} {w2['tol']} {w2['s']}"
    for a in [5, -400, 900]:
        v = b2.rowB2(w2["D"], w2["e"], 128, w2, w2["N"], w2["l"], a)
        out.append((f"sjs_row_{'m' if a < 0 else ''}{abs(a)}",
                    f"rowB2 sD se 128 {par2} {w2['fuel']} {w2['N']} {zl(a)} = {opt(v)}"))
    return defs, out


HEADER = '''/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.Fiber.Bulk2Site

/-!
# Cross-language test of the extended bulk walk (generated)

Written by `scripts/certifier/fiber3_bulk2_xlang.py` from the Python mirror
`scripts/certifier/fiber3_bulk2.py`; do not edit by hand. Each theorem is a value the mirror
computed, decided by the kernel: `powDownK`, `gsumK`, tent and crossing runs that the mirror's walk
accepted and rejected (receding and approaching), a crossing cut, `rowB2` and `walkB2` on the toy
box of `Tests/BulkToy.lean`, `bulk2SiteOk` on both sides of the exact bound and constant, and three
rows of the SJS-plan frequencies at `P = 128`.
-/

@[expose] public section

namespace KAM.CertificateSharp.V2.XLangBulk2

open KAM.Certificate KAM.CertificateSharp KAM.CertificateSharp.V2 KAM.CertificateSharp.Fiber

'''


def render():
    defs, cs = cases()
    body = "".join(f"theorem xl_{c[0]} :\n{wrap(c[1])} := by\n  decide +kernel\n\n" for c in cs)
    text = HEADER + defs + body + "end KAM.CertificateSharp.V2.XLangBulk2\n\nend\n"
    long = [line for line in text.splitlines() if len(line) > 100]
    assert not long, long[:3]
    return text


def main(argv):
    text = render()
    if "--check" in argv:
        cur = OUT.read_text() if OUT.exists() else ""
        if cur != text:
            print("fiber3_bulk2_xlang: the Lean module differs from the mirror's values")
            return 1
        print("fiber3_bulk2_xlang: the Lean module matches the mirror")
        return 0
    OUT.write_text(text)
    print("wrote", OUT.relative_to(ROOT))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
