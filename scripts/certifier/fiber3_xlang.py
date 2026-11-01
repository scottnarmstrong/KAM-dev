#!/usr/bin/env python3
"""V2-3FREQ cross-language test: the Python mirror (fiber3.py) against the Lean kernel.

The mirror computes exact values (naturals, Options, Booleans) of the Lean definitions

  powUpK, mode3K, walk2 (mode3K ...)   KAM/CertificateSharp/V2/Fiber/Enum2.lean
  fiberSiteOk (both verdicts)          KAM/CertificateSharp/V2/Fiber/Site3.lean
  noIntRootIn, cubicDioOk (both)       KAM/CertificateSharp/Freq/CubicNorm.lean

on fixed inputs, and writes them as `decide +kernel` theorems into
KAM/CertificateSharp/V2/Tests/Fiber3XLang.lean.  Building that module is the test: the kernel
evaluates the Lean definitions and must agree with every value.  Boundary cases are exact (a claimed
bound equal to the mirror's bound passes, one 10^-40 below fails; a constant at the mirror's limit
passes, one 10^-9 above fails), so a one-unit drift of the mirror or of Lean breaks the build.

Usage:
  python3 -I scripts/certifier/fiber3_xlang.py           # rewrite the Lean module
  python3 -I scripts/certifier/fiber3_xlang.py --check   # exit 1 if the module on disk differs
"""
import importlib.util
import math
import pathlib
import sys
from fractions import Fraction as F

HERE = pathlib.Path(__file__).resolve().parent
ROOT = HERE.parents[1]
OUT = ROOT / "KAM/CertificateSharp/V2/Tests/Fiber3XLang.lean"

spec = importlib.util.spec_from_file_location("fiber3", HERE / "fiber3.py")
m = importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)


def q(x):
    x = F(x)
    return f"({x.numerator} / {x.denominator} : ℚ)" if x.denominator != 1 else f"({x.numerator} : ℚ)"


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


def fibwit_def(name, w, dname):
    B = F(w["B"])
    return (f"def {name} : FibWit where\n  N := {w['N']}\n  l := {w['l']}\n  J := {w['J']}\n  P := {w['P']}\n"
            f"  e := {w['e']}\n  D := {dname}\n  B := {B.numerator} /\n    {B.denominator}\n\n")


def plastic_box():
    """An enclosed clock: omega = (theta^-1, theta^-2, 1) * kappa with an uncertain kappa."""
    th = F(1324717957244746025960908854, 10 ** 27)          # plastic number, 27 digits
    kc, kr = F(7, 5), F(1, 10 ** 15)
    c0, c1 = kc / th, kc / th ** 2
    return [(c0, F(1, 10 ** 14)), (c1, F(1, 10 ** 14)), (kc, kr)]


def cases():
    """(definitions, [(tag, statement)])."""
    defs = ""
    out = []
    t3 = m.t3_box()
    w, c, s = m.produce_site(t3, F(1, 12), F(1, 4), 2)
    e, P, D = w["e"], w["P"], w["D"]
    defs += dbox_def("xD", D) + f"def xe : ℕ := {e}\n\n"
    for j in [0, 1, 2, 7, 63, 200]:
        out.append((f"pow_{j}", f"powUpK xe {P} 64 {j} = {m.powUp(e, P, 64, j)}"))
    for (a, b) in [(1, 0), (0, 1), (3, -2), (-5, 7), (2, 2)]:
        v = m.mode3(D, e, P, a, b)
        out.append((f"mode_{a}_{b}".replace("-", "m"), f"mode3K xD xe {P} {zl(a)} {zl(b)} = {opt(v)}"))
    qq, C0, C1, R0, R1 = D
    Dw = (qq, C0, C1, R0 + 2 ** (qq - 6), R1)
    defs += dbox_def("xDw", Dw)
    out.append(("mode_wide", f"mode3K xDw xe {P} 3 (-2) = {opt(m.mode3(Dw, e, P, 3, -2))}"))
    out.append(("walk_t3", f"walk2 (mode3K xD xe {P}) {w['N']} {w['l']} = {opt(s)}"))
    # sharding: the two halves of the row bisection, then the parent by `balFold_succ_of`
    N, l = w["N"], w["l"]
    M = lambda a, b: m.mode3(D, e, P, a, b)
    rows = [0 if 2 * N < i else sum(m.cell2(M, N, i, j) for j in range(2 ** l)) for i in range(2 ** l)]
    half = 2 ** (l - 1)
    lo, hi = sum(rows[:half]), sum(rows[half:])
    assert lo + hi == s
    f = f"(row2 (mode3K xD xe {P}) {N} {l})"
    out.append(("shard_lo", f"balFold {f} {l - 1} 0 = some {lo}"))
    out.append(("shard_hi", f"balFold {f} {l - 1} (0 + pow2 {l - 1}) = some {hi}"))
    out.append(("shard_walk", f"walk2 (mode3K xD xe {P}) {N} {l} = some ({lo} + {hi})",
                "balFold_succ_of xl_shard_lo xl_shard_hi"))
    # the enclosed clock: site verdicts at the exact bound
    pb = plastic_box()
    gam = F(1, 10)
    w2, c2, s2 = m.produce_site(pb, gam, F(1, 4), 2)
    bound = m.fibBound(pb, gam, F(1, 4), 2, w2, s2)
    wexact = dict(w2, B=bound)
    wlow = dict(w2, B=bound - F(1, 10 ** 40))
    kl = m.clockC(pb) - m.clockR(pb)
    cmin2 = F(2) ** 3 * bound / kl ** 2 * (gam * F(1, 4) ** 2) ** 2 / (2 * F(31415, 10000)) ** 2
    cc = F(math.isqrt(int(cmin2 * 10 ** 40)) + 1, 10 ** 20)          # smallest 20-digit c with the test
    assert m.fiberSiteOk(3, 2, pb, gam, F(1, 4), cc, wexact)
    assert not m.fiberSiteOk(3, 2, pb, gam, F(1, 4), cc, wlow)
    assert not m.fiberSiteOk(3, 2, pb, gam, F(1, 4), cc - F(1, 10 ** 20), wexact)
    defs += box_def("xBox", pb) + dbox_def("xD2", w2["D"]) + fibwit_def("xW", wexact, "xD2")
    defs += fibwit_def("xWlow", wlow, "xD2") + qdef("xc", cc) + qdef("xcLow", cc - F(1, 10 ** 20))
    out.append(("walk_clock", f"walk2 (mode3K xD2 {w2['e']} {w2['P']}) {w2['N']} {w2['l']} = {opt(s2)}"))
    out.append(("site_exact", "fiberSiteOk 3 2 xBox (1 / 10) (1 / 4) xc xW = true"))
    out.append(("site_low", "fiberSiteOk 3 2 xBox (1 / 10) (1 / 4) xc xWlow = false"))
    out.append(("site_c_low", "fiberSiteOk 3 2 xBox (1 / 10) (1 / 4) xcLow xW = false"))
    # cubic: the plastic number, omega = (1, theta, theta^2)
    th = F(1324717957244746025960908854, 10 ** 27)
    tr = F(1, 10 ** 26)
    A = [[1, 0, 0], [0, 1, 0], [0, 0, 1]]
    g, Wb = m.cubic_gamma(-1, -1, 0, th, tr, A, 1)
    g_ok = F(math.floor(g * 10 ** 9), 10 ** 9)
    g_bad = g_ok + F(1, 10 ** 9)
    assert m.cubicDioOk(-1, -1, 0, th, tr, A, 1, g_ok) and not m.cubicDioOk(-1, -1, 0, th, tr, A, 1, g_bad)
    defs += qdef("xθ", th) + qdef("xθr", tr) + "def xI : Fin 3 → Fin 3 → ℤ := ![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]\n\n"
    out.append(("cubic_ok", f"cubicDioOk (-1) (-1) 0 xθ xθr xI 1 {q(g_ok)} = true"))
    out.append(("cubic_bad", f"cubicDioOk (-1) (-1) 0 xθ xθr xI 1 {q(g_bad)} = false"))
    for (p0, p1, p2) in [(-2, 0, 0), (-1, -1, 0), (-8, 0, 0), (6, -5, -2)]:
        v = (p0 != 0 and all(m.cubic_eval(p0, p1, p2, z) != 0 for z in range(-abs(p0), abs(p0) + 1)))
        out.append((f"noroot_{abs(p0)}_{abs(p1)}_{abs(p2)}",
                    f"noIntRootIn {zl(p0)} {zl(p1)} {zl(p2)} = {'true' if v else 'false'}"))
    return defs, out, float(g)


HEADER = '''/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.Fiber.Shard
public import KAM.CertificateSharp.Freq.CubicNorm

/-!
# Cross-language test of the three-frequency site (generated)

Written by `scripts/certifier/fiber3_xlang.py` from the Python mirror `scripts/certifier/fiber3.py`;
do not edit by hand. Each theorem is a value the mirror computed (`powUpK`, `mode3K`, the walk,
`fiberSiteOk` at an enclosed clock on both sides of the exact bound, `noIntRootIn`, `cubicDioOk` on
both sides of the plastic number's constant `γ = 1/W̄ ≈ {gamma:.6f}`), decided by the kernel.
-/

@[expose] public section

namespace KAM.CertificateSharp.V2.XLang3

open KAM.Certificate KAM.CertificateSharp KAM.CertificateSharp.V2 KAM.CertificateSharp.Fiber
  KAM.CertificateSharp.Cubic

'''


def render():
    defs, cs, g = cases()
    body = "".join(f"theorem xl_{c[0]} :\n    {c[1]} :=\n  {c[2]}\n\n" if len(c) == 3 else
                   f"theorem xl_{c[0]} :\n    {c[1]} := by\n  decide +kernel\n\n" for c in cs)
    text = HEADER.replace("{gamma:.6f}", f"{g:.6f}") + defs + body
    text += "end KAM.CertificateSharp.V2.XLang3\n\nend\n"
    assert max(len(line) for line in text.splitlines()) <= 100, "a line exceeds 100 characters"
    return text


def main(argv):
    text = render()
    if "--check" in argv:
        cur = OUT.read_text() if OUT.exists() else ""
        if cur != text:
            print("fiber3_xlang: the Lean module differs from the mirror's values")
            return 1
        print("fiber3_xlang: the Lean module matches the mirror")
        return 0
    OUT.write_text(text)
    print("wrote", OUT.relative_to(ROOT))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
