#!/usr/bin/env python3
"""LOCK-GEN part 2: the body of `lockHamExpr Ω cs` (design §3) as a HamExpr tree, in one place.  Form "design" is
the LANDED tree (KAM/SpinOrbit/Lock/Coords/HamExpr.lean, inp 7e8f8c02; node order in LOCK-COORDS-C-handoff.md),
and its lock_jet program is the landed `slpCompile` program op for op (3116 ops; `lock_jet.py check-lit`).

    K = J̃ + Y²/2 − c′²/2 + X c″ + V(φ + c + X, φ) − 1/2,   X = √(I/(πΩ)) sin 2πα,   Y = √(IΩ/π) cos 2πα,
    V(φ + c + X, φ) = −Σ_m εA_m cos(2π(2(c + X) + (2 − m)φ))
                    = −cos A · Σ_m εA_m cos 2π(2−m)φ + sin A · Σ_m εA_m sin 2π(2−m)φ,   A = 4π(c + X)

(angles enter a `HamExpr` only through modes, so the φ-phase is split off by the addition formula; the two trig
nodes `cos A`, `sin A` compile to four `exp` slots).  Trees are tuples in the shape of `adv_jet.compile_`:
("const", q) | ("pi",) | ("action", j) | ("cosMode", k) | ("sinMode", k) | ("add", a, b) | ("mul", a, b) |
("div", a, b) | ("pow", a, m) | ("exp", a) | ("sin", a) | ("cos", a) | ("sqrt", a).

Forms (owner review, see LOCK-GEN-NUMERICS.md Part 2):
  "design"  the design §3 text: two square roots, √(I/(πΩ)) for X and its Ω-twin √(IΩ/π) for Y, so that
            `lockHamExpr_eval` is purely algebraic (holds for every z);
  "lean"    Y²/2 written as (Ω/(2π)) I cos²2πα (no second root): fewer witnesses and a smaller Ham claim, but
            `lockHamExpr_eval` then holds only where sqrtE(IΩ/π)² = IΩ/π (off the nonpositive real I axis), which
            is all the consumers use (Re I > 0 on the certified domain).
`sqrt_node(arg)` is the ONLY place that builds a square root (the sqrt witnesses are keyed by the slot number of
their `sqrt` operation).  The certificate's `ham` is `lock_ham_scaled`, the time-scaled tree that the landed
`lockBarrier_of_exact_torus` (Lock/Graph.lean) consumes for every κ, κ = 1 included.  Untrusted tooling.
"""
from fractions import Fraction as F
from model import A_EXACT, EPS

ALPHA_KEY = (1, 0)


def two_pi(k=1):
    """2πk as an expression."""
    return ("mul", ("const", F(2 * k)), ("pi",))


def sqrt_node(arg):
    """The square root of an expression (the one encoding of `HamExpr.sqrt`)."""
    return ("sqrt", arg)


def add_all(terms):
    out = terms[-1]
    for t in reversed(terms[:-1]):
        out = ("add", t, out)
    return out


def x_expr(Om):
    """X = √(I/(πΩ)) sin 2πα, with the radicand of design §3: (1/Ω · I)/π."""
    return ("mul", sqrt_node(("div", ("mul", ("const", 1 / F(Om)), ("action", 0)), ("pi",))), ("sinMode", ALPHA_KEY))


def y_expr(Om):
    """Y = √(IΩ/π) cos 2πα (radicand (Ω · I)/π)."""
    return ("mul", sqrt_node(("div", ("mul", ("const", F(Om)), ("action", 0)), ("pi",))), ("cosMode", ALPHA_KEY))


def centre_exprs(cs):
    """c, c′, c″ of the sine centre c(φ) = Σ cs_j sin 2π(j+1)φ (written as mode sums with 2π factors)."""
    c = add_all([("mul", ("const", F(q)), ("sinMode", (0, j + 1))) for j, q in enumerate(cs)])
    cp = add_all([("mul", ("mul", ("const", F(q)), two_pi(j + 1)), ("cosMode", (0, j + 1))) for j, q in enumerate(cs)])
    cpp = add_all([("mul", ("mul", ("const", -F(q)), ("pow", two_pi(j + 1), 2)), ("sinMode", (0, j + 1)))
                   for j, q in enumerate(cs)])
    return c, cp, cpp


def forcing_sums():
    """Σ_m εA_m cos 2π(2−m)φ and Σ_m εA_m sin 2π(2−m)φ (m = 1..7; the (0, 0) mode is the constant εA_2)."""
    ea = {m: EPS * A_EXACT[m] for m in A_EXACT}
    cos_t, sin_t = [], []
    for m in sorted(ea):
        k = 2 - m
        if k == 0:
            cos_t.append(("const", ea[m]))
        else:
            cos_t.append(("mul", ("const", ea[m]), ("cosMode", (0, k))))
            sin_t.append(("mul", ("const", ea[m]), ("sinMode", (0, k))))
    return add_all(cos_t), add_all(sin_t)


def lock_ham_expr(Om, cs, form="design"):
    """The proposed `lockHamExpr Ω cs` (unscaled)."""
    c, cp, cpp = centre_exprs(cs)
    X = x_expr(Om)
    A = ("mul", two_pi(2), ("add", c, X))
    Cs, Ss = forcing_sums()
    V = ("add", ("mul", ("const", F(-1)), ("mul", ("cos", A), Cs)), ("mul", ("sin", A), Ss))
    if form == "design":
        half_y2 = ("mul", ("const", F(1, 2)), ("pow", y_expr(Om), 2))
    elif form == "lean":
        half_y2 = ("mul", ("div", ("mul", ("const", F(Om) / 2), ("action", 0)), ("pi",)),
                   ("pow", ("cosMode", ALPHA_KEY), 2))
    else:
        raise ValueError(form)
    return add_all([("action", 1), half_y2, ("mul", ("const", F(-1, 2)), ("pow", cp, 2)), ("mul", X, cpp), V,
                    ("const", F(-1, 2))])


def lock_ham_scaled(kappa, Om, cs, form="design"):
    """`.mul (.const κ) (lockHamExpr Ω cs)`: the certificate's `ham` (Lock/Graph.lean `lockBarrier_of_exact_torus`).
    Its program is the landed tree's, shifted one slot by the κ constant (slot 1), plus one product per nonzero jet
    entry of the tree (41 at N = 65): 3116 + 42 = 3158 ops."""
    return ("mul", ("const", F(kappa)), lock_ham_expr(Om, cs, form))


def to_lean(e):
    """The tree as Lean `HamExpr` syntax (for the sample output and for LOCK-COORDS-C to compare against)."""
    t = e[0]
    q = lambda x: "(%s)" % x if F(x).denominator == 1 else "(%d / %d)" % (F(x).numerator, F(x).denominator)
    key = lambda k: "[%s]" % ", ".join(str(x) for x in k)
    if t == "const":
        return "(.const %s)" % q(e[1])
    if t == "pi":
        return ".pi"
    if t == "action":
        return "(.action %d)" % e[1]
    if t in ("cosMode", "sinMode"):
        return "(.%s %s)" % (t, key(e[1]))
    if t in ("add", "mul", "div"):
        return "(.%s %s %s)" % (t, to_lean(e[1]), to_lean(e[2]))
    if t == "pow":
        return "(.pow %s %d)" % (to_lean(e[1]), e[2])
    return "(.%s %s)" % (t, to_lean(e[1]))


def eval_tree(e, z):
    """Numerical value (numpy complex arrays) at z = (alpha, phi, I, Jt): cross-check against lock_v2.lock_ham_jet."""
    import numpy as np
    t = e[0]
    if t == "const":
        return complex(F(e[1]))
    if t == "pi":
        return np.pi
    if t == "action":
        return z[2 + e[1]]
    if t in ("cosMode", "sinMode"):
        ph = 2 * np.pi * (e[1][0] * z[0] + e[1][1] * z[1])
        return np.cos(ph) if t == "cosMode" else np.sin(ph)
    if t in ("add", "mul", "div"):
        a, b = eval_tree(e[1], z), eval_tree(e[2], z)
        return a + b if t == "add" else a * b if t == "mul" else a / b
    if t == "pow":
        return eval_tree(e[1], z) ** e[2]
    a = eval_tree(e[1], z)
    return {"exp": np.exp, "sin": np.sin, "cos": np.cos, "sqrt": np.sqrt}[t](a)
