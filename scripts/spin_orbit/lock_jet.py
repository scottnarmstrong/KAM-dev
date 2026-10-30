#!/usr/bin/env python3
"""LOCK-GEN part 2: Python mirror of the jet compiler for the constructors `adv_jet.py` does not cover.

`adv_jet.py` mirrors const, action, cosMode, sinMode, add, mul, pow.  This module adds, operation by operation,
the remaining nodes of `KAM/Certificate/Expr/{DiffNode,Diff}.lean` (inp a5f010eb) and of `DiffNodeSqrt.lean`
(branch inp-locksqrt a12b69cb, read-only):
  pi                       slpConstNode s (1/2) 0 1
  slpExpNode / slpExpD3    exp
  slpExpScaleNode          exp (c A)
  slpTrigNode              sin, cos of an expression: exp(i A), exp(-i A), combined
  slpInvPre / slpInvTail / slpInvD3, slpDivNode
  slpSqrtPre / slpSqrtTail / slpSqrtD3 (the sqrt node: V = sqrt x, w = V^-1, w^2, w^3 = w w^2, w^5 = w^2 w^3)
and `compile_`, `jet` over the full constructor set.  Ops are tuples ("const", re, im, deg) | ("action", j) |
("char", k) | ("add", a, b) | ("mul", a, b) | ("exp", a) | ("inv", a) | ("sqrt", a).  Untrusted tooling.
"""
from fractions import Fraction as F
import adv_jet as AJ
from adv_jet import (emit, mulO, pure, cadd, cmul, cscale, finish, const_node, action_node, add_node,  # noqa: F401
                     mul_node, scale_node, combine, pow_node, trig_char, Node)


def cross(A, i, j, k):
    P = pure
    return cadd(cadd(cmul(P(A.g2(i, j)), P(A.g1(k))), cmul(P(A.g1(j)), P(A.g2(i, k)))),
                cmul(P(A.g1(i)), P(A.g2(j, k))))


def g3(A, i, j, k):
    return A.d3[i][j][k] if A.d3 else None


def exp_node(n, s, A):
    E = len(s)
    P = pure
    c1 = lambda i: cmul(P(E), P(A.g1(i)))
    c2 = lambda i, j: cadd(cmul(P(E), cmul(P(A.g1(i)), P(A.g1(j)))), cmul(P(E), P(A.g2(i, j))))
    c3 = lambda i, j, k: cmul(P(E), cadd(cmul(P(A.g1(i)), cmul(P(A.g1(j)), P(A.g1(k)))),
                                         cadd(cross(A, i, j, k), P(A.g3(i, j, k)))))
    return finish(n, E, c1, c2, c3, s + [("exp", A.v)])


def exp_scale_node(n, s, re, im, deg, A):
    s1, B = scale_node(n, s, re, im, deg, A)
    return exp_node(n, s1, B)


def trig_node(n, re1, im1, re2, im2, s, A):
    s1, X = exp_scale_node(n, s, F(0), F(1), 0, A)
    s2, Y = exp_scale_node(n, s1, F(0), F(-1), 0, A)
    return combine(n, s2, re1, im1, re2, im2, X, Y)


def inv_pre(s, A):
    s1, w = emit(s, ("inv", A.v))
    s2, w2 = mulO(s1, w, w)
    s3, w3 = mulO(s2, w, w2)
    s4, w4 = mulO(s3, w, w3)
    return s4, w2, w3, w4


def inv_node(n, s, A):
    v = len(s)
    s4, w2, w3, w4 = inv_pre(s, A)
    P = pure
    c1 = lambda i: cscale(F(-1), F(0), 0, cmul(P(w2), P(A.g1(i))))
    c2 = lambda i, j: cadd(cscale(F(2), F(0), 0, cmul(P(w3), cmul(P(A.g1(i)), P(A.g1(j))))),
                           cscale(F(-1), F(0), 0, cmul(P(w2), P(A.g2(i, j)))))
    c3 = lambda i, j, k: cadd(cscale(F(-6), F(0), 0, cmul(P(w4), cmul(P(A.g1(i)), cmul(P(A.g1(j)), P(A.g1(k)))))),
                              cadd(cscale(F(2), F(0), 0, cmul(P(w3), cross(A, i, j, k))),
                                   cscale(F(-1), F(0), 0, cmul(P(w2), P(A.g3(i, j, k))))))
    return finish(n, v, c1, c2, c3, s4)


def div_node(n, s, A, B):
    s1, W = inv_node(n, s, B)
    return mul_node(n, s1, A, W)


def sqrt_pre(s, A):
    v = len(s)
    s0, _ = emit(s, ("sqrt", A.v))
    s1, w1 = emit(s0, ("inv", v))
    s2, w2 = mulO(s1, w1, w1)
    s3, w3 = mulO(s2, w1, w2)
    s5, w5 = mulO(s3, w2, w3)
    return s5, w1, w3, w5


def sqrt_node(n, s, A):
    v = len(s)
    s5, w1, w3, w5 = sqrt_pre(s, A)
    P = pure
    h = F(1, 2)
    c1 = lambda i: cscale(h, F(0), 0, cmul(P(w1), P(A.g1(i))))
    c2 = lambda i, j: cadd(cscale(h, F(0), 0, cmul(P(w1), P(A.g2(i, j)))),
                           cscale(F(-1, 4), F(0), 0, cmul(P(w3), cmul(P(A.g1(i)), P(A.g1(j))))))
    c3 = lambda i, j, k: cadd(cscale(F(3, 8), F(0), 0, cmul(P(w5), cmul(P(A.g1(i)), cmul(P(A.g1(j)), P(A.g1(k)))))),
                              cadd(cscale(F(-1, 4), F(0), 0, cmul(P(w3), cross(A, i, j, k))),
                                   cscale(h, F(0), 0, cmul(P(w1), P(A.g3(i, j, k))))))
    return finish(n, v, c1, c2, c3, s5)


Node.g3 = lambda self, i, j, k: self.d3[i][j][k]


def compile_(n, e, s):
    t = e[0]
    if t == "const":
        return const_node(n, s, F(e[1]), F(0), 0)
    if t == "pi":
        return const_node(n, s, F(1, 2), F(0), 1)
    if t == "action":
        return action_node(n, s, e[1])
    if t == "cosMode":
        return trig_char(n, F(1, 2), F(0), F(1, 2), F(0), s, e[1])
    if t == "sinMode":
        return trig_char(n, F(0), F(-1, 2), F(0), F(1, 2), s, e[1])
    if t in ("add", "mul", "div"):
        sa, A = compile_(n, e[1], s)
        sb, B = compile_(n, e[2], sa)
        return {"add": add_node, "mul": mul_node, "div": div_node}[t](n, sb, A, B)
    if t == "pow":
        sa, A = compile_(n, e[1], s)
        return pow_node(n, sa, A, e[2])
    if t in ("exp", "sin", "cos", "sqrt"):
        sa, A = compile_(n, e[1], s)
        if t == "exp":
            return exp_node(n, sa, A)
        if t == "sqrt":
            return sqrt_node(n, sa, A)
        if t == "sin":
            return trig_node(n, F(0), F(-1, 2), F(0), F(1, 2), sa, A)
        return trig_node(n, F(1, 2), F(0), F(1, 2), F(0), sa, A)
    raise ValueError(t)


def jet(n, e):
    s, N = compile_(n, e, [("const", F(0), F(0), 0)])
    z = lambda o: 0 if o is None else o
    return dict(prog=s, v0=N.v, d1=[z(x) for x in N.d1], d2=[[z(x) for x in r] for r in N.d2],
                d3=[[[z(x) for x in r] for r in t] for t in N.d3])


# ------------------------------------------------------------------------------------------------ analysis
UNARY = ("exp", "inv", "sqrt")


def deps(op):
    if op[0] in ("add", "mul"):
        return [op[1], op[2]]
    if op[0] in UNARY:
        return [op[1]]
    return []


def closure(prog, wanted):
    seen, stack = set(), [w for w in wanted if w]
    seen.add(0)
    while stack:
        i = stack.pop()
        if i in seen:
            continue
        seen.add(i)
        stack += deps(prog[i])
    return seen


def kinds(prog):
    """C (constant) / M (Fourier model) per slot, and the class CC / CM / MM of every product."""
    kd, cls = [], {}
    for i, op in enumerate(prog):
        t = op[0]
        if t == "const":
            kd.append("C")
        elif t in ("action", "char"):
            kd.append("M")
        elif t in UNARY:
            kd.append(kd[op[1]])
        else:
            ka, kb = kd[op[1]], kd[op[2]]
            kd.append("C" if ka == kb == "C" else "M")
            if t == "mul":
                cls[i] = "".join(sorted(ka + kb))
    return kd, cls


def census(J, n=2):
    """Program size, witness counts and product classes of the slots needed by H (energy), d1 (invariance) and
    d1 + d2 (Gram / torsion models), for the composition with an embedding."""
    prog = J["prog"]
    kd, cls = kinds(prog)
    d1 = J["d1"]
    d2 = [x for r in J["d2"] for x in r]
    out = dict(length=len(prog), ops={t: sum(1 for o in prog if o[0] == t) for t in
                                      ("const", "action", "char", "add", "mul", "exp", "inv", "sqrt")})
    for name, w in (("energy", [J["v0"]]), ("invariance", d1), ("torsion", d1 + d2), ("all", range(len(prog)))):
        sl = closure(prog, w)
        c = {"CC": 0, "CM": 0, "MM": 0}
        for i in sl:
            if i in cls:
                c[cls[i]] += 1
        out[name] = dict(slots=len(sl), **c, exp=sum(1 for i in sl if prog[i][0] == "exp" and kd[i] == "M"),
                         inv=sum(1 for i in sl if prog[i][0] == "inv" and kd[i] == "M"),
                         sqrt=sum(1 for i in sl if prog[i][0] == "sqrt" and kd[i] == "M"))
    out["sqrt_slots"] = [i for i, o in enumerate(prog) if o[0] == "sqrt"]
    out["inv_slots"] = [i for i, o in enumerate(prog) if o[0] == "inv"]
    out["exp_slots"] = [i for i, o in enumerate(prog) if o[0] == "exp"]
    return out


AJ_COMPILE = AJ.compile_      # the lunar subset, for cross-checks


def big_slots(prog):
    """Slots whose composed model depends on the torus data (an action, a character with an angle-0 component, or
    a function of such a slot): 'big' (full 2-d model); the others are constants or few-term phi-only models."""
    big = []
    for op in prog:
        t = op[0]
        if t == "action":
            big.append(True)
        elif t == "char":
            big.append(op[1][0] != 0)
        elif t in UNARY:
            big.append(big[op[1]])
        elif t in ("add", "mul"):
            big.append(big[op[1]] or big[op[2]])
        else:
            big.append(False)
    return big


def heavy_products(J):
    """Products with both factors big, per check (energy, invariance, torsion)."""
    prog = J["prog"]
    bg = big_slots(prog)
    d1 = J["d1"]
    d2 = [x for r in J["d2"] for x in r]
    out = {}
    for name, w in (("energy", [J["v0"]]), ("invariance", d1), ("torsion", d1 + d2)):
        sl = closure(prog, w)
        out[name] = sum(1 for i in sl if prog[i][0] == "mul" and bg[prog[i][1]] and bg[prog[i][2]])
    return out
