#!/usr/bin/env python3
"""SO-ADVCOUNT: Python mirror of the LANDED jet compiler and a count of the products `Slp.compose` performs.

Mirrors `KAM/Certificate/Expr/{DiffBuild,DiffNode,Diff}.lean` (inp 074bd0c5) operation by operation:
`slpEmit`, `slpAddO`, `slpMulO`, `slpScaleO`, `slpCAdd`, `slpCMul`, `slpCScale`, `slpTab1/2/3`, `slpFinish`,
`slpConstNode`, `slpActionNode`, `slpCharNode`, `slpAddNode`, `slpMulNode` (with `slpMulD3`), `slpScaleNode`,
`slpCombine`, `slpPowNode`, `slpTrigChar`, `slpCompile` (const, action, cosMode, add, mul, pow; the lunar
Hamiltonian uses nothing else) and `HamExpr.jet`.  The expression is `soRotHamExprScaled c` verbatim from
`.drafts/design/SOSignaturesLunar.lean` (design Revision 5, A-L).

Composition with the embedding K (the generic `Slp.compose`, SO-EMB, not yet written) is modelled by slot KINDS:
    C  a constant (no action / character below it): a scalar, a one-term model;
    M  a Fourier model: `action j` -> the data component A_j(theta); `char k` -> a shift of the character witness
       (chi_k o K = chi_k * E_{norm(k)}: exact `CertPoly.shift`, no product);
and a `mul a b` slot is a product of kind CC (scalar arithmetic), CM (scalar times model) or MM (a genuine
polynomial product).  Untrusted tooling; no Lean is run.
"""
import json, sys
from fractions import Fraction as F

# ------------------------------------------------------------------------------------------------ program
# an op is a tuple: ("const", re, im, deg) | ("action", j) | ("char", k) | ("add", a, b) | ("mul", a, b)


def emit(s, op):
    return s + [op], len(s)


def addO(s, x, y):
    if x is None:
        return s, y
    if y is None:
        return s, x
    return emit(s, ("add", x, y))


def mulO(s, x, y):
    if x is not None and y is not None:
        return emit(s, ("mul", x, y))
    return s, None


def scaleO(s, re, im, deg, x):
    if x is None:
        return s, None
    if re == 0 and im == 0:
        return s, None
    s2, c = emit(s, ("const", re, im, deg))
    return mulO(s2, c, x)


def pure(x):
    return lambda s: (s, x)


def cadd(c1, c2):
    def f(s):
        s1, x1 = c1(s)
        s2, x2 = c2(s1)
        return addO(s2, x1, x2)
    return f


def cmul(c1, c2):
    def f(s):
        s1, x1 = c1(s)
        s2, x2 = c2(s1)
        return mulO(s2, x1, x2)
    return f


def cscale(re, im, deg, c):
    def f(s):
        s1, x = c(s)
        return scaleO(s1, re, im, deg, x)
    return f


class Node:
    def __init__(self, v, d1, d2, d3):
        self.v, self.d1, self.d2, self.d3 = v, d1, d2, d3

    def g1(self, i):
        return self.d1[i] if i < len(self.d1) else None

    def g2(self, i, j):
        return self.d2[i][j]

    def g3(self, i, j, k):
        return self.d3[i][j][k]


def tab1(n, f, s):
    out = []
    for i in range(2 * n):
        s, x = f(i)(s)
        out.append(x)
    return s, out


def tab2(n, f, s):
    out = []
    for i in range(2 * n):
        s, row = tab1(n, lambda j, i=i: f(i, j), s)
        out.append(row)
    return s, out


def tab3(n, f, s):
    out = []
    for i in range(2 * n):
        s, t = tab2(n, lambda j, k, i=i: f(i, j, k), s)
        out.append(t)
    return s, out


def finish(n, v, c1, c2, c3, s):
    s, d1 = tab1(n, c1, s)
    s, d2 = tab2(n, c2, s)
    s, d3 = tab3(n, c3, s)
    return s, Node(v, d1, d2, d3)


NONE1 = lambda i: pure(None)
NONE2 = lambda i, j: pure(None)
NONE3 = lambda i, j, k: pure(None)


def const_node(n, s, re, im, deg):
    return finish(n, len(s), NONE1, NONE2, NONE3, s + [("const", re, im, deg)])


def action_node(n, s, j):
    def c1(i):
        if i == n + j:
            return lambda s2: emit(s2, ("const", F(1), F(0), 0))
        return pure(None)
    return finish(n, len(s), c1, NONE2, NONE3, s + [("action", j)])


def char_node(n, s, k):
    v = len(s)
    kk = lambda i: F(k[i]) if i < len(k) else F(0)
    c1 = lambda i: cscale(F(0), kk(i), 1, pure(v)) if i < n else pure(None)
    c2 = lambda i, j: cscale(-(kk(i) * kk(j)), F(0), 2, pure(v)) if (i < n and j < n) else pure(None)
    c3 = lambda i, j, l: (cscale(F(0), -(kk(i) * kk(j) * kk(l)), 3, pure(v))
                          if (i < n and j < n and l < n) else pure(None))
    return finish(n, v, c1, c2, c3, s + [("char", tuple(k))])


def add_node(n, s, A, B):
    return finish(n, len(s),
                  lambda i: cadd(pure(A.g1(i)), pure(B.g1(i))),
                  lambda i, j: cadd(pure(A.g2(i, j)), pure(B.g2(i, j))),
                  lambda i, j, k: cadd(pure(A.g3(i, j, k)), pure(B.g3(i, j, k))),
                  s + [("add", A.v, B.v)])


def mul_d3(A, B, i, j, k):
    P = pure
    return cadd(
        cadd(cadd(cmul(P(A.g3(i, j, k)), P(B.v)), cmul(P(A.g2(j, k)), P(B.g1(i)))),
             cadd(cmul(P(A.g2(i, k)), P(B.g1(j))), cmul(P(A.g1(k)), P(B.g2(i, j))))),
        cadd(cadd(cmul(P(A.g2(i, j)), P(B.g1(k))), cmul(P(A.g1(j)), P(B.g2(i, k)))),
             cadd(cmul(P(A.g1(i)), P(B.g2(j, k))), cmul(P(A.v), P(B.g3(i, j, k))))))


def mul_node(n, s, A, B):
    P = pure
    return finish(n, len(s),
                  lambda i: cadd(cmul(P(A.g1(i)), P(B.v)), cmul(P(A.v), P(B.g1(i)))),
                  lambda i, j: cadd(cadd(cmul(P(A.g2(i, j)), P(B.v)), cmul(P(A.g1(j)), P(B.g1(i)))),
                                    cadd(cmul(P(A.g1(i)), P(B.g1(j))), cmul(P(A.v), P(B.g2(i, j))))),
                  lambda i, j, k: mul_d3(A, B, i, j, k),
                  s + [("mul", A.v, B.v)])


def scale_node(n, s, re, im, deg, A):
    s1, C = const_node(n, s, re, im, deg)
    return mul_node(n, s1, C, A)


def combine(n, s, re1, im1, re2, im2, X, Y):
    s1, X1 = scale_node(n, s, re1, im1, 0, X)
    s2, Y1 = scale_node(n, s1, re2, im2, 0, Y)
    return add_node(n, s2, X1, Y1)


def pow_node(n, s, A, m):
    if m == 0:
        return const_node(n, s, F(1), F(0), 0)
    s1, Pm = pow_node(n, s, A, m - 1)
    return mul_node(n, s1, Pm, A)


def trig_char(n, re1, im1, re2, im2, s, k):
    s1, X = char_node(n, s, k)
    s2, Y = char_node(n, s1, tuple(-x for x in k))
    return combine(n, s2, re1, im1, re2, im2, X, Y)


def compile_(n, e, s):
    t = e[0]
    if t == "const":
        return const_node(n, s, F(e[1]), F(0), 0)
    if t == "action":
        return action_node(n, s, e[1])
    if t == "cosMode":
        return trig_char(n, F(1, 2), F(0), F(1, 2), F(0), s, e[1])
    if t == "sinMode":
        return trig_char(n, F(0), F(-1, 2), F(0), F(1, 2), s, e[1])
    if t in ("add", "mul"):
        sa, A = compile_(n, e[1], s)
        sb, B = compile_(n, e[2], sa)
        return (add_node if t == "add" else mul_node)(n, sb, A, B)
    if t == "pow":
        sa, A = compile_(n, e[1], s)
        return pow_node(n, sa, A, e[2])
    raise ValueError(t)


def jet(n, e):
    s, N = compile_(n, e, [("const", F(0), F(0), 0)])
    z = lambda o: 0 if o is None else o
    return dict(prog=s, v0=N.v, d1=[z(x) for x in N.d1], d2=[[z(x) for x in r] for r in N.d2],
                d3=[[[z(x) for x in r] for r in t] for t in N.d3])


# ------------------------------------------------------------------------------------------------ lunar H'
def so_rot_ham_expr_scaled(c, epsA):
    """`soRotHamExprScaled c = .mul (.const c) soRotHamExpr` (A-L, verbatim shape); epsA[m] = soEpsQ * soAQ m."""
    modes = ("const", 0)
    for m in reversed(range(7)):                         # List.range 7 |>.foldr
        modes = ("add", ("mul", ("const", -epsA[m + 1]), ("cosMode", (2, 1 - m))), modes)
    H = ("add", ("action", 1),
         ("add", ("add", ("mul", ("const", F(1, 2)), ("pow", ("action", 0), 2)),
                  ("mul", ("const", F(-1)), ("action", 0))),
          modes))
    return ("mul", ("const", c), H)


# ------------------------------------------------------------------------------------------------ kinds
def kinds(prog):
    """slot kinds (C / M), the 'source' of every M slot (which data it is built from), and the mul classes."""
    kd, src, cls = [], [], {}
    for i, op in enumerate(prog):
        t = op[0]
        if t == "const":
            kd.append("C"); src.append(None)
        elif t == "action":
            kd.append("M"); src.append("A%d" % op[1])
        elif t == "char":
            kd.append("M"); src.append("chi%s" % (op[1],))
        else:
            a, b = op[1], op[2]
            ka, kb = kd[a], kd[b]
            k = "C" if ka == kb == "C" else "M"
            kd.append(k)
            if t == "mul":
                cls[i] = "".join(sorted(ka + kb))          # CC, CM, MM
            sa, sb = src[a], src[b]
            src.append(sa if sb is None else sb if sa is None else "(%s%s%s)" % (sa, "*" if t == "mul" else "+", sb))
    return kd, src, cls


def closure(prog, wanted):
    seen, stack = set(), list(wanted)
    while stack:
        i = stack.pop()
        if i in seen:
            continue
        seen.add(i)
        op = prog[i]
        if op[0] in ("add", "mul"):
            stack += [op[1], op[2]]
    return seen


def count(prog, slots, cls):
    c = {"CC": 0, "CM": 0, "MM": 0}
    for i in slots:
        if i in cls:
            c[cls[i]] += 1
    return c


def report(c=F(237, 125)):
    import model
    epsA = {m: model.EPS * model.A_EXACT[m] for m in model.M_MODES}
    e = so_rot_ham_expr_scaled(c, epsA)
    J = jet(2, e)
    prog = J["prog"]
    kd, src, cls = kinds(prog)
    d1 = J["d1"]
    d2 = [x for r in J["d2"] for x in r]
    wanted = {"invariance (d1)": d1, "energy (v0)": [J["v0"]], "torsion (d1, d2)": d1 + d2,
              "whole program (naive left fold, incl. d3)": list(range(len(prog)))}
    out = dict(program_length=len(prog), ops={t: sum(1 for o in prog if o[0] == t) for t in
                                              ("const", "action", "char", "add", "mul")},
               mul_classes_whole=count(prog, range(len(prog)), cls), per_call={})
    for name, w in wanted.items():
        sl = closure(prog, w)
        mm = sorted(src[i] for i in sl if cls.get(i) == "MM")
        out["per_call"][name] = dict(slots=len(sl), **count(prog, sl, cls), MM_products=mm)
    out["zero_slots_in_tables"] = dict(d1=sum(1 for x in d1 if x == 0), d2=sum(1 for x in d2 if x == 0))
    return out, J, kd, src, cls


if __name__ == "__main__":
    out, *_ = report()
    print(json.dumps(out, indent=1, default=str))
