#!/usr/bin/env python3
"""LOCK-GEN part 2: Python mirror of the jet compiler for the constructors `adv_jet.py` does not cover.

`adv_jet.py` mirrors const, action, cosMode, sinMode, add, mul, pow.  This module adds, operation by operation,
the remaining nodes of `KAM/Certificate/Expr/{DiffNode,Diff,DiffNodeSqrt}.lean` (inp 7e8f8c02):
  pi                       slpConstNode s (1/2) 0 1
  slpExpNode / slpExpD3    exp
  slpExpScaleNode          exp (c A)
  slpTrigNode              sin, cos of an expression: exp(i A), exp(-i A), combined
  slpInvPre / slpInvTail / slpInvD3, slpDivNode
  slpSqrtPre / slpSqrtTail / slpSqrtD3 (the sqrt node: V = sqrt x, w = V^-1, w^2, w^3 = w w^2, w^5 = w^2 w^3)
and `compile_`, `jet` over the full constructor set.  Ops are tuples ("const", re, im, deg) | ("action", j) |
("char", k) | ("add", a, b) | ("mul", a, b) | ("exp", a) | ("inv", a) | ("sqrt", a).  Untrusted tooling.

`parse_jet_lit` reads a landed `HamJet` literal (the SO-LOCK-COST gate's `G1lit.lean`, printed by the elaborator
from `(lockHamExpr Ω cs).jet`); `python3 lock_jet.py check-lit G1lit.lean` compares it with this mirror field by
field (LOCK-GEN-2 Part 3: 3116 ops, identical).
"""
import re
import sys
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


# ------------------------------------------------------------------------------------------------ landed literal
_Q = r"\(\((-?\d+) : ℚ\) / (\d+)\)"


def parse_op_lit(line):
    """One `SlpOp.…` literal in the gate's `opLit` format, as an op tuple."""
    t = line.split()[0][len("SlpOp."):]
    if t == "const":
        (a, b), (c, d) = re.findall(_Q, line)[:2]
        return ("const", F(int(a), int(b)), F(int(c), int(d)), int(re.search(r"\((-?\d+)\)$", line).group(1)))
    if t == "char":
        return ("char", tuple(int(x) for x in re.findall(r"\((-?\d+) : ℤ\)", line)))
    return (t,) + tuple(int(x) for x in line.split()[1:])


def parse_jet_lit(text):
    """The `lockOpsLit` chunks and the `lockJetLit` roots (v0, d1, d2, d3) of a gate probe file."""
    prog = [parse_op_lit(ln.strip().rstrip(",]")) for ln in text.splitlines() if ln.strip().startswith("SlpOp.")]
    roots = re.search(r"def lockJetLit : HamJet := ⟨⟨lockOpsLit⟩, (\d+), (.*)⟩\s*$", text, re.M)
    d1, d2, d3 = eval("[" + roots.group(2) + "]")
    return dict(prog=prog, v0=int(roots.group(1)), d1=d1, d2=d2, d3=d3)


def norm_op(o):
    if o[0] == "char":
        return ("char", tuple(o[1]))
    if o[0] == "const":
        return ("const", F(o[1]), F(o[2]), o[3])
    return tuple(o)


def compare_jets(J, K):
    """First differing op index (None if the programs agree) and whether the roots agree."""
    a, b = [norm_op(o) for o in J["prog"]], [norm_op(o) for o in K["prog"]]
    first = next((i for i, (x, y) in enumerate(zip(a, b)) if x != y), None if len(a) == len(b) else min(len(a), len(b)))
    return dict(lengths=(len(a), len(b)), first_diff=first,
                roots=all(J[k] == K[k] for k in ("v0", "d1", "d2", "d3")))


def nonzero_entries(J):
    return (1 + sum(1 for x in J["d1"] if x) + sum(1 for r in J["d2"] for x in r if x)
            + sum(1 for t in J["d3"] for r in t for x in r if x))


if __name__ == "__main__" and sys.argv[1:2] == ["check-lit"]:
    import lock_ham as LH
    from lock_emit import OMEGA_R, CENTRE
    lit = parse_jet_lit(open(sys.argv[2]).read())
    bare = jet(2, LH.lock_ham_expr(OMEGA_R, CENTRE))
    wrapped = jet(2, LH.lock_ham_scaled(1, OMEGA_R, CENTRE))
    print("landed literal vs lock_ham_expr:", compare_jets(bare, lit))
    print("certificate ham .mul (.const κ) lockHamExpr: %d ops = %d + 1 const + %d products (nonzero jet entries)"
          % (len(wrapped["prog"]), len(bare["prog"]), nonzero_entries(bare)))
