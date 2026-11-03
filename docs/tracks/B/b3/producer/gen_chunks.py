"""Emit the chunk accumulators (Data/<Shard>Acc<i>.lean, Data/<Shard>Accs.lean) replaying the four
big `cartEqCheck`s of the Henon-Heiles certificate in chunks (see KAM/.../HenonHeiles/ChunkMerge.lean).
Python mirror of the Lean definitions cartLieSum / cartAdPow / cartBracket / cartActSubst / cartMerge;
untrusted: a mismatch makes the kernel check fail.  Usage: gen_chunks.py <hh-cert.json> <repo-root>."""
import json, os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fractions import Fraction as F
from math import factorial
from qs import QS

BCHUNK = {1: 120, 2: 60, 3: 33}
WCHUNK = 1000
CHUNKS = {"Lie1": 250, "Lie2": 250, "Lie3": 200, "Fin": 250}
ONE = QS(1)


def pq(s):
    return F(s)


def qs_of(c):
    return QS(pq(c["a"]), pq(c["b"]))


def trim(l):
    l = list(l)
    while l and l[-1] == 0:
        l.pop()
    return tuple(l)


def mono(m):
    return (tuple(m["a"]), tuple(m["b"]), qs_of(m["c"]))


def poly(P):
    return [mono(m) for m in P]


def addpad(x, y):
    n = max(len(x), len(y))
    return tuple((x[i] if i < len(x) else 0) + (y[i] if i < len(y) else 0) for i in range(n))


def mmul(m, n):
    return (addpad(m[0], n[0]), addpad(m[1], n[1]), m[2] * n[2])


def pmul(P, Q):
    return [mmul(m, n) for m in P for n in Q]


def getd(l, i):
    return l[i] if i < len(l) else 0


def dq(i, P):
    out = []
    for a, b, c in P:
        e = getd(a, i)
        if e != 0:
            aa = list(a); aa[i] = e - 1
            out.append((tuple(aa), b, c * QS(e)))
    return out


def dp(i, P):
    out = []
    for a, b, c in P:
        e = getd(b, i)
        if e != 0:
            bb = list(b); bb[i] = e - 1
            out.append((a, tuple(bb), c * QS(e)))
    return out


def neg(P):
    return [(a, b, -c) for a, b, c in P]


def width(P):
    return max([max(len(a), len(b)) for a, b, c in P] + [0])


def bracket(P, Q):
    out = []
    for i in range(width(P)):
        out += pmul(dq(i, P), dp(i, Q)) + neg(pmul(dp(i, P), dq(i, Q)))
    return out


def adpow(chi, k, P):
    for _ in range(k):
        P = bracket(P, chi)
    return P


def smul(r, P):
    return [(a, b, r * c) for a, b, c in P]


def liesum(chi, H, L):
    out = []
    for j in range(L):
        out += smul(QS(F(1, factorial(j))), adpow(chi, j, H))
    return out


def unitexp(j, e):
    return tuple([0] * j + [e])


def action(j):
    h = QS(F(1, 2))
    return [(unitexp(j, 2), (), h), ((), unitexp(j, 2), h)]


def ppow(P, k):
    R = [((), (), ONE)]
    for _ in range(k):
        R = pmul(P, R)
    return R


def actprod(a, L):
    R = [((), (), ONE)]
    for k in range(L):
        R = pmul(R, ppow(action(k), getd(a, k)))
    return R


def actsubst(N):
    out = []
    for a, b, c in N:
        out += smul(c, actprod(a, len(a)))
    return out


def insert(m, P):
    """cartInsertMono"""
    for idx, (a, b, c) in enumerate(P):
        if a == m[0] and b == m[1]:
            return P[:idx] + [(a, b, c + m[2])] + P[idx + 1:]
    return P + [m]


def foldr_ins(Y, acc):
    for m in reversed(Y):
        acc = insert(m, acc)
    return acc


def accs(P, Q, n):
    Y = [(trim(a), trim(b), c) for a, b, c in P + neg(Q)]
    m = (len(Y) + n - 1) // n
    out = [foldr_ins(Y[m * n:], [])]
    for i in range(m - 1, -1, -1):
        out.insert(0, foldr_ins(Y[i * n:(i + 1) * n], out[0]))
    nz = [x for x in out[0] if not x[2].iszero()]
    assert not nz, "identity fails in Python: %d nonzero" % len(nz)
    return out


S2UB = F(141422, 100000)


def monobound(m, rho):
    """cartMonoBound m (replicate 2 rho) (replicate 2 rho) = absUB c * prod r^a s^b."""
    a, b, c = m
    v = abs(c.a) + abs(c.b) * S2UB
    for k in range(max(len(a), len(b))):
        v *= (rho if k < 2 else F(0)) ** getd(a, k) * (rho if k < 2 else F(0)) ** getd(b, k)
    return v


def rat(q):
    return "(%d : ℚ)" % q.numerator if q.denominator == 1 else "(%d/%d : ℚ)" % (q.numerator, q.denominator)


def natexpr(n, ind):
    """A natural number as a sum of <=30-digit limbs times powers of ten, one limb per line."""
    if n < 10 ** 30:
        return str(n)
    limbs = []
    k = 0
    while n:
        limbs.append((n % 10 ** 30, 30 * k))
        n //= 10 ** 30
        k += 1
    parts = []
    for v, e in reversed(limbs):
        if v == 0:
            continue
        parts.append(str(v) if e == 0 else "%d * 10 ^ %d" % (v, e))
    return (" +\n" + " " * ind).join(parts)


def ratw(q, ind):
    """Rational literal with limbed numerals (every line <= 100 columns)."""
    if q.denominator == 1:
        return "(%s : ℚ)" % natexpr(q.numerator, ind + 1) if q.numerator >= 0 else rat(q)
    assert q.numerator > 0
    return "((%s)\n%s/ (%s) : ℚ)" % (natexpr(q.numerator, ind + 2), " " * (ind + 1), natexpr(q.denominator, ind + 4))


def ms(m):
    one = "⟨%s, %s, ⟨%s, %s⟩⟩" % (list(m[0]), list(m[1]), rat(m[2].a), rat(m[2].b))
    if len(one) <= 96:
        return one
    return "⟨%s, %s,\n    ⟨%s,\n     %s⟩⟩" % (list(m[0]), list(m[1]), rat(m[2].a), rat(m[2].b))


HDR = """/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.Poly.Coeff
public import KAM.EffectiveStability.Poly.Basic
%s
/-!
# Hénon–Heiles chunk accumulators, %s (track B, B3-CERT)

%s
Generated by `docs/tracks/B/b3/producer/gen_chunks.py`; do not edit.
-/

@[expose] public noncomputable section

namespace KAM.EffectiveStability.HenonHeiles

"""
FTR = "end KAM.EffectiveStability.HenonHeiles\n"


SHARD_HDR = """/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.HenonHeiles.Cert
public import KAM.EffectiveStability.HenonHeiles.ChunkMerge
public import KAM.EffectiveStability.HenonHeiles.Data.%(name)sAccs

/-!
# Shard %(name)s: %(title)s (track B, B3-CERT)

Kernel check of the identity `cartEqCheck P Q = true` with
`P = %(P)s`
and `Q = %(Q)s`,
replayed in %(m)d chunks of %(n)d monomials (`ChunkMerge`), each chunk a separate
`decide +kernel` theorem. Generated by `docs/tracks/B/b3/producer/gen_chunks.py`; do not edit.
-/

@[expose] public noncomputable section

namespace KAM.EffectiveStability.HenonHeiles

open CartPoly

/-- The trimmed unmerged difference checked by shard %(name)s. -/
def hh%(name)sY : List (CartMonoK QSqrt2) :=
  (cartSub
    (%(P)s)
    (%(Q)s)).map CartMonoK.cartMonoTrim

"""


def emit_shard(root, name, title, P, Q, A, n):
    m = len(A) - 1
    out = SHARD_HDR % dict(name=name, title=title, P=P, Q=Q, m=m, n=n)
    Y = "hh%sY" % name
    for i in range(m):
        out += ("theorem hh%s_c%d :\n    ((%s.drop %d).take %d).foldr cartInsertMono hhAcc%s_%d =\n"
                "      hhAcc%s_%d := by\n  decide +kernel\n\n" % (name, i, Y, i * n, n, name, i + 1, name, i))
    out += ("theorem hh%s_c%d : (%s.drop %d).foldr cartInsertMono [] = hhAcc%s_%d := by\n"
            "  decide +kernel\n\n" % (name, m, Y, m * n, name, m))
    out += "theorem hh%s_check :\n    cartEqCheck (%s) (%s) = true := by\n" % (name, P, Q)
    out += "  have h%d := hh%s_c%d\n" % (m, name, m)
    for i in range(m - 1, -1, -1):
        out += "  have h%d := chunk_step %s %d %d %d rfl _ _ h%d hh%s_c%d\n" % (
            i, Y, i * n, n, (i + 1) * n, i + 1, name, i)
    out += ("  have h0' : %s.foldr cartInsertMono [] = hhAcc%s_0 := by\n"
            "    simpa only [List.drop_zero] using h0\n"
            "  exact cartEqCheck_of_merge (A := hhAcc%s_0) h0' (by decide +kernel)\n\n" % (Y, name, name))
    out += "end KAM.EffectiveStability.HenonHeiles\n\nend\n"
    d = os.path.join(os.path.dirname(root), "Shard")
    os.makedirs(d, exist_ok=True)
    with open("%s/%s.lean" % (d, name), "w", encoding="utf-8") as f:
        f.write(out)


BOUND_HDR = """/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.HenonHeiles.Cert
public import KAM.EffectiveStability.HenonHeiles.BracketChunk

/-!
# Shard Bound: the remainder majorants of the three steps (track B, B3-CERT)

`oscChainBound` sums `cartSupBound (cartAdPow gen_k L_k Q_{k-1})` over the unmerged `ad` lists
(up to ~5000 monomials, deeper than the kernel stack allows in one `List.sum`); here each
`cartSupBound` is replayed in seed chunks (`BracketChunk`), each a separate
`decide +kernel` theorem.
Generated by `docs/tracks/B/b3/producer/gen_chunks.py`; do not edit.
-/

@[expose] public noncomputable section

namespace KAM.EffectiveStability.HenonHeiles

open CartPoly

"""


GROUP = 8


def bound_hdr(k, title, imps):
    h = BOUND_HDR.replace("Shard Bound: the remainder majorants of the three steps", title)
    return h.replace("public import KAM.EffectiveStability.HenonHeiles.Cert\n" +
                     "public import KAM.EffectiveStability.HenonHeiles.BracketChunk\n", imps)


def emit_bound(root, k, Zexpr, Z, rho, n, Pexpr, Pl, chi):
    """Returns {filename-suffix: text}: Bound<k>P<g> (chunk theorems) and Bound<k> (assembly)."""
    base = "public import KAM.EffectiveStability.HenonHeiles.Cert\npublic import KAM.EffectiveStability.HenonHeiles.BracketChunk\n"
    Zn = "hhZ%d" % k
    rr = "(List.replicate 2 hhStep%d.ρ)" % k
    m = (len(Pl) + n - 1) // n
    vals = [sum((monobound(x, rho) for x in bracket(Pl[i * n:(i + 1) * n], chi)), F(0)) for i in range(m)]
    groups = [list(range(g, min(g + GROUP, m))) for g in range(0, m, GROUP)]
    files = {}
    for gi, idx in enumerate(groups):
        imps = base if gi == 0 else base + "public import KAM.EffectiveStability.HenonHeiles.Shard.Bound%dP0\n" % k
        out = bound_hdr(k, "Shard Bound%d, part %d: chunk majorants of step %d" % (k, gi, k), imps)
        if gi == 0:
            out += "/-- The unmerged `ad` list of step %d. -/\ndef %s : CartPolyK QSqrt2 :=\n  %s\n\n" % (k, Zn, Zexpr)
            out += "/-- The previous `ad` list of step %d. -/\ndef hhP%d : CartPolyK QSqrt2 :=\n  %s\n\n" % (k, k, Pexpr)
            out += "/-- `%s` with the width made explicit. -/\ndef hhV%d : CartPolyK QSqrt2 :=\n  cartBracketW 2 hhP%d hhStep%d.gen\n\n" % (Zn, k, k, k)
            mw = (len(Pl) + WCHUNK - 1) // WCHUNK
            for i in range(mw):
                chunk = Pl[i * WCHUNK:(i + 1) * WCHUNK]
                wv = max([max(len(a), len(b)) for a, b, c in chunk] + [0])
                assert wv <= 2
                sl = "hhP%d.drop %d" % (k, i * WCHUNK) if i == mw - 1 else "(hhP%d.drop %d).take %d" % (k, i * WCHUNK, WCHUNK)
                out += "theorem hhWidth%d_c%d : cartWidth (%s) = %d := by\n  decide +kernel\n\n" % (k, i, sl, wv)
            wvals = [max([max(len(a), len(b)) for a, b, c in Pl[i * WCHUNK:(i + 1) * WCHUNK]] + [0]) for i in range(mw)]
            out += "theorem hhWidth%d : cartWidth hhP%d = 2 := by\n  have h%d := hhWidth%d_c%d\n" % (k, k, mw - 1, k, mw - 1)
            acc = wvals[-1]
            for i in range(mw - 2, -1, -1):
                acc = max(acc, wvals[i])
                out += "  have h%d : cartWidth (hhP%d.drop %d) = %d :=\n    width_chunk hhP%d %d %d %d rfl _ _ h%d hhWidth%d_c%d\n" % (
                    i, k, i * WCHUNK, acc, k, i * WCHUNK, WCHUNK, (i + 1) * WCHUNK, i + 1, k, i)
            out += "  rw [List.drop_zero] at h0\n  exact h0\n\n"
            out += "theorem hhZ%d_eq : %s = hhV%d :=\n  cartBracket_width _ hhWidth%d\n\n" % (k, Zn, k, k)
        for i in idx:
            out += "/-- Majorant of chunk %d of step %d. -/\ndef hhBv%d_%d : ℚ :=\n  %s\n\n" % (i, k, k, i, ratw(vals[i], 2))
        for i in idx:
            last = (i == m - 1)
            sl = "hhP%d.drop %d" % (k, i * n) if last else "(hhP%d.drop %d).take %d" % (k, i * n, n)
            out += "theorem hhBound%d_c%d :\n    cartSupBound (cartBracketW 2 (%s) hhStep%d.gen)\n      %s %s =\n      hhBv%d_%d := by\n  decide +kernel\n\n" % (
                k, i, sl, k, rr, rr, k, i)
        files["Bound%dP%d" % (k, gi)] = out
    imps = "".join("public import KAM.EffectiveStability.HenonHeiles.Shard.Bound%dP%d\n" % (k, g)
                   for g in range(len(groups)))
    out = bound_hdr(k, "Shard Bound%d: the remainder majorant of step %d" % (k, k), imps)
    for i in range(m - 2, -1, -1):
        rest = "hhBv%d_%d" % (k, m - 1) if i == m - 2 else "hhBs%d_%d" % (k, i + 1)
        out += "/-- Partial sum of the chunk majorants of step %d from chunk %d. -/\ndef hhBs%d_%d : ℚ :=\n  hhBv%d_%d + %s\n\n" % (
            k, i, k, i, k, i, rest)
    top = "hhBs%d_0" % k if m > 1 else "hhBv%d_0" % k
    out += "theorem hhBound%d :\n    cartSupBound hhZ%d %s %s =\n      %s := by\n" % (k, k, rr, rr, top)
    out += "  have h%d := hhBound%d_c%d\n" % (m - 1, k, m - 1)
    for i in range(m - 2, -1, -1):
        tgt = "hhBs%d_%d" % (k, i)
        out += "  have h%d : cartSupBound (cartBracketW 2 (hhP%d.drop %d) hhStep%d.gen)\n      %s %s =\n      %s :=\n    supBoundBr_chunk hhP%d hhStep%d.gen 2 %d %d %d rfl _ _ _ _ h%d hhBound%d_c%d\n" % (
            i, k, i * n, k, rr, rr, tgt, k, k, i * n, n, (i + 1) * n, i + 1, k, i)
    out += "  rw [List.drop_zero] at h0\n  rw [hhZ%d_eq]\n  exact h0\n\n" % k
    files["Bound%d" % k] = out
    return files


def emit(root, name, A):
    parts, cur, curl = [], [], 0
    for i, X in enumerate(A):
        body = ",\n".join("  " + ms(m) for m in X)
        txt = "/-- Accumulator %d of shard %s. -/\ndef hhAcc%s_%d : List (CartMonoK QSqrt2) := [\n%s]\n\n" % (
            i, name, name, i, body)
        ls = len(X) + 4
        if curl + ls > 1100 and cur:
            parts.append(cur); cur, curl = [], 0
        cur.append(txt); curl += ls
    parts.append(cur)
    imps = ""
    for k, part in enumerate(parts, 1):
        with open("%s/%sAcc%d.lean" % (root, name, k), "w", encoding="utf-8") as f:
            f.write(HDR % ("", "shard %s, part %d" % (name, k),
                           "Intermediate merge accumulators of shard %s." % name) + "".join(part) + FTR)
        imps += "public import KAM.EffectiveStability.HenonHeiles.Data.%sAcc%d\n" % (name, k)
    with open("%s/%sAccs.lean" % (root, name), "w", encoding="utf-8") as f:
        f.write(HDR % (imps, "shard %s" % name, "Facade importing the %d accumulators of shard %s." % (
            len(A), name)) + FTR)
    print(name, len(A), [len(x) for x in A], "parts", len(parts))


def main():
    d = json.load(open(sys.argv[1]))
    root = os.path.join(sys.argv[2], "KAM/EffectiveStability/HenonHeiles/Data")
    H, N, P = poly(d["H"]), poly(d["Nact"]), poly(d["P"])
    st = d["steps"]
    gen = [poly(s["gen"]) for s in st]
    out = [poly(s["out"]) for s in st]
    specs = [("Lie1", "the step-1 Lie identity", "cartLieSum hhStep1.gen hhH hhStep1.order", "hhStep1.out",
              liesum(gen[0], H, st[0]["order"]), out[0]),
             ("Lie2", "the step-2 Lie identity", "cartLieSum hhStep2.gen hhStep1.out hhStep2.order",
              "hhStep2.out", liesum(gen[1], out[0], st[1]["order"]), out[1]),
             ("Lie3", "the step-3 Lie identity", "cartLieSum hhStep3.gen hhStep2.out hhStep3.order",
              "hhStep3.out", liesum(gen[2], out[1], st[2]["order"]), out[2]),
             ("Fin", "the final identity `Q₃ = Nact(I) + P`", "hhStep3.out",
              "cartAdd (cartActSubst hhNact) hhP", out[2], actsubst(N) + P)]
    rho = [F(st[k]["rho"]) for k in range(3)]
    Zs = [adpow(gen[0], st[0]["order"], H), adpow(gen[1], st[1]["order"], out[0]),
          adpow(gen[2], st[2]["order"], out[1])]
    Zex = ["cartAdPow hhStep1.gen hhStep1.order hhH", "cartAdPow hhStep2.gen hhStep2.order hhStep1.out",
           "cartAdPow hhStep3.gen hhStep3.order hhStep2.out"]
    Pex = ["cartAdPow hhStep1.gen (hhStep1.order - 1) hhH",
           "cartAdPow hhStep2.gen (hhStep2.order - 1) hhStep1.out",
           "cartAdPow hhStep3.gen (hhStep3.order - 1) hhStep2.out"]
    Pls = [adpow(gen[0], st[0]["order"] - 1, H), adpow(gen[1], st[1]["order"] - 1, out[0]),
           adpow(gen[2], st[2]["order"] - 1, out[1])]
    d = os.path.join(os.path.dirname(root), "Shard")
    os.makedirs(d, exist_ok=True)
    for k in range(3):
        for nm, body in emit_bound(root, k + 1, Zex[k], Zs[k], rho[k], BCHUNK[k + 1], Pex[k], Pls[k], gen[k]).items():
            with open(d + "/%s.lean" % nm, "w", encoding="utf-8") as f:
                f.write(body + "end KAM.EffectiveStability.HenonHeiles\n\nend\n")
    for name, title, ps, qs_, Pp, Qq in specs:
        A = accs(Pp, Qq, CHUNKS[name])
        emit(root, name, A)
        emit_shard(root, name, title, ps, qs_, A, CHUNKS[name])


main()
