#!/usr/bin/env python3
"""SO-DATA3: exact mirrors of the v2 refined-route data checks (untrusted tooling; the kernel decides).

  CertificateSharp/Corner/SupBound.lean   signLists, dotList, expLoQ, wloOf, expUb, cornerSumUp, cornerUp,
                                          rowCornerUp, rowCornerLeq
  CertificateSharp/Frame/Majorants.lean   freqNormUp, frameNModels, frameGram, checkFrameL, checkFrameN,
                                          checkFrameT, checkFrameOmega, checkFrameMajorants
  CertificateSharp/V2/HamClaim.lean       hamClaimOk, checkHamClaim

Every function follows the Lean definition step by step in the certificate's backend B (fold order included:
`foldr` is a right fold, so the accumulation runs over the reversed list).  Besides the verdicts, `frame_values`
returns the exact largest vertex value of every checked row (the backend number, as a rational), from which the
claims are chosen (rounded up) and then re-checked with the verdict functions.
"""
from fractions import Fraction as F

import sofx_arith as A
import sofx_model as M
import sofx_check as C
import toy_arith as TA

PI_LO = F(3141592, 1000000)                      # piLoQ


# ---------------------------------------------------------------------------------------------- SupBound.lean
def signLists(n):
    if n == 0:
        return [[]]
    return [x for l in signLists(n - 1) for x in ([True] + l, [False] + l)]


def dotList(k, l):
    return sum((a if b else -a) for a, b in zip(k, l))


def expLoQ(x, N):
    out, fact = F(0), 1
    for j in range(N + 1):
        if j:
            fact *= j
        out += F(x) ** j / fact
    return out


def wloOf(W, N):
    return expLoQ(2 * PI_LO * W.rho, N)


def expUb(W, wlo, m):
    return W.w ** m if m >= 0 else 1 / (wlo ** (-m))


def cornerSumUp(B, W, wlo, l, P):
    acc = B.ofInt(0)
    for k, c in reversed(P):
        acc = B.upAdd(B.upMul(A.normUp(B, c), B.ofRatUp(expUb(W, wlo, dotList(list(k), l)))), acc)
    return acc


def cornerUp(B, W, wlo, l, m):
    return B.upMul(B.ofRatUp(M.degFactorUp(m.deg)), B.upAdd(cornerSumUp(B, W, wlo, l, m.poly), m.rad))


def rowCornerUp(B, W, wlo, l, ms):
    acc = B.ofInt(0)
    for m in reversed(ms):
        acc = B.upAdd(cornerUp(B, W, wlo, l, m), acc)
    return acc


def rowCornerLeq(B, W, wlo, n, ms, b):
    return all(B.ble(rowCornerUp(B, W, wlo, l, ms), b) for l in signLists(n))


def rowCornerMax(B, W, wlo, n, ms):
    """the largest vertex value (exact rational of the backend number): rowCornerLeq ms b iff it is <= b."""
    return max(C.val(B, rowCornerUp(B, W, wlo, l, ms)) for l in signLists(n))


# ---------------------------------------------------------------------------------------------- Majorants.lean
def freqNormUp(box):
    acc = F(0)
    for c, r in reversed(box):
        acc = max(abs(F(c)) + F(r), acc)
    return acc


def frameGram(B, c):
    p = c.params
    return C.gramCheck(B, c.n, c.emb, c.gramInv, c.weight, c.cfgLow, c.piEnc, p["sB"] - p["mu"], c.DKc)


def frameNModels(B, c, eps):
    n, m = c.n, c.n + c.n
    L = C.dkModels(B, n, c.DKc)
    Gi = C.buildMat(n, n, lambda k, j: M.Model(0, C.gramInvPoly(c.gramInv, k, j), eps))
    return C.modelMatOmega(B, n, n, C.modelMatMul(B, c.weight, c.cfgLow, c.piEnc, (4, 0), m, n, n, L, Gi))


def frame_rows(B, c):
    """the rows checked by checkFrameL/N/T: lists of models, by family; None where the Lean returns false."""
    n, m = c.n, c.n + c.n
    DK = C.dkModels(B, n, c.DKc)
    rows = dict(L=[[C.entry(DK, r, j, B) for r in range(m)] for j in range(n)])
    db = frameGram(B, c)
    if db is None:
        return rows
    eps = C.gramInvRadius(B, db)
    if eps is not None:
        Nm = frameNModels(B, c, eps)
        rows["N"] = [[C.entry(Nm, r, j, B) for j in range(n)] for r in range(m)]
        rows["Nt"] = [[C.entry(Nm, r, j, B) for r in range(m)] for j in range(n)]
    p = c.params
    T = C.torsionModels(B, n, c.jet, c.emb, c.wit, c.gramInv, db, c.freqBox, p["s"], c.weight, c.cfgLow, c.piEnc,
                        c.DKc)
    if T is not None:
        rows["T"] = [[C.entry(T, i, j, B) for j in range(n)] for i in range(n)]
    return rows


def frame_values(B, c, rows=None):
    rows = frame_rows(B, c) if rows is None else rows
    W, wlo = c.weight, wloOf(c.weight, c.expOrder)
    out = {k: [rowCornerMax(B, W, wlo, c.n, ms) for ms in v] for k, v in rows.items()}
    out["Om"] = [freqNormUp(c.freqBox)]
    return out


def checkFrameMajorants(B, c, b, rows=None):
    """b = dict(bL, bN, bNt, bT, bOm) of rationals: the four Lean checks, conjoined."""
    rows = frame_rows(B, c) if rows is None else rows
    W, wlo, n = c.weight, wloOf(c.weight, c.expOrder), c.n
    leq = lambda fam, q: fam in rows and all(rowCornerLeq(B, W, wlo, n, ms, B.ofRatDown(q)) for ms in rows[fam])
    res = dict(L=leq("L", b["bL"]), N=leq("N", b["bN"]) and leq("Nt", b["bNt"]), T=leq("T", b["bT"]),
               Om=freqNormUp(c.freqBox) <= b["bOm"])
    return all(res.values()), res


# ---------------------------------------------------------------------------------------------- HamClaim.lean
def ham_values(c):
    """the four sums of hamClaimOk (exact rationals; Slp.balls with the SO-BALLDY rounding), or None."""
    bs = TA.slp_balls(c.n, c.jetOps_toy, c.weightH.w, c.centre, c.radius, c.expOrder)
    if bs is None:
        return None
    m, J = 2 * c.n, c.jet
    g = lambda L, a, d: L[a] if a < len(L) else d
    d1 = lambda a: C.slotMagQ(bs, g(J["d1"], a, 0))
    d2 = lambda a, b: C.slotMagQ(bs, g(g(J["d2"], a, []), b, 0))
    d3 = lambda a, b, e: C.slotMagQ(bs, g(g(g(J["d3"], a, []), b, []), e, 0))
    return dict(dh=sum(d1(a) for a in range(m)),
                dx=max(sum(d2(a, b) for b in range(m)) for a in range(m)),
                d2x=max(sum(d3(a, b, e) for b in range(m) for e in range(m)) for a in range(m)),
                d2h=sum(d2(a, b) for a in range(m) for b in range(m)))


def checkHamClaim(c, R, hv=None):
    hv = ham_values(c) if hv is None else hv
    return hv is not None and all(hv[k] <= R[k] for k in ("dh", "dx", "d2x", "d2h"))
