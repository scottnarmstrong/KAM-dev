"""Cartesian polynomials over Q(sqrt 2), mirroring KAM/EffectiveStability/Poly/*.lean.

n = 2 degrees of freedom. A monomial key is (a0, a1, b0, b1): q-exponents then p-exponents.
Merged polynomial = dict key -> QS (nonzero). Majorant ("weight") polynomial = dict key -> Fraction >= 0.
"""
from fractions import Fraction as F
from math import factorial
from qs import QS, ZERO, ONE

N = 2


def deg(k):
    return sum(k)


def clean(P):
    return {k: v for k, v in P.items() if not v.iszero()}


def padd(P, Q):
    R = dict(P)
    for k, v in Q.items():
        R[k] = R[k] + v if k in R else v
    return clean(R)


def pneg(P):
    return {k: -v for k, v in P.items()}


def psub(P, Q):
    return padd(P, pneg(Q))


def psmul(c, P):
    return clean({k: v * c for k, v in P.items()})


def pmul(P, Q):
    R = {}
    for k1, v1 in P.items():
        for k2, v2 in Q.items():
            k = tuple(x + y for x, y in zip(k1, k2))
            w = v1 * v2
            R[k] = R[k] + w if k in R else w
    return clean(R)


def dq(i, P):
    R = {}
    for k, v in P.items():
        if k[i] > 0:
            kk = list(k); kk[i] -= 1
            kk = tuple(kk)
            w = v * k[i]
            R[kk] = R[kk] + w if kk in R else w
    return clean(R)


def dp(i, P):
    R = {}
    for k, v in P.items():
        if k[N + i] > 0:
            kk = list(k); kk[N + i] -= 1
            kk = tuple(kk)
            w = v * k[N + i]
            R[kk] = R[kk] + w if kk in R else w
    return clean(R)


def bracket(P, Q):
    """cartBracket P Q = sum_i dq_i P * dp_i Q - dp_i P * dq_i Q   (Poly/Bracket.lean)."""
    R = {}
    for i in range(N):
        R = padd(R, psub(pmul(dq(i, P), dp(i, Q)), pmul(dp(i, P), dq(i, Q))))
    return R


def adpow(chi, k, P):
    """cartAdPow chi k P: P -> {P, chi} iterated k times."""
    for _ in range(k):
        P = bracket(P, chi)
    return P


def liesum(chi, H, L):
    """cartLieSum chi H L = sum_{j<L} (1/j!) ad^j  (merged)."""
    R = {}
    cur = H
    for j in range(L):
        R = padd(R, psmul(QS(F(1, factorial(j))), cur))
        if j + 1 < L:
            cur = bracket(cur, chi)
    return R


def action(j):
    k1 = [0] * (2 * N); k1[j] = 2
    k2 = [0] * (2 * N); k2[N + j] = 2
    return {tuple(k1): QS(F(1, 2)), tuple(k2): QS(F(1, 2))}


def const(c):
    return {(0,) * (2 * N): QS(c)}


def ppow(P, k):
    R = const(1)
    for _ in range(k):
        R = pmul(R, P)
    return R


def act_subst(Nact):
    """cartActSubst: Nact keyed by q-exponents (k0,k1) (b = 0) -> prod_L (cartAction L)^{k_L}."""
    R = {}
    for key, c in Nact.items():
        prod = const(1)
        for L in range(N):
            prod = pmul(prod, ppow(action(L), key[L]))
        R = padd(R, psmul(c, prod))
    return R


# --- majorants (cartSupBound) ---------------------------------------------------------------

def supbound(P, rho):
    """cartSupBound P (replicate n rho) (replicate n rho) for a merged/normalized P.
    (For an unmerged list this is the sum over its raw terms; callers pass raw-equivalent data.)"""
    return sum((v.absub() * rho ** deg(k) for k, v in P.items()), F(0))


def weights(P):
    return {k: v.absub() for k, v in P.items()}


def wbracket(W, chi):
    """Majorant of the RAW cartBracket W chi: weights multiply by |multiplier| * absUB(c_chi).
    The Lean raw bound is sum over raw terms of absUB(c_raw) rho^deg, and absUB(xy) <= absUB(x)absUB(y),
    so summing the weight polynomial gives an upper bound (>=) of the Lean cartSupBound of the raw list."""
    R = {}
    wc = weights(chi)
    for i in range(N):
        # term 1
        for k1, w1 in W.items():
            if k1[i] == 0:
                continue
            for k2, w2 in wc.items():
                if k2[N + i] == 0:
                    continue
                k = list(k1); k[i] -= 1
                k = tuple(x + y for x, y in zip(k, k2)); k = list(k); k[N + i] -= 1
                k = tuple(k)
                R[k] = R.get(k, F(0)) + w1 * k1[i] * w2 * k2[N + i]
        # term 2
        for k1, w1 in W.items():
            if k1[N + i] == 0:
                continue
            for k2, w2 in wc.items():
                if k2[i] == 0:
                    continue
                k = list(k1); k[N + i] -= 1
                k = tuple(x + y for x, y in zip(k, k2)); k = list(k); k[i] -= 1
                k = tuple(k)
                R[k] = R.get(k, F(0)) + w1 * k1[N + i] * w2 * k2[i]
    return R


def wadpow_bound(chi, L, Q, rho):
    W = weights(Q)
    for _ in range(L):
        W = wbracket(W, chi)
    return sum((w * rho ** deg(k) for k, w in W.items()), F(0))


# --- exact raw semantics (for cross-checks, small orders only) ---------------------------------

def raw_bracket(rawP, chi):
    """raw (unmerged) list of (key, QS) for cartBracket rawP chi, as in Poly/Bracket.lean."""
    out = []
    for i in range(N):
        for k1, v1 in rawP:
            if k1[i] > 0:
                for k2, v2 in chi.items():
                    if k2[N + i] > 0:
                        k = list(k1); k[i] -= 1
                        k = tuple(x + y for x, y in zip(k, k2)); k = list(k); k[N + i] -= 1
                        out.append((tuple(k), v1 * k1[i] * v2 * k2[N + i]))
            if k1[N + i] > 0:
                for k2, v2 in chi.items():
                    if k2[i] > 0:
                        k = list(k1); k[N + i] -= 1
                        k = tuple(x + y for x, y in zip(k, k2)); k = list(k); k[i] -= 1
                        out.append((tuple(k), -(v1 * k1[N + i] * v2 * k2[i])))
    return out


def raw_supbound(raw, rho):
    return sum((v.absub() * rho ** deg(k) for k, v in raw), F(0))


# --- angle average (action-only projection) ---------------------------------------------------

def dfact(n):  # (n)!! for n >= -1
    r = 1
    while n > 1:
        r *= n; n -= 2
    return r


def avg_mono(a, b):
    if a % 2 or b % 2:
        return None
    return F(dfact(a - 1) * dfact(b - 1), dfact(a + b))


def avg_action(P):
    """Angle average of P in the I-variables: returns dict (k0,k1)->QS with q_j^2+p_j^2 = 2 I_j."""
    R = {}
    for key, v in P.items():
        m = F(1); kk = []
        ok = True
        for j in range(N):
            a, b = key[j], key[N + j]
            t = avg_mono(a, b)
            if t is None:
                ok = False; break
            kj = (a + b) // 2
            m *= t * 2 ** kj
            kk.append(kj)
        if ok:
            kk = tuple(kk)
            R[kk] = R[kk] + v * m if kk in R else v * m
    return clean(R)


def avg_poly(P):
    """angle average of P as a polynomial in (q, p) (via act_subst)."""
    return act_subst(avg_action(P))
