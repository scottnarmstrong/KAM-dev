#!/usr/bin/env python3
"""V2-3FREQ: exact mirror of the three-frequency sharp site, producer, and cubic Diophantine check.

Untrusted tooling.  Transcribes over Fraction, with the Lean names:

  KAM/CertificateSharp/V2/Fiber/TailTau.lean   expLowQ, cLoQ, tailQ
  KAM/CertificateSharp/V2/Fiber/Enum2.lean     ceilDiv, mulUp, sqMulUp, powUp, nearP, mode3, rowA, rowW, cell2,
                                               row2, walk2 (balFold)
  KAM/CertificateSharp/V2/Fiber/Site3.lean     clockC, clockR, clockRad, clockBox2, dboxOk, fibGamma, fibBound,
                                               fibSumOk, fiberSiteOk
  KAM/CertificateSharp/Freq/CubicNorm.lean     cubicH, cubicW, polyAbsUp, cubicDioOk

The walk is mirrored cell by cell (same order, same integer rounding: every quotient rounded UP).
`fiberSiteOk` returns the Lean Bool; `produce_site` picks a witness (N, l, J, P, e, D, B) and the
smallest short constant c it certifies; `lean_fibwit` prints the FibWit literal.

Float helpers (`sd_sum_float`, `classical_c_float`, `sjs_estimate`) are estimates only.

Usage:
  python3 -I scripts/certifier/fiber3.py toy        # the T3 sites (witnesses, constants, timings)
  python3 -I scripts/certifier/fiber3.py sjs        # mode counts and constants at the SJS bites
  python3 -I scripts/certifier/fiber3.py cubic      # cubicDioOk on the T3 frequency
"""
import itertools
import math
import sys
import time
from fractions import Fraction as F

HALF = F(1, 2)
FIBER_C0Q = 4 + F(99225, 30000)
PI2_3 = F(99225, 30000)


def floor_q(q):
    return q.numerator // q.denominator


def ceil_q(q):
    return -((-q.numerator) // q.denominator)


# ----------------------------------------------------------------------------- TailTau.lean
def expLowQ(delta, J):
    x = F(628, 100) * delta
    return sum(x ** i / math.factorial(i) for i in range(J + 1))


def cLoQ(delta, tau, N):
    return F(628, 100) * delta - F(2 * tau) / (N + 1)


def inv(q):
    return F(0) if q == 0 else 1 / F(q)


def tailQ(gamma, delta, tau, N, Ep):
    return (2 * (1 + F(2) ** tau) * inv(gamma ** 2) * (F(63, 10) * delta)
            * ((F(N) + 1) ** (2 * tau) * Ep) * (1 + inv(cLoQ(delta, tau, N))))


# ----------------------------------------------------------------------------- Enum2.lean
def ceilDiv(A, B):
    return (A + B - 1) // B


def mulUp(P, a, b):
    return ceilDiv(a * b, 2 ** P)


def sqMulUp(e, P, r, h):
    return mulUp(P, h, h) if r == 0 else mulUp(P, mulUp(P, h, h), e)


def powUp(e, P, f, j):
    if f == 0 or j == 0:
        return 2 ** P
    return sqMulUp(e, P, j % 2, powUp(e, P, f - 1, j // 2))


def nearP(q, X):
    return (2 ** q - 2 * X) // 2 ** (q + 1)


def mode3(D, e, P, a, b):
    """The rounded term (times 2^P) of the mode (a, b), or None.  D = (q, C0, C1, R0, R1)."""
    q, C0, C1, R0, R1 = D
    X = a * C0 + b * C1
    p = nearP(q, X)
    Y = abs(X + p * 2 ** q)
    Rd = abs(a) * R0 + abs(b) * R1
    if Rd < Y and 2 * (Y + Rd) <= 2 ** q:
        s = abs(a) + abs(b)
        Es = powUp(e, P, 64, s)
        t = ceilDiv(powUp(e, P, 64, s + abs(p)) * 2 ** (2 * q), (Y - Rd) ** 2)
        t += 0 if p == 0 else ceilDiv(Es * 4, (2 * abs(p) - 1) ** 2)
        t += ceilDiv(Es * powUp(e, P, 64, 1) * 14615, 2 ** P * 2000)
        return t
    return None


def rowA(N, i):
    return i - N


def rowW(N, i):
    return max(0, N - abs(rowA(N, i)))


def cell2(M, N, i, j):
    w = rowW(N, i)
    if 2 * w < j:
        return 0
    if rowA(N, i) == 0 and j - w == 0:
        return 0
    return M(rowA(N, i), j - w)


def walk2(M, N, l):
    """The walk: rows i < 2^l and columns j < 2^l (None if a mode fails)."""
    tot = 0
    for i in range(2 ** l):
        if 2 * N < i:
            continue
        for j in range(2 ** l):
            v = cell2(M, N, i, j)
            if v is None:
                return None
            tot += v
    return tot


def walk2_fast(M, N):
    """Same value as walk2 (only the diamond's cells are nonzero)."""
    tot = 0
    for a in range(-N, N + 1):
        w = N - abs(a)
        for b in range(-w, w + 1):
            if a == 0 and b == 0:
                continue
            v = M(a, b)
            if v is None:
                return None
            tot += v
    return tot


# ----------------------------------------------------------------------------- Site3.lean
def getD(box, i):
    return box[i] if i < len(box) else (F(0), F(0))


def clockC(box):
    return getD(box, 2)[0]


def clockR(box):
    return getD(box, 2)[1]


def clockRad(box, i):
    return ((getD(box, i)[1] * clockC(box) + abs(getD(box, i)[0]) * clockR(box))
            * inv((clockC(box) - clockR(box)) * clockC(box)))


def clockBox2(box):
    return [(getD(box, 0)[0] * inv(clockC(box)), clockRad(box, 0)),
            (getD(box, 1)[0] * inv(clockC(box)), clockRad(box, 1))]


def dboxOk(box, D):
    q, C0, C1, R0, R1 = D
    cb = clockBox2(box)
    return (abs(F(C0, 2 ** q) - cb[0][0]) + cb[0][1] <= F(R0, 2 ** q)
            and abs(F(C1, 2 ** q) - cb[1][0]) + cb[1][1] <= F(R1, 2 ** q))


def fibGamma(box, gamma):
    return gamma * inv(clockC(box) + clockR(box))


def fibBound(box, gamma, b, tau, w, s):
    P = w["P"]
    return (F(powUp(w["e"], P, 64, 1), 2 ** P) * F(99225, 30000) + F(s, 2 ** P)
            + tailQ(fibGamma(box, gamma), 2 * b, tau, w["N"], F(powUp(w["e"], P, 64, w["N"] + 1), 2 ** P)))


def fibWalk(w, fast=True):
    M = lambda a, b: mode3(w["D"], w["e"], w["P"], a, b)
    return walk2_fast(M, w["N"]) if fast else walk2(M, w["N"], w["l"])


def fiberSiteOk(n, tau, box, gamma, b, c, w, fast=True, detail=False):
    """The Lean Bool (in the order of the conjunction)."""
    def no(why):
        return (False, why) if detail else False
    if n != 3:
        return no("n")
    if not (0 < c and 0 < b and 0 < gamma):
        return no("c, b, gamma")
    if not 0 < clockC(box) - clockR(box):
        return no("clock")
    if not dboxOk(box, w["D"]):
        return no("dbox")
    if not 0 < cLoQ(2 * b, tau, w["N"]):
        return no("cLoQ")
    if not (w["e"] <= 2 ** w["P"] and 2 ** w["P"] <= w["e"] * expLowQ(2 * b, w["J"])):
        return no("e")
    if not 2 * w["N"] + 1 <= 2 ** w["l"]:
        return no("l")
    s = fibWalk(w, fast)
    if s is None:
        return no("mode")
    if not fibBound(box, gamma, b, tau, w, s) <= w["B"]:
        return no("bound")
    kl = clockC(box) - clockR(box)
    if not F(2) ** n * w["B"] * inv(kl ** 2) * (gamma * b ** tau) ** 2 <= (2 * F(31415, 10000) * c) ** 2:
        return no("constant")
    return (True, s) if detail else True


# ----------------------------------------------------------------------------- producer
def up(x, sig=4):
    """A short rational >= x > 0."""
    x = F(x)
    e = math.floor(math.log10(float(x))) - sig + 1
    q = F(10) ** e
    return F(ceil_q(x / q)) * q


def dbox_for(box, q):
    """The dyadic box (q, C0, C1, R0, R1) containing clockBox2(box)."""
    cb = clockBox2(box)
    C = [round(c * 2 ** q) for c, _ in cb]
    R = [ceil_q((abs(F(C[i], 2 ** q) - cb[i][0]) + cb[i][1]) * 2 ** q) for i in range(2)]
    return (q, C[0], C[1], R[0], R[1])


def produce_site(box, gamma, b, tau, n=3, tail_frac=F(1, 1000), P=64, q=64, J=None, Nmax=40000):
    """Pick (N, l, J, P, e, D, B) and the smallest 4-digit c; returns (w, c, s)."""
    delta = 2 * b
    if J is None:
        J = max(8, int(3 * float(F(628, 100) * delta)) + 8)
    e = ceil_q(F(2) ** P / expLowQ(delta, J))
    cb = clockBox2(box)
    S_est = sd_sum_fiber_float((cb[0][0], cb[1][0]), float(delta), 64)
    gp = fibGamma(box, gamma)
    N = max(2, math.ceil(tau / (3.14 * float(delta))))
    while True:
        if cLoQ(delta, tau, N) > 0:
            Ep = F(powUp(e, P, 64, N + 1), 2 ** P)
            if float(tailQ(gp, delta, tau, N, Ep)) <= float(tail_frac) * S_est:
                break
        N += max(1, N // 8)
        if N > Nmax:
            raise ValueError("N too large")
    l = (2 * N).bit_length()
    w = {"N": N, "l": l, "J": J, "P": P, "e": e, "D": dbox_for(box, q), "B": F(0)}
    s = fibWalk(w)
    if s is None:
        raise ValueError("a mode fails")
    w["B"] = up(fibBound(box, gamma, b, tau, w, s), 6)
    kl = clockC(box) - clockR(box)
    rhs = F(2) ** n * w["B"] / kl ** 2 * (gamma * b ** tau) ** 2
    c = up(math.sqrt(float(rhs)) / (2 * 3.1415), 4)
    while not (rhs <= (2 * F(31415, 10000) * c) ** 2):
        c = up(float(c) * 1.0001, 4)
    assert fiberSiteOk(n, tau, box, gamma, b, c, w)
    return w, c, s


def lean_fibwit(w):
    """The FibWit literal."""
    q, C0, C1, R0, R1 = w["D"]
    B = w["B"]
    return ("{ N := %d, l := %d, J := %d, P := %d, e := %d,\n    D := { q := %d, C0 := %d, C1 := %d, R0 := %d, "
            "R1 := %d },\n    B := %d / %d }" % (w["N"], w["l"], w["J"], w["P"], w["e"], q, C0, C1, R0, R1,
                                                B.numerator, B.denominator))


# ----------------------------------------------------------------------------- floats
def sd_sum_fiber_float(cs, delta, N):
    """Float estimate of S((omega', 1), delta) by the fibered bound (no rounding, no tail)."""
    c0, c1 = float(cs[0]), float(cs[1])
    E = math.exp(-2 * math.pi * delta)
    tot = E * math.pi ** 2 / 3
    for a in range(-N, N + 1):
        w = N - abs(a)
        for b in range(-w, w + 1):
            if a == 0 and b == 0:
                continue
            x = a * c0 + b * c1
            p = math.floor(-x + 0.5)
            y = abs(x + p)
            s = abs(a) + abs(b)
            tot += E ** (s + abs(p)) / y ** 2 + E ** s * ((0 if p == 0 else 1 / (abs(p) - 0.5) ** 2)
                                                         + E * (4 + math.pi ** 2 / 3))
    return tot


def sd_sum_float(omega, b, R):
    """S(omega, b) = sum_{0<|k|_1<=R} |k.omega|^-2 e^{-4 pi b |k|_1} (direct, n = 3)."""
    import numpy as np
    ks = np.array([k for k in itertools.product(range(-R, R + 1), repeat=3)
                   if 0 < sum(map(abs, k)) <= R])
    dots = ks @ np.array(omega, dtype=float)
    l1 = np.abs(ks).sum(1)
    return float((np.exp(-4 * math.pi * b * l1) / dots ** 2).sum())


def classical_c_float(n, tau, b):
    """c_natural(n, tau, b) (cohConstC), float."""
    z = sum(1 / (2 ** tau + j) ** 2 for j in range(200000))
    A = 2 ** (2 * tau + 1) * z
    eps = 4 * math.pi * b * (2 * tau / math.e) ** (2 * tau) / math.gamma(2 * tau + 1)
    return (2 * math.pi) ** -1 * math.sqrt(2 ** n * (A * math.gamma(2 * tau + 1) * (1 + eps))) * \
        (4 * math.pi) ** (-tau)


# ----------------------------------------------------------------------------- CubicNorm.lean
def cubicH(p0, p1, p2):
    """H(theta) = sum_l H_l theta^l (symmetric 3x3, entries in 1/2 Z): Y(u) = u^T H u."""
    H = [[[F(0)] * 3 for _ in range(3)] for _ in range(3)]   # H[l][a][b]

    def put(l, a, b, v):
        v = F(v)
        if a == b:
            H[l][a][a] += v
        else:
            H[l][a][b] += v / 2
            H[l][b][a] += v / 2
    # y0
    put(0, 0, 0, 1); put(0, 0, 1, -p2); put(0, 0, 2, p2 * p2 - 2 * p1); put(0, 1, 1, p1)
    put(0, 1, 2, p0 - p1 * p2); put(0, 2, 2, p1 * p1 - p0 * p2)
    # y1
    put(1, 0, 1, -1); put(1, 1, 1, p2); put(1, 1, 2, -p2 * p2); put(1, 2, 2, p1 * p2 - p0)
    # y2
    put(2, 0, 2, -1); put(2, 1, 1, 1); put(2, 1, 2, -p2); put(2, 2, 2, p1)
    return H


def cubicW(A, p0, p1, p2):
    """W_l = A H_l A^T (exact)."""
    H = cubicH(p0, p1, p2)
    return [[[sum(A[i][a] * A[j][b] * H[l][a][b] for a in range(3) for b in range(3))
              for j in range(3)] for i in range(3)] for l in range(3)]


def polyAbsUp(w0, w1, w2, tc, tr):
    """|w0 + w1 t + w2 t^2| <= ... for |t - tc| <= tr."""
    return abs(w0 + w1 * tc + w2 * tc * tc) + tr * (abs(w1) + abs(w2) * (2 * abs(tc) + tr))


def cubic_eval(p0, p1, p2, z):
    return z ** 3 + p2 * z ** 2 + p1 * z + p0


def cubicDioOk(p0, p1, p2, tc, tr, A, D, gamma):
    if p0 == 0 or any(cubic_eval(p0, p1, p2, z) == 0 for z in range(-abs(p0), abs(p0) + 1)):
        return False
    det = (A[0][0] * (A[1][1] * A[2][2] - A[1][2] * A[2][1]) - A[0][1] * (A[1][0] * A[2][2] - A[1][2] * A[2][0])
           + A[0][2] * (A[1][0] * A[2][1] - A[1][1] * A[2][0]))
    if det == 0 or not (0 < D and 0 < gamma and 0 <= tr):
        return False
    W = cubicW(A, p0, p1, p2)
    Wb = max(polyAbsUp(W[0][i][j], W[1][i][j], W[2][i][j], tc, tr) for i in range(3) for j in range(3))
    return gamma * D * Wb <= 1


def cubic_gamma(p0, p1, p2, tc, tr, A, D):
    W = cubicW(A, p0, p1, p2)
    Wb = max(polyAbsUp(W[0][i][j], W[1][i][j], W[2][i][j], tc, tr) for i in range(3) for j in range(3))
    return 1 / (D * Wb), Wb


# ----------------------------------------------------------------------------- data
def t3_box():
    import json
    import pathlib
    root = pathlib.Path(__file__).resolve().parents[2]
    d = json.load(open(root / "certificates/so-toys/T3.json"))["certificate"]
    return [(F(c), F(r)) for c, r in d["freqBox"]]


def main(argv):
    what = argv[1] if len(argv) > 1 else "toy"
    if what == "toy":
        box = t3_box()
        gamma, tau = F(1, 12), 2
        th = 2 ** (1 / 3)
        omega = [th / 2, th * th / 2, 0.5]
        for b in [F(1), F(1, 2), F(1, 4)]:
            t0 = time.time()
            w, c, s = produce_site(box, gamma, b, tau)
            dt = time.time() - t0
            S = sd_sum_float(omega, float(b), 30)
            csharp = (2 * math.pi) ** -1 * 2 ** 1.5 * math.sqrt(S) * float(gamma) * float(b) ** tau
            print(f"b={b}: N={w['N']} l={w['l']} J={w['J']} P={w['P']} e={w['e']} B={float(w['B']):.6g}"
                  f" c={c} (={float(c):.4g}) exact-S c={csharp:.4g} classical={classical_c_float(3, 2, float(b)):.4g}"
                  f" modes={2 * w['N'] * (w['N'] + 1)} python {dt:.2f}s")
    elif what == "cubic":
        tc = F(12599210498948731647672106072782283505702514647015079800819751121, 10 ** 64)
        g, Wb = cubic_gamma(-2, 0, 0, tc, F(1, 10 ** 60), [[0, 1, 0], [0, 0, 1], [1, 0, 0]], 2)
        print("T3 frequency (x/2, x^2/2, 1/2), x^3 = 2: Wbar =", float(Wb), " gamma =", float(g))
        print("cubicDioOk(gamma=99/500):", cubicDioOk(-2, 0, 0, tc, F(1, 10 ** 60),
                                                    [[0, 1, 0], [0, 0, 1], [1, 0, 0]], 2, F(99, 500)))
    elif what == "sjs":
        sjs_estimate()


def sjs_estimate():
    """Mode counts and float constants at the SJS bites (docs/explorations/sjs-plan.md)."""
    # FH25 planar SJS frequencies (sjs-plan, 10^-8 row); only ratios matter for S at the clock form
    for delta in [2.65e-3, 5.3e-4]:
        b = delta / 2
        for tau in [2]:
            # N with 2 pi delta (N+1) ~ 2 tau ln(N+1) + 30
            N = 10
            while 2 * math.pi * delta * (N + 1) < 2 * tau * math.log(N + 1) + 30:
                N += 1
            print(f"delta={delta:g} (b={b:g}): N~{N}, fibres 2N(N+1)={2 * N * (N + 1):,},"
                  f" full box ~{4 * N ** 3 // 3:,}; classical c(3,2,b)={classical_c_float(3, 2, b):.4g}")


if __name__ == "__main__":
    main(sys.argv)
