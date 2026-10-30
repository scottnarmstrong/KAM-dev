"""Exact mirror of KAM.CertificateSharp.V2.L1.gamOk / fibCheck (package C6L1).

Gamma_inf(s w*, delta) for a clock box [(c0, r0), (kappa, 0)]: the fibered test on
w' in [c0/kappa - r0/kappa, c0/kappa + r0/kappa], Diophantine constant g = gamma/kappa,
then Gamma(s w*) <= claim / (s kappa).  Usage: functions below; run as a script for R1 and T2.
"""
from fractions import Fraction as F
import math


def fexpLow(d):
    y = F(6283, 1000) * d
    return 1 + y + y ** 2 / 2 + y ** 3 / 6 + y ** 4 / 24


def floor(q):
    return q.numerator // q.denominator


def fpk(c, z):
    return floor(-(F(z) * c) + F(1, 2))


def fdist(c, z):
    return abs(F(z) * c + fpk(c, z))


def flb(c, r, z):
    return fdist(c, z) - abs(F(z)) * r


def fiberOk(c, r, N, E1, claim, z):
    p = fpk(c, z)
    return (fdist(c, z) + abs(F(z)) * r <= F(1, 2) and flb(c, r, z) > 0
            and E1 ** (abs(z) + abs(p)) <= claim * (F(628, 100) * flb(c, r, z))
            and E1 ** abs(z) <= claim * F(314, 100))


def fibCheck(c, r, g, d, N, E1, claim, why=False):
    conds = [d > 0, g > 0, 1 <= F(628, 100) * d * (N + 1), 1 <= E1 * fexpLow(d),
             (N + 1) * E1 ** (N + 1) <= claim * (F(628, 100) * g), E1 <= claim * F(628, 100)]
    if not all(conds):
        return (False, [i for i, x in enumerate(conds) if not x]) if why else False
    for j in range(N):
        for z in (j + 1, -(j + 1)):
            if not fiberOk(c, r, N, E1, claim, z):
                return (False, ("fiber", z)) if why else False
    return (True, None) if why else True


def gamOk(box, kappa, gamma, s, d, G, N, E1, claim):
    (c0, r0), (k1, r1) = box
    assert k1 == kappa and r1 == 0 and kappa > 0 and s > 0
    ok = fibCheck(c0 / kappa, r0 / kappa, gamma / kappa, d, N, E1, claim)
    return ok and claim <= G * (s * kappa)


def gamma_float(w1, d, K=3000):
    """sup_{k != 0} exp(-2 pi d |k|_1) / (2 pi |k . (w1, 1)|), k = (k1, k2)."""
    best = 0.0
    for k1 in range(-K, K + 1):
        p = -round(k1 * w1)
        for k2 in (p - 1, p, p + 1):
            if k1 == 0 and k2 == 0:
                continue
            dot = abs(k1 * w1 + k2)
            if dot == 0:
                continue
            v = math.exp(-2 * math.pi * d * (abs(k1) + abs(k2))) / (2 * math.pi * dot)
            best = max(best, v)
    return best


def min_E1(d, digits=4):
    """the smallest short rational E1 with 1 <= E1 * fexpLow(d)."""
    den = 10 ** digits
    lo = F(1) / fexpLow(d)
    return F(math.ceil(lo * den), den)


if __name__ == "__main__":
    # R1 (C6's r1Box, r1Kappa, s = 1 + 1e-6), the l1 strip rho' = 1/70 (sup data on T_{1/70 + 1/10^5})
    k = F(7, 4) / (1 + F(1, 10 ** 6))
    box = [(-(79 - F(2236067977, 10 ** 9)) / 3118 * k, F(1, 10 ** 12)), (k, F(0))]
    gamma = k / 42
    s = 1 + F(1, 10 ** 6)
    rho1 = F(1, 70)
    rinf = F(1, 70000)
    d0 = min(F(1), (rho1 - rinf) / 6)
    w1 = float(box[0][0] / k)
    import sys
    for d, lab in ((d0, "delta0"), (rho1, "rho'")):
        gfib = gamma_float(w1, float(d), K=int(4 / float(d)))
        print("R1 %s = %.7f: Gamma((w',1)) float %.5f, Gamma(s w*) = %.5f" % (lab, float(d), gfib, gfib / float(s * k)))
        E1 = min_E1(d, 4)
        # the smallest N for the tail and 1 <= 6.28 d (N+1), at the claim 1.002 * float
        claim = F(math.ceil(gfib * 1.002 * 10000), 10000)
        g = gamma / k
        N = 1
        while not (1 <= F(628, 100) * d * (N + 1) and (N + 1) * E1 ** (N + 1) <= claim * (F(628, 100) * g)):
            N += 1
        ok = fibCheck(box[0][0] / k, box[0][1] / k, g, d, N, E1, claim, why=True)
        G = F(math.ceil(float(claim / (s * k)) * 10000 + 1), 10000)
        print("   witness N = %d, E1 = %s, claim = %s: %s; G = %s, gamOk %s" % (N, E1, claim, ok, G, gamOk(box, k, gamma, s, d, G, N, E1, claim)))
