#!/usr/bin/env python3
"""SHARP-CERTSIDE: certified Diophantine constants and frequency-specific small-divisor sums.

Untrusted design tooling (numbers for docs/campaign/design/CERTIFIER-SHARPNESS.md, not a certificate).

1. Exact Diophantine infimum for a quadratic irrational frequency omega = (alpha, 1) (tau = 1, |k|_1 as in the
   frozen `IsDiophantine`):  gamma*(omega) = inf_{k != 0} |k|_1 |k1 alpha + k2|.  Certified (kernel-style) by
   (a) a finite enumeration |k1| < K0 (only the two integers k2 nearest to -k1 alpha matter), and
   (b) the algebraic tail: with alpha a root of A x^2 + B x + C (integers, discriminant > 0) and alpha' its
       conjugate, |k1 alpha + k2| |k1 alpha' + k2| = |A k2^2 - B k1 k2 + C k1^2| / |A| >= 1/|A|, hence
       x := |k1 alpha + k2| < g/|k|_1 implies  x >= 1/(|A| (g/|k1| + |k1| |alpha - alpha'|)), and
       |k|_1 x >= (|k1|(1 + |alpha|) - x) / (|A| (g/|k1| + |k1| Delta))  >= g  for |k1| >= K0.
   The value certified is min_{|k1| < K0} (lower bound of |k|_1 |k1 alpha + k2|), i.e. the true infimum up to the
   enclosure of alpha.  Also: the transfer to the rotated frame and the current proved values.
2. S(omega, delta) = sum_{k != 0} |k.omega|^-2 e^{-2 pi delta |k|_1} (n = 2): a finite part over |k1| <= K plus
   a tail.  For fixed k1 the l-sum is bounded in closed form (shifted lattice), so the certified bound costs O(K)
   rational operations.  Compared with the generic Diophantine bound gamma^-2 sum |k|^{2 tau} e^{-2 pi delta |k|}
   and with the cohomological constants of the sharp theorem (Russmann c_R gamma^-1 delta^-tau).
   The frequency-specific cohomological constant (Parseval on the 2^n distinguished tori, Cauchy-Schwarz):
        ||u||_{r - delta} <= Gamma_spec(delta) ||g||_r,   Gamma_spec(delta) = (2 pi)^-1 2^{n/2} S(omega, 2 delta)^{1/2}.

Usage: python3 -I scripts/certifier/smalldiv.py [--json OUT]
"""
import sys, math, json
import mpmath as mp

mp.mp.dps = 50
TP = 2 * mp.pi


# ------------------------------------------------------------------------------------------------ frequencies
def lunar_alpha(which, frame):
    """alpha with omega = (alpha, 1): theta frame alpha = nu, rotated frame alpha = nu - 1; and its minimal
    polynomial (A, B, C) with A alpha^2 + B alpha + C = 0."""
    a = (79 - mp.sqrt(5)) / 3118                     # 1/(40 + g)
    nu = 1 - a if which == "lower" else 1 + a
    # nu_-: 1559 x^2 - 3039 x + 1481 = 0 ; nu_+: 1559 x^2 - 3197 x + 1639 = 0 (KAM/Certificate/QuadraticDiophantine)
    P = (1559, -3039, 1481) if which == "lower" else (1559, -3197, 1639)
    if frame == "theta":
        return nu, P
    # alpha = nu - 1: substitute x = y + 1
    A, B, C = P
    return nu - 1, (A, 2 * A + B, A + B + C)


def conj(alpha, P):
    A, B, C = P
    d = mp.sqrt(B * B - 4 * A * C)
    r1, r2 = (-B + d) / (2 * A), (-B - d) / (2 * A)
    return r2 if abs(r1 - alpha) < abs(r2 - alpha) else r1


def dioph_inf(alpha, P, K0=None):
    """(gamma*, argmin k, K0 used, tail bound at K0): exact infimum of |k|_1 |k1 alpha + k2| for tau = 1."""
    A = abs(P[0]); Delta = abs(alpha - conj(alpha, P))
    best = (mp.inf, None)
    # enumerate k1 = 0 (|k2| >= 1 gives |k|_1 |k2| >= 1) and 1 <= k1 < K0 (k -> -k symmetry)
    K0 = K0 or 2000
    for k1 in range(1, K0):
        x = k1 * alpha
        for k2 in (int(mp.floor(-x)), int(mp.ceil(-x))):
            v = (k1 + abs(k2)) * abs(x + k2)
            if v < best[0]:
                best = (v, (k1, k2))
    g = best[0]
    # tail certificate at K0: |k|_1 x >= (K0 (1 + |alpha|) - g/K0) / (A (g/K0 + K0 Delta)), increasing in K0
    tail = (K0 * (1 + abs(alpha)) - g / K0) / (A * (g / K0 + K0 * Delta))
    tail_inf = (1 + abs(alpha)) / (A * Delta)
    return dict(gamma=g, argmin=best[1], K0=K0, tail_at_K0=tail, tail_limit=tail_inf,
                certified=bool(tail >= g), A=A, Delta=Delta)


# ------------------------------------------------------------------------------------------------ S(omega, delta)
def S_bound(alpha, delta, K=None, gstar=None):
    """Upper bound of S(omega, delta) for omega = (alpha, 1):  sum_{k != 0} |k.omega|^-2 e^{-2 pi delta |k|_1}.
    Row k1 = 0 exactly (2 Li_2(q)); rows 1 <= |k1| <= K: the l-sum  sum_l q^{|k1| + |l|} / (k1 alpha + l)^2  exactly
    for |l - l0| <= 60 (l0 = floor(-k1 alpha)) plus 2 q^{|k1|} sum_{j > 60} j^-2 <= 2 q^{|k1|}/60 beyond (there
    |k1 alpha + l| >= j - 1 and q^|l| <= 1); rows |k1| > K by the Diophantine tail
    sum_{m > K} 4 m (m/gamma*)^2 q^m (|k.omega| >= gamma*/|k|_1)."""
    K = K or int(mp.ceil(40 / (TP * delta)))           # e^{-2 pi delta K} <= e^-40
    q = mp.e ** (-TP * delta)
    tot = 2 * mp.polylog(2, q)
    for k1 in range(1, K + 1):
        x = k1 * alpha
        l0 = int(mp.floor(-x))
        row = mp.mpf(0)
        for l in range(l0 - 60, l0 + 62):
            row += q ** (abs(l)) / (x + l) ** 2
        row += 2 / mp.mpf(60)
        tot += 2 * q ** k1 * row                        # k1 and -k1 (symmetry k -> -k)
    gstar = gstar or mp.mpf(1) / 100
    tot += mp.nsum(lambda m: 4 * m ** 3 * q ** m, [K + 1, mp.inf]) / gstar ** 2
    return tot, K


def S_generic(gamma, tau, delta, scale=1):
    """gamma^-2 sum_{k != 0} |k|_1^{2 tau} e^{-2 pi delta |k|_1}, n = 2 (#{|k|_1 = m} = 4 m)."""
    q = mp.e ** (-TP * delta)
    s = mp.nsum(lambda m: 4 * m * m ** (2 * tau) * q ** m, [1, mp.inf])
    return s / (gamma * scale) ** 2


def cohConstR(n, tau):
    """KAM.cohConstR n tau (KAM/Strip/CohomologicalRussmannLattice.lean)."""
    t = mp.mpf(tau)
    return (2 * mp.pi) ** -1 * mp.sqrt(2 ** n * 6 * (1 + 2 ** t) * (2 * t / (mp.e * mp.pi)) ** (2 * t))


def cohConstP(n, tau):
    t = mp.mpf(tau)
    return (2 * mp.pi) ** -1 * mp.sqrt(2 ** n * (2 * t / (mp.e * mp.pi)) ** (2 * t) * (8 * mp.mpf(n) / mp.pi) ** n)


def gamma_spec(alpha, delta, n=2, gstar=None):
    """(2 pi)^-1 2^{n/2} S(omega, 2 delta)^{1/2} (omega = (alpha, 1), unscaled)."""
    S, K = S_bound(alpha, 2 * delta, gstar=gstar)
    return (2 * mp.pi) ** -1 * mp.mpf(2) ** (mp.mpf(n) / 2) * mp.sqrt(S), S, K


def main():
    out = {"dioph": {}, "S": {}}
    print("== exact Diophantine infima (tau = 1, |k|_1), proved values in KAM/Certificate")
    proved = {"theta": mp.mpf(1) / 21, "rot": mp.mpf(1) / 42}
    for which in ("lower", "upper"):
        for frame in ("theta", "rot"):
            alpha, P = lunar_alpha(which, frame)
            r = dioph_inf(alpha, P, K0=4000)
            gp = proved[frame]
            gain4 = 4 * mp.log10(r["gamma"] / gp)
            print("%s %-5s alpha %.8f  gamma* %.8f at k=%s  proved %.6f  ratio %.4f (gamma^4: %+.3f orders)  "
                  "tail(K0=%d) %.3f >= gamma*: %s  (limit (1+|a|)/(A Delta) = %.3f)" % (
                      which, frame, float(alpha), float(r["gamma"]), r["argmin"], float(gp), float(r["gamma"] / gp),
                      float(gain4), r["K0"], float(r["tail_at_K0"]), r["certified"], float(r["tail_limit"])))
            # smallest K0 that certifies
            K0 = 2
            while not dioph_inf(alpha, P, K0=K0)["certified"]:
                K0 *= 2
            out["dioph"]["%s/%s" % (which, frame)] = dict(alpha=float(alpha), gamma=float(r["gamma"]),
                                                          argmin=r["argmin"], proved=float(gp),
                                                          gain_orders_gamma4=float(gain4), K0_needed=K0)
            print("     certified with K0 = %d (enumeration of %d rows)" % (K0, K0))
    print()
    print("== frequency-specific cohomological constant vs Russmann / Parseval (rotated frame, unscaled omega')")
    print("   Gamma(delta) bounds ||u||_{r-delta}/||g||_r;  ratio = Gamma_R / Gamma_spec")
    for which in ("lower", "upper"):
        alpha, P = lunar_alpha(which, "rot")
        gam = mp.mpf(1) / 42                            # proved (transfer)
        gstar = dioph_inf(alpha, P, K0=200)["gamma"]
        for delta in (mp.mpf("0.0005"), mp.mpf("0.001"), mp.mpf("0.0024"), mp.mpf("0.005"), mp.mpf("0.01"),
                      mp.mpf("0.02")):
            Gs, S, K = gamma_spec(alpha, delta, gstar=gstar)
            GR = cohConstR(2, 1) / (gam * delta)
            GRs = cohConstR(2, 1) / (gstar * delta)
            GP = cohConstP(2, 1) / (gam * delta ** 2)
            Sg = S_generic(gstar, 1, 2 * delta)
            GPopt = (2 * mp.pi) ** -1 * 2 * mp.sqrt(Sg)
            print("%s delta %.4f: S(w,2d) %.4e (K=%d)  Gamma_spec %.4e | Russmann(1/42) %.4e ratio %.2f "
                  "(4 log10: %.2f) | Russmann(gamma*) ratio %.2f | Parseval-generic(gamma*) %.4e ratio %.2f" % (
                      which, float(delta), float(S), K, float(Gs), float(GR), float(GR / Gs),
                      float(4 * mp.log10(GR / Gs)), float(GRs / Gs), float(GPopt), float(GPopt / Gs)))
            out["S"]["%s/%s" % (which, float(delta))] = dict(S=float(S), K=K, Gamma_spec=float(Gs),
                                                             Gamma_R=float(GR), Gamma_R_gstar=float(GRs),
                                                             Gamma_P_generic=float(GPopt))
    if "--json" in sys.argv:
        json.dump(out, open(sys.argv[sys.argv.index("--json") + 1], "w"), indent=1, default=str)


if __name__ == "__main__":
    main()
