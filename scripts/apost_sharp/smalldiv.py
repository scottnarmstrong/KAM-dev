#!/usr/bin/env python3
"""Small-divisor constants for the v2 design (docs/campaign/design/APOST-SHARP-V2.md, blueprint p2s2-*).

Untrusted tooling (design numbers, not a certificate).  Convention: R solves d_omega u = g - <g> on the torus
R^n/Z^n with characters e^{2 pi i k.theta}; a constant c is admissible at the bite delta if
    sup_{T_{r-delta}} |R g| <= c gamma^{-1} delta^{-kappa} sup_{T_r} |g|     (max norm, componentwise).
The route of every bound below: Bessel on the 2^n corners of the FULL strip (r' -> r, a monotone limit),
Cauchy-Schwarz, and the small-divisor sum
    S(omega, delta) := sum_{k != 0} |k.omega|^{-2} e^{-4 pi delta |k|_1},
giving c(delta) = (2 pi)^{-1} gamma delta^tau 2^{n/2} S(omega, delta)^{1/2}.

* c_v1(n, tau)       = KAM.cohConstR (v1 data, bite r - delta/2 in Bessel, crude Abel): 0.31628 for (2, 1).
* c_classical(n,tau) = the classical constant of the full-strip route with ordered divisors (FHL17 (94)-(96) adapted
                       to flows) and exact Abel summation:
                         (2 pi)^{-1} 2^{n/2} (2^{2 tau+1} zeta(2, 2^tau) Gamma(2 tau+1))^{1/2} (4 pi)^{-tau} (1 + eps_tau(delta))^{1/2}
                       eps_tau(delta) = 4 pi delta (2 tau/e)^{2 tau}/Gamma(2 tau+1) (unimodal sum vs integral).
                       0.08137 (1 + 3.40 delta)^{1/2} for (2, 1); the uniform constant (delta <= 1) is 0.1707.
* c_freq(omega, gamma, delta) = the frequency-specific value: the exact finite part |k|_1 <= N plus the classical
                       tail (shell bound S_M <= A gamma^{-2} M^{2 tau}, A = 2^{2 tau+1} zeta(2, 2^tau), Abel summation).
"""
import math
import numpy as np

try:
    import mpmath as mp
    mp.mp.dps = 30
except ImportError:                                   # pragma: no cover
    mp = None


def hurwitz2(a):
    return float(mp.zeta(2, a))


def shell_const(tau):
    """A with sum_{0<|k|_1<=M} |k.omega|^{-2} <= A gamma^{-2} M^{2 tau} (ordered divisors: the positive values k.omega,
    |k|_1 <= M, are >= gamma M^{-tau} and pairwise >= gamma (2M)^{-tau} apart; pairs +-k)."""
    return 2 * 2 ** (2 * tau) * hurwitz2(2 ** tau)


def c_v1(n, tau):
    return float((2 * mp.pi) ** -1 * mp.sqrt(2 ** n * 6 * (1 + 2 ** mp.mpf(tau)) * (2 * mp.mpf(tau) / (mp.e * mp.pi)) ** (2 * tau)))


def c_classical(n, tau, delta=0.0):
    eps = 4 * math.pi * delta * (2 * tau / math.e) ** (2 * tau) / math.gamma(2 * tau + 1)
    return (2 * math.pi) ** -1 * 2 ** (n / 2) * math.sqrt(shell_const(tau) * math.gamma(2 * tau + 1) * (1 + eps)) \
        * (4 * math.pi) ** (-tau)


def S_finite(omega, delta, N):
    """sum_{0 < |k|_1 <= N} |k.omega|^{-2} e^{-4 pi delta |k|_1} for n = 2 (vectorised)."""
    k1 = np.arange(-N, N + 1)
    tot = 0.0
    for a in k1:
        m = N - abs(a)
        k2 = np.arange(-m, m + 1)
        K = abs(a) + np.abs(k2)
        dot = np.abs(a * omega[0] + k2 * omega[1])
        msk = K > 0
        tot += float((np.exp(-4 * math.pi * delta * K[msk]) / dot[msk] ** 2).sum())
    return tot


def S_tail(gamma, tau, delta, N, Mmax=None):
    """Classical tail sum_{|k|_1 > N}: (1 - e^{-b}) A gamma^{-2} sum_{M > N} M^{2 tau} e^{-b M}, b = 4 pi delta."""
    b = 4 * math.pi * delta
    A = shell_const(tau)
    Mmax = Mmax or int(N + 60 / b) + 10
    M = np.arange(N + 1, Mmax + 1, dtype=float)
    return (1 - math.exp(-b)) * A / gamma ** 2 * float((M ** (2 * tau) * np.exp(-b * M)).sum())


def c_freq(omega, gamma, tau, delta, n=2, N=None):
    """Frequency-specific constant at the bite delta (finite part + classical tail)."""
    N = N or max(50, int(16.0 / (4 * math.pi * delta)))
    S = S_finite(omega, delta, N) + S_tail(gamma, tau, delta, N)
    return (2 * math.pi) ** -1 * gamma * delta ** tau * 2 ** (n / 2) * math.sqrt(S), N


if __name__ == "__main__":
    print("c_v1(2,1) = %.5f, c_classical(2,1,0) = %.5f, c_classical(2,1,1) = %.5f" % (c_v1(2, 1), c_classical(2, 1),
          c_classical(2, 1, 1.0)))
    alpha = (79 - math.sqrt(5)) / 3118
    c = 7 / 4; s = 1 + 1e-6
    om = (c * (-alpha) / s, c / s)
    gam = c / (42 * s)
    rho = 1 / 70; d0 = (rho - rho / 1000) / 6
    for d in (rho, d0, d0 / 2, d0 / 4, d0 / 8):
        v, N = c_freq(om, gam, 1, d)
        print("delta = %.6g  c_freq = %.5f  (N = %d)" % (d, v, N))


def gamma_inf(omega, delta, gamma, tau=1, N=None):
    """L9: the l^1 (Wiener-algebra) small-divisor constant Gamma_inf(omega, delta) = sup_{k != 0} e^{-2 pi delta |k|_1}/(2 pi |k.omega|)
    (n = 2): exact on |k|_1 <= N, and for |k|_1 > N the Diophantine tail e^{-2 pi delta m} m^tau/(2 pi gamma), decreasing for
    m > tau/(2 pi delta).  Returns (Gamma_inf, c_inf = Gamma_inf gamma delta^tau)."""
    N = N or max(50, int(30.0 / (2 * math.pi * delta)))
    best = 0.0
    for a in range(-N, N + 1):
        m = N - abs(a)
        k2 = np.arange(-m, m + 1)
        K = abs(a) + np.abs(k2)
        dot = np.abs(a * omega[0] + k2 * omega[1])
        msk = K > 0
        v = np.exp(-2 * math.pi * delta * K[msk]) / (2 * math.pi * dot[msk])
        best = max(best, float(v.max()))
    M0 = max(N + 1, int(math.ceil(tau / (2 * math.pi * delta))))
    tail = math.exp(-2 * math.pi * delta * M0) * M0 ** tau / (2 * math.pi * gamma)
    G = max(best, tail)
    return G, G * gamma * delta ** tau


def c_inf_classical(tau):
    """The l^1 classical constant: sup_m m^tau e^{-2 pi delta m}/(2 pi gamma) <= (tau/(2 pi e delta))^tau/(2 pi gamma)."""
    return (tau / (2 * math.pi * math.e)) ** tau / (2 * math.pi)
