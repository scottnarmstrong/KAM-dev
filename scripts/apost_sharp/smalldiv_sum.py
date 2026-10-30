#!/usr/bin/env python3
"""Lever L2: the small-divisor series S(omega, delta) = sum_{k != 0} |k.omega|^-2 exp(-2 pi delta |k|_1)
and the effective constant of the frequency-specific cohomological estimate (SHARP-L2).

The Lean theorem KAM.cohomological_sum bounds the cohomological solution by
    (2 pi)^-1 2^{n/2} S(omega, delta)^{1/2} A,
so for a given (gamma, tau)-Diophantine omega its effective Russmann constant at the loss delta is
    c_R(delta) = (2 pi)^-1 2^{n/2} S(omega, delta)^{1/2} gamma delta^tau,
which is <= cohConstR n tau for every delta (KAM.cohConstSum_le_russmann). c_R(delta) is invariant
under omega -> lambda omega, gamma -> lambda gamma.

S is enclosed rigorously up to floating point (all terms are positive, last frequency component = 1):
  lower = sum over |k'|_1 <= K (k' = first n-1 components) and |k_n + round(k'.omega')| <= W;
  upper = lower + T_K (Lean's KAM.sdTail, for |k|_1 > K)
                + (W - 1/2)^-2 ((1 + e^-b)/(1 - e^-b))^n   (the window complement, |k.omega| >= W - 1/2).
The certificate of KAM.smallDivisorSum_le_box_add_tail, S <= F_N + T_N, is also evaluated at delta_0
(F_N with the exact |k.omega|): it reports the cut-off N with T_N <= 10^-3 F_N and the box size.

Usage: python3 -I scripts/apost_sharp/smalldiv_sum.py
"""
import math

import numpy as np


def cohConstR(n, tau):
    """KAM.cohConstR n tau = (2 pi)^-1 sqrt(2^n 6 (1 + 2^tau) (2 tau/(e pi))^{2 tau})."""
    return math.sqrt(2 ** n * 6 * (1 + 2 ** tau) * (2 * tau / (math.e * math.pi)) ** (2 * tau)) / (2 * math.pi)


def sd_tail(gamma, tau, delta, N):
    """KAM.sdTail gamma tau delta N (requires 2 tau < 2 pi delta (N + 1))."""
    b = 2 * math.pi * delta
    c = b - 2 * tau / (N + 1)
    assert c > 0
    C = 2 * (1 + 2 ** tau) / gamma ** 2
    return C * (-math.expm1(-b)) * (N + 1) ** (2 * tau) * math.exp(-b * (N + 1)) / (-math.expm1(-c))


def l1_ball(m, K):
    """All integer vectors of dimension m with |k|_1 <= K, as an (P, m) array."""
    if m == 1:
        return np.arange(-K, K + 1).reshape(-1, 1)
    rows = []
    for k1 in range(-K, K + 1):
        sub = l1_ball(m - 1, K - abs(k1))
        rows.append(np.hstack([np.full((sub.shape[0], 1), k1), sub]))
    return np.vstack(rows)


def window_sum(omega, delta, K, W, chunk=200000):
    """Sum of the terms with |k'|_1 <= K and |k_n + round(k'.omega')| <= W (omega[-1] == 1)."""
    n = len(omega)
    assert omega[-1] == 1.0
    b = 2 * math.pi * delta
    kp = l1_ball(n - 1, K)
    w = np.array(omega[:-1])
    j = np.arange(-W, W + 1)
    total = 0.0
    for s in range(0, kp.shape[0], chunk):
        block = kp[s:s + chunk]
        x = block @ w                                   # k'.omega'
        kn = -np.rint(x)[:, None] + j[None, :]          # last components in the window
        dot = x[:, None] + kn
        size = np.abs(block).sum(axis=1)[:, None] + np.abs(kn)
        with np.errstate(divide="ignore"):
            t = np.exp(-b * size) / dot ** 2
        t[(size == 0)] = 0.0                            # k = 0
        total += float(t.sum())
    return total


def S_enclosure(omega, gamma, tau, delta, W=10, bK=40.0):
    n = len(omega)
    b = 2 * math.pi * delta
    K = max(int(math.ceil(bK / b)), int(math.ceil(2 * tau / b)) + 1)
    lo = window_sum(omega, delta, K, W)
    far = (W - 0.5) ** -2 * ((1 + math.exp(-b)) / (-math.expm1(-b))) ** n
    hi = lo + sd_tail(gamma, tau, delta, K) + far
    return lo, hi, K


def box_sum(omega, delta, N, chunk=500):
    """F_N = sum_{0 < |k|_1 <= N} |k.omega|^-2 e^{-2 pi delta |k|_1} (exact |k.omega|)."""
    n = len(omega)
    b = 2 * math.pi * delta
    kp = l1_ball(n - 1, N)
    w = np.array(omega[:-1])
    total = 0.0
    count = 0
    for s in range(0, kp.shape[0], chunk):
        block = kp[s:s + chunk]
        x = block @ w
        r = N - np.abs(block).sum(axis=1)               # remaining l1 budget for the last component
        L = int(r.max())
        j = np.arange(-L, L + 1)
        mask = np.abs(j)[None, :] <= r[:, None]
        dot = x[:, None] + j[None, :]
        size = np.abs(block).sum(axis=1)[:, None] + np.abs(j)[None, :]
        with np.errstate(divide="ignore"):
            t = np.exp(-b * size) / dot ** 2
        t[~mask | (size == 0)] = 0.0
        total += float(t.sum())
        count += int(mask.sum()) - int(((size == 0) & mask).sum())
    return total, count


def report(name, omega, gamma, tau, delta0, js, cert=True):
    n = len(omega)
    cR = cohConstR(n, tau)
    print(f"\n## {name}: n = {n}, tau = {tau}, gamma = {gamma:.6g}, delta_0 = {delta0:.6g}, "
          f"cohConstR {n} {tau} = {cR:.5f}")
    print("| delta | S lower | S upper | c_R(delta) (upper) | cohConstR / c_R(delta) | K |")
    print("|---|---:|---:|---:|---:|---:|")
    rows = []
    for jj in js:
        d = delta0 / 2 ** jj
        lo, hi, K = S_enclosure(omega, gamma, tau, d)
        ceff = math.sqrt(2 ** n * hi) * gamma * d ** tau / (2 * math.pi)
        rows.append((jj, d, lo, hi, ceff))
        print(f"| delta_0/2^{jj} = {d:.4g} | {lo:.6g} | {hi:.6g} | {ceff:.4g} | {cR / ceff:.1f} | {K} |")
    sup = max(r[4] for r in rows)
    print(f"max over the listed delta: c_R = {sup:.4g} (cohConstR / max = {cR / sup:.1f})")
    if cert:
        b = 2 * math.pi * delta0
        lo, hi, _ = S_enclosure(omega, gamma, tau, delta0)
        N = int(math.ceil(2 * tau / b))
        while sd_tail(gamma, tau, delta0, N) > 1e-3 * lo:
            N = int(N * 1.1) + 1
        F, cnt = box_sum(omega, delta0, N)
        T = sd_tail(gamma, tau, delta0, N)
        print(f"certificate at delta_0 (KAM.smallDivisorSum_le_box_add_tail): N = {N}, box size {cnt}, "
              f"F_N = {F:.6g}, T_N = {T:.3g}, F_N + T_N = {F + T:.6g} (S in [{lo:.6g}, {hi:.6g}])")
    return rows


def main():
    # lunar: (psi, phi)-frame omega' = (nu - 1, 1), nu = 1 + 1/(40 + g), g = (sqrt 5 - 1)/2;
    # |a nu + b| >= 1/(21(|a| + |b|)) gives (1/42, 1)-Diophantine (QuadraticDiophantine.lean);
    # package R1: rho = 1/70, rho_inf = rho/1000, delta_0 = (rho - rho_inf)/6.
    g = (math.sqrt(5) - 1) / 2
    alpha = 1 / (40 + g)
    rho = 1 / 70
    report("lunar R1, omega' = (nu - 1, 1)", [alpha, 1.0], 1 / 42, 1, (rho - rho / 1000) / 6,
           range(0, 11))
    # toy T3: omega = s omega*, omega* = (cbrt 2/2, cbrt 4/2, 1/2), s = 2, gamma = 1/12, tau = 2,
    # rho = 9, rho_inf = 1, delta_0 = min(1, 8/6) = 1.
    c2 = 2 ** (1 / 3)
    report("toy T3, omega = 2 (cbrt 2/2, cbrt 4/2, 1/2) = (cbrt 2, cbrt 4, 1)", [c2, c2 ** 2, 1.0],
           1 / 12, 2, 1.0, range(0, 8))


if __name__ == "__main__":
    main()
