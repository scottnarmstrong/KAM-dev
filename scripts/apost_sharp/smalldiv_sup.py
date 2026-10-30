#!/usr/bin/env python3
"""Lever L9 (SHARP-L9): the sup-over-modes constant of the weighted l1 cohomological estimate.

In weighted l1 coefficient norms (Lean: KAM.cohomological_l1) the solution of the cohomological
equation satisfies
    ||u||_{l1, 2 pi (rho - delta)} <= Gamma_inf(omega, delta) ||g||_{l1, 2 pi rho},  with
    Gamma_inf(omega, delta) = sup_{k != 0} e^{-2 pi delta |k|_1} / (2 pi |k.omega|)
(KAM.smallDivisorSup).  The effective constant is c_inf(delta) = Gamma_inf gamma delta^tau,
to compare with
  * cohConstR 2 1 = 0.316 (Russmann, sup norms),
  * c_R = (2 pi)^-1 2^{n/2} S(omega, delta)^{1/2} gamma delta^tau (SHARP-L2, sup norms; 0.0058
    for the lunar frequency),
  * the generic l1 bound (2 pi)^-1 (tau / (2 pi e))^tau = 1/(4 pi^2 e) = 0.0093 at tau = 1
    (KAM.smallDivisorSup_le_solveBound; PlasmaLean's ||u||_{r-delta} <= ||f||_r / (e gamma delta)),
  * the L2 route (2 pi)^-1 S(omega, 2 delta)^{1/2} gamma delta^tau
    (KAM.smallDivisorSup_le_sqrt_sum).

For omega = (omega', 1) with omega' = (alpha) the supremum is computed fiber by fiber
(KAM.smallDivisorSup_snoc_le): in the fiber k' the nearest k_n = p(k') = -round(k' alpha) gives the
only small divisor, the other k_n give at most e^{-b|k'|}/pi, the fiber k' = 0 gives e^{-b}/(2 pi),
and |k'|_1 > N is bounded by KAM.sdSupTail = (N+1)^tau e^{-b(N+1)} / (2 pi gamma) once
tau <= b (N+1).  The certificate column is the smallest N whose tail is below Gamma_inf (so that the
certified bound max(B, tail) equals Gamma_inf up to the rounding of the data), with its number of
entries 2N (k' in +-[1, N]).

Units of PlasmaLean (angles in radians, strip r = 0.1257 rad, delta_0 = r/7): our turns are
radians / (2 pi), so rho = 0.02 turns and delta = delta_0 / (2 pi); its constant
sup_k e^{-delta_rad |k|} / |k.omega| is 2 pi Gamma_inf, and c_inf is invariant.

Double precision; not Lean-certified (the Lean route is KAM.smallDivisorSup_snoc_le with rational
data).

Usage: python3 -I scripts/apost_sharp/smalldiv_sup.py
"""
import importlib.util
import math
import pathlib

import numpy as np

HERE = pathlib.Path(__file__).resolve().parent


def load(name):
    spec = importlib.util.spec_from_file_location(name, HERE / f"{name}.py")
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


sds = load("smalldiv_sum")
C_GENERIC = 1 / (4 * math.pi ** 2 * math.e)


def sup_tail(gamma, tau, delta, N):
    """KAM.sdSupTail gamma tau delta N (inf if tau > b (N + 1))."""
    b = 2 * math.pi * delta
    if tau > b * (N + 1):
        return math.inf
    return (N + 1) ** tau * math.exp(-b * (N + 1)) / (2 * math.pi * gamma)


def gamma_inf(alpha, gamma, tau, delta):
    """Gamma_inf((alpha, 1), delta) by fibers, the maximizing mode, and the certificate cut-off.

    Returns (Gamma, (k1, k2), N_cert, B(N_cert), tail(N_cert))."""
    b = 2 * math.pi * delta
    # fibers up to K, with K so large that the tail is negligible
    K = int(math.ceil(60 / b)) + 10
    k1 = np.arange(1, K + 1, dtype=np.float64)
    x = k1 * alpha
    p = -np.rint(x)
    d = np.abs(x + p)
    near = np.exp(-b * (k1 + np.abs(p))) / (2 * math.pi * d)
    # second nearest k_n in each fiber (exact), and the fiber k' = 0
    p2 = p - np.sign(x + p)
    p2 = np.where(p2 == p, p - 1, p2)
    far = np.exp(-b * (k1 + np.abs(p2))) / (2 * math.pi * np.abs(x + p2))
    zero = math.exp(-b) / (2 * math.pi)
    i = int(np.argmax(near))
    G = max(float(near[i]), float(far.max()), zero)
    assert sup_tail(gamma, tau, delta, K) < 1e-6 * G
    arg = (int(k1[i]), int(p[i]))
    # the certificate: smallest N with tau <= b (N + 1) and tail(N) <= Gamma
    pref = np.maximum.accumulate(np.maximum(near, np.exp(-b * k1) / math.pi))
    N = max(int(math.ceil(tau / b)) - 1, 1)
    while sup_tail(gamma, tau, delta, N) > G:
        N += 1
    B = max(float(pref[N - 1]), zero)
    return G, arg, N, B, sup_tail(gamma, tau, delta, N)


def best_gamma(alpha, tau, K=200000):
    """min_{k != 0} |k.omega| |k|_1^tau over 0 < |k1| <= K (nearest k2 in each fiber)."""
    k1 = np.arange(1, K + 1, dtype=np.float64)
    x = k1 * alpha
    p = -np.rint(x)
    return float((np.abs(x + p) * (k1 + np.abs(p)) ** tau).min())


def report(name, alpha, gamma, tau, delta0, js, cR_L2=None, with_S=True):
    print(f"\n## {name}: omega = ({alpha:.12g}, 1), gamma = {gamma:.6g}, tau = {tau}, "
          f"delta_0 = {delta0:.6g} turns")
    print(f"best gamma of the frequency (|k|_1, tau = {tau}, |k1| <= 2e5): "
          f"{best_gamma(alpha, tau):.6g}")
    head = "| delta | Gamma_inf | argmax k | c_inf = Gamma gamma delta^tau | generic / c_inf | "
    if with_S:
        head += "L2 route (2pi)^-1 S(2 delta)^1/2 gamma delta^tau | "
    head += "N cert | entries | tail(N) / Gamma |"
    print(head)
    print("|---" * (head.count("|") - 1) + "|")
    out = []
    for j in js:
        d = delta0 / 2 ** j
        G, arg, N, B, T = gamma_inf(alpha, gamma, tau, d)
        c = G * gamma * d ** tau
        row = (f"| delta_0/2^{j} = {d:.4g} | {G:.6g} | {arg} | {c:.5f} | {C_GENERIC / c:.2f} | ")
        if with_S:
            lo, hi, _ = sds.S_enclosure([alpha, 1.0], gamma, tau, 2 * d)
            cS = math.sqrt(hi) * gamma * d ** tau / (2 * math.pi)
            row += f"{cS:.5f} | "
        row += f"{N} | {2 * N} | {T / G:.3f} |"
        # the certified bound max(B, tail) is Gamma_inf itself (B = the largest entry)
        assert abs(max(B, T) - G) <= 1e-9 * G
        print(row)
        out.append(c)
    worst = max(out)
    print(f"largest c_inf over the table: {worst:.5f}; cohConstR 2 1 / it = "
          f"{sds.cohConstR(2, tau) / worst:.1f}; generic 1/(4 pi^2 e) / it = "
          f"{C_GENERIC / worst:.2f}" + (f"; SHARP-L2 c_R / it = {cR_L2 / worst:.2f}"
                                       if cR_L2 else ""))
    return worst


def r1_threshold(c_inf):
    """Indicative only: the sup-norm constant model of thresholds.py with c_R := c_inf.

    The l1 scheme is not built, so this is what the constant would be worth if every other
    estimate of the scheme were carried over to weighted l1 norms unchanged."""
    thr = load("thresholds")
    from fractions import Fraction as F
    p, gamma = thr.package_R1()
    sep = dict(M=p["M"], sK=p["sK"], sB=p["sB"], sT=p["sT"])
    base = dict(n=2, tau=1, mu=p["mu"], rho=p["rho"], rhoinf=p["rhoinf"], gbar=p["gbar"])
    rows = []
    for label, cR in [("cohConstR 2 1", thr.cohConstR_lean(2, 1)),
                      ("SHARP-L2 c_R = 0.00583", F(583, 10 ** 5)),
                      ("generic l1 1/(4 pi^2 e) = 0.00932", F(932, 10 ** 5)),
                      (f"Gamma_inf c = {c_inf:.5f} (rounded up)",
                       F(math.ceil(c_inf * 1e5), 10 ** 5))]:
        for iso in (False, True):
            k = thr.sharp(nu=p["nu"], iso=iso, kappa=1, cR=cR, **base, **sep)
            t = thr.threshold(k, gamma)
            rows.append((label, "iso" if iso else "fixed", float(thr.lg(t)), k["active"]))
    print("\n## R1 threshold, indicative (thresholds.py sup-norm constant model, c_R := constant)")
    print("| constant | form | log10 threshold | active branch |")
    print("|---|---|---:|---|")
    for label, form, lgt, act in rows:
        print(f"| {label} | {form} | {lgt:.2f} | {act} |")


def main():
    g = (math.sqrt(5) - 1) / 2
    alpha = 1 / (40 + g)
    rho = 1 / 70
    worst = report("lunar R1, omega = (nu - 1, 1)", alpha, 1 / 42, 1, (rho - rho / 1000) / 6,
                   range(0, 7), cR_L2=0.00583)
    iota = (75 + math.sqrt(5)) / 562
    r_rad = 0.1257
    report("PlasmaLean, omega = (iota, 1)", iota, 0.0687, 1, r_rad / 7 / (2 * math.pi),
           range(0, 7))
    r1_threshold(worst)


if __name__ == "__main__":
    main()
