#!/usr/bin/env python3
"""Lever L2, kernel-cheap form (SHARP-L2B): the fibered bound of the small-divisor series.

For omega = (omega', 1), Lean's KAM.smallDivisorSum_snoc_le_fiber gives
    S(omega, delta) <= e^{-b} pi^2/3 + sum_{0 < |k'|_1 <= N} ( e^{-b(|k'|_1 + |p|)} / L^2
                       + e^{-b|k'|_1} ([p != 0] / L0^2 + e^{-b} C0) ) + T_N,
with b = 2 pi delta, p = p(k') an integer with |k'.omega' + p| <= 1/2, 0 < L <= |k'.omega' + p|,
0 < L0 <= |k'.omega'| (if p != 0),
C0 = 4 + pi^2/3 (KAM.fiberConst) and T_N = KAM.sdTail gamma tau delta N (needs 2 tau < b(N + 1)).
Here p is the nearest integer and L = |k'.omega' + p| (double precision; a certificate would use a
rational lower bound).  The data box has #{0 < |k'|_1 <= N} entries in Z^{n-1} (2N for n = 2,
2N(N+1) for n = 3) instead of #{0 < |k|_1 <= N} in Z^n.

For each case and delta = delta_0 2^-j this prints: the exact S (enclosure of smalldiv_sum.py), the
limit B_inf of the fibered bound (N large) and its overhead over S, the smallest N with
B(N) <= 1.01 S, the number of data entries, and the effective constant
c_R(delta) = (2 pi)^-1 2^{n/2} sqrt(B(N)) gamma delta^tau; then the R1 threshold in the constant
model of thresholds.py with c_R = the largest c_R(delta) of the table.

Usage: python3 -I scripts/apost_sharp/smalldiv_fiber.py
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
C0 = 4 + math.pi ** 2 / 3


def fiber_terms(omega_p, delta, N):
    """Per-entry terms of the fibered box (sorted by |k'|_1) for omega = (omega', 1)."""
    b = 2 * math.pi * delta
    kp = sds.l1_ball(len(omega_p), N)
    size = np.abs(kp).sum(axis=1)
    keep = size > 0
    kp, size = kp[keep], size[keep]
    x = kp @ np.array(omega_p)
    p = -np.rint(x)
    d = np.abs(x + p)
    res = np.exp(-b * (size + np.abs(p))) / d ** 2
    # the term j = 0 (if p != 0) with its weight, and the rest (|j| >= 1) with e^{-b} C0
    bg = np.exp(-b * size) * (np.where(p != 0, 1 / x ** 2, 0.0) + math.exp(-b) * C0)
    order = np.argsort(size, kind="stable")
    return size[order], res[order], bg[order]


def fibered_bound(omega_p, gamma, tau, delta, N, terms=None):
    size, res, bg = terms if terms is not None else fiber_terms(omega_p, delta, N)
    m = size <= N
    b = 2 * math.pi * delta
    return math.exp(-b) * math.pi ** 2 / 3 + float(res[m].sum() + bg[m].sum()) + \
        sds.sd_tail(gamma, tau, delta, N)


def entries(n1, N):
    return 2 * N if n1 == 1 else 2 * N * (N + 1)


def l1_count(dim, N):
    """#{k in Z^dim : |k|_1 <= N} (dim = 2, 3)."""
    return 2 * N * (N + 1) + 1 if dim == 2 else (2 * N + 1) * (2 * N * N + 2 * N + 3) // 3


def sd_tail_vec(gamma, tau, delta, N):
    """KAM.sdTail for an array of cut-offs N (inf where 2 tau >= b (N + 1))."""
    b = 2 * math.pi * delta
    N = np.asarray(N, dtype=float)
    c = b - 2 * tau / (N + 1)
    C = 2 * (1 + 2 ** tau) / gamma ** 2
    with np.errstate(divide="ignore", invalid="ignore"):
        t = C * (-math.expm1(-b)) * (N + 1) ** (2 * tau) * np.exp(-b * (N + 1)) / (-np.expm1(-c))
    return np.where(c > 0, t, np.inf)


def report(name, omega_p, gamma, tau, delta0, js):
    n = len(omega_p) + 1
    cR = sds.cohConstR(n, tau)
    print(f"\n## {name}: n = {n}, tau = {tau}, gamma = {gamma:.6g}, delta_0 = {delta0:.6g}, "
          f"cohConstR {n} {tau} = {cR:.5f}")
    print("| delta | S (exact, enclosure) | B_inf / S - 1 | N (1 %) | entries | full box (L2) | "
          "c_R(delta) | cohConstR / c_R |")
    print("|---|---|---:|---:|---:|---:|---:|---:|")
    out = []
    for j in js:
        d = delta0 / 2 ** j
        b = 2 * math.pi * d
        lo, hi, _ = sds.S_enclosure(omega_p + [1.0], gamma, tau, d)
        Nmax = max(int(math.ceil(45 / b)), int(math.ceil(2 * tau / b)) + 2)
        terms = fiber_terms(omega_p, d, Nmax)
        Binf = fibered_bound(omega_p, gamma, tau, d, Nmax, terms)
        # B(N) for every cut-off N <= Nmax at once (entries sorted by |k'|_1)
        size, res, bg = terms
        cum = np.concatenate([[0.0], np.cumsum(res + bg)])
        Ns = np.arange(1, Nmax + 1)
        Bs = math.exp(-b) * math.pi ** 2 / 3 + cum[np.searchsorted(size, Ns, side="right")] + \
            sd_tail_vec(gamma, tau, d, Ns)
        ok = np.nonzero(Bs <= 1.01 * lo)[0]
        N = int(Ns[ok[0]]) if ok.size else None
        # if 1 % of S is out of reach, the cut-off within 1 % of the bound's own limit
        ok2 = np.nonzero(Bs <= 1.01 * Binf)[0]
        N2 = int(Ns[ok2[0]])
        if N is None:
            N, B = N2, float(Bs[ok2[0]])
        else:
            B = float(Bs[ok[0]])
        ceff = math.sqrt(2 ** n * B) * gamma * d ** tau / (2 * math.pi)
        # the full box of the L2 certificate, for comparison (#{0 < |k|_1 <= N} in Z^n)
        full = l1_count(n, N) - 1 if N else None
        out.append((j, d, lo, hi, Binf, N, B, ceff))
        star = "" if B <= 1.01 * lo else "*"
        print(f"| delta_0/2^{j} = {d:.4g} | [{lo:.6g}, {hi:.6g}] | {Binf / lo - 1:.2%} | {N}{star} | "
              f"{entries(n - 1, N) if N else '-'} | {full} | {ceff:.4g} | {cR / ceff:.1f} |")
    worst = max(r[7] for r in out)
    print(f"largest c_R over the table: {worst:.5f} (cohConstR / it = {cR / worst:.1f}); "
          "* = 1 % of S out of reach, N within 1 % of the bound's limit B_inf")
    return worst


def r1_threshold(cR_val):
    thr = load("thresholds")
    from fractions import Fraction as F
    p, gamma = thr.package_R1()
    sep = dict(M=p["M"], sK=p["sK"], sB=p["sB"], sT=p["sT"])
    base = dict(n=2, tau=1, mu=p["mu"], rho=p["rho"], rhoinf=p["rhoinf"], gbar=p["gbar"])
    rows = []
    for label, cR in [("cohConstR 2 1", thr.cohConstR_lean(2, 1)),
                      (f"fibered L2, c_R = {cR_val:.5f} (rounded up)",
                       F(math.ceil(cR_val * 1e5), 10 ** 5))]:
        for iso in (False, True):
            k = thr.sharp(nu=p["nu"], iso=iso, kappa=1, cR=cR, **base, **sep)
            t = thr.threshold(k, gamma)
            rows.append((label, "iso" if iso else "fixed", float(thr.lg(t)), k["active"]))
    print("\n## R1 threshold (thresholds.py constant model)")
    print("| c_R | form | log10 threshold | active branch |")
    print("|---|---|---:|---|")
    for label, form, lgt, act in rows:
        print(f"| {label} | {form} | {lgt:.2f} | {act} |")


def main():
    g = (math.sqrt(5) - 1) / 2
    alpha = 1 / (40 + g)
    rho = 1 / 70
    worst = report("lunar R1, omega = (nu - 1, 1)", [alpha], 1 / 42, 1, (rho - rho / 1000) / 6,
                   range(0, 7))
    c2 = 2 ** (1 / 3)
    report("toy T3, omega = (cbrt 2, cbrt 4, 1)", [c2, c2 ** 2], 1 / 12, 2, 1.0, range(0, 8))
    r1_threshold(worst)


if __name__ == "__main__":
    main()
