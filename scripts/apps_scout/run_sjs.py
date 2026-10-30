#!/usr/bin/env python3
"""Planar Sun-Jupiter-Saturn (Figueras-Haro, J. Nonlinear Sci. 35 (2025) 13, arXiv:2403.10152): what the KAM certifier would need.

All inputs are the paper's: n = 3, tau = 2.4 (we use the next integer our checker allows, tau = 3, and also tau = 2 for a cubic frequency vector), gamma = 1.69e-6,
rho = 0.1 in 2 pi angles, delta = rho/6; c_Xh = 0.09, c_DXh = 129, c_D2Xh = 5e10; |DK| = 4.78, |B| = 7.36, |<T>^-1| = 354; torus error 3.6e-54 (tangent) / 1.7e-57 (normal);
their thresholds 1e-38 / 1e-44; grid 1024^3 (1.07e9 complex coefficients per component, 6 components), one Newton step = one week, 194 GB RAM.

Conversion to our period-1 convention: angles theta_p1 = theta/2 pi, actions I_p1 = 2 pi I, H_p1 = 2 pi H (time unit 2 pi): rho_p1 = rho/2 pi, frequencies are unchanged in the
sense omega_p1 = omega (cycles per 2 pi units), gamma unchanged, |X_h| ~ 2 pi-free (angle rows) etc.  We keep M = max of their constants; this is the v1 hypothesis (a single M).
"""
import math
import sys
import os
from fractions import Fraction as F

import pipeline as pl
import thresholds_est as te
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "apost_sharp"))
import thresholds as TH


def main():
    gam = 1.69e-6
    rho = 0.1 / (2 * math.pi)
    sK, sB, sT = 4.7811815833, 7.35806411265, 354.07743243
    out = {}
    for label, M, M2 in (("one M = 5e10 (v1 hypotheses)", 5e10, 5e10), ("M = 129 + M2 = 5e10 (v2-type split)", 129.0, 5e10)):
        for tau, kappa in ((3, 3), (2, 2)):
            res = {}
            r = te.Q(rho, up=False)
            for name, cR in (("v1", TH.cohConstR_lean(3, tau)), ("v2 c_R=0.05", te.Q(0.05))):
                k = te.sharp_mod(3, tau, kappa, cR, te.Q(M), te.Q(sK), te.Q(sB), te.Q(sT), te.Q(1 / 160), r, r / 1000, te.Q(gam), nu=F(1, 10 ** 8), iso=False,
                                 HT=None if name == "v1" else te.Q(3e3), M2=te.Q(M2))
                res[name] = TH.lg(TH.threshold(k, te.Q(gam)))
            k0 = TH.current_fixed(n=3, tau=tau, M=te.Q(M), sK=te.Q(M), sB=te.Q(M), sT=te.Q(M), mu=te.Q(1 / 160), rho=r, rhoinf=r / 1000, gbar=te.Q(gam), cR=max(F(1), TH.cohConst_crude(3, tau)))
            res["current"] = TH.lg(TH.threshold(k0, te.Q(gam)))
            out["%s tau=%d" % (label, tau)] = res
            print(label, "tau", tau, {k: round(v, 1) for k, v in res.items()}, flush=True)
    # Fourier support: the paper's strips rho = (0.52, 0.42, 0.32) in 2 pi angles; a coefficient at |k|_1 modes in direction i decays as exp(-rho_i k_i)
    sup = {}
    a = [r / math.log(10) for r in (0.524, 0.417, 0.316)]  # digits per mode
    for L in (30, 54, 80, 120, 160):
        # octant simplex volume L^3 / (6 a1 a2 a3), times 8 for signs
        S = 8 * L ** 3 / (6 * a[0] * a[1] * a[2])
        K = [L / x for x in a]
        sup[L] = dict(S=S, box=8 * K[0] * K[1] * K[2], Kmax=K)
        print("L %d support %.2e box %.2e max modes %s" % (L, S, sup[L]["box"], [round(x) for x in K]), flush=True)
    out["support"] = sup
    import costmodel as cm
    # a v2-type theorem at L = 85, S = 1e8; N_full >= 100 (two Kepler charts: 2 x the PCR3BP count); box/support = 6 in three dimensions against 2 for the lunar unit
    p = cm.project(1e8, 85, 100, Nlow=500, box_factor=3.0)
    out["cost"] = dict(lunar_units=p["ratio"], cpuh_P=p["cpuh"]["P"], advice_MB=p["advice_MB"])
    print("cost: %.2e lunar units, %.1e-%.1e CPU-h, advice %.2e MB" % (p["ratio"], p["cpuh"]["P"][0], p["cpuh"]["P"][1], p["advice_MB"]), flush=True)
    out["paper"] = dict(N=1024 ** 3, components=6, coefficients=6 * 1024 ** 3, ram_GB=194, newton_step_days=7, eta_DK=3.6e-54, eta_N=1.7e-57, thr_DK=1e-38, thr_N=1e-44, gamma=gam, tau=2.4, rho=0.1)
    pl.save("sjs.json", out)


if __name__ == "__main__":
    main()
