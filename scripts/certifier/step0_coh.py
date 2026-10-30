#!/usr/bin/env python3
"""SHARP-CERTSIDE: actual size of the cohomological solution of the lunar residual vs the a-priori bounds.

Untrusted design tooling.  For the action rows g of the invariance error of the rotated candidate (rho = 1/70,
time scale c = 1, omega' = (nu - 1, 1)), the zero-average solution u of omega'.d u = g has coefficients
u_k = g_k / (2 pi i k.omega').  Compared on T_{rho - delta}, delta = delta0 = (rho - rho_inf)/6 (sharp schedule):
  measured  ||u||  (weighted l1 and corner bound of the exact coefficients)        [lever L6, step 0]
  Gamma_spec(delta) sup|g|   (frequency-specific constant, scripts/certifier/smalldiv.py)  [lever L2]
  c_R gamma^-1 delta^-1 sup|g| (Russmann data of the sharp theorem, gamma = 1/42)      [v1]
The step-0 right-hand sides of the theorem are frame matrices times E (low-degree multipliers), so this is the
order of magnitude of the gain of a measured step 0, not its exact value.
Usage: python3 -I scripts/certifier/step0_coh.py CACHE_DIR
"""
import sys, os, math
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from lunar_oracle import LunarOracle, Series, TP          # noqa: E402
from optimize import gamma_spec, CR_R                     # noqa: E402

rho = 1 / 70
d0 = (rho - rho / 1000) / 6
for which in ("lower", "upper"):
    O = LunarOracle(which, sys.argv[1] if len(sys.argv) > 1 else None, log=lambda *a: None)
    A = np.eye(2)
    for name, g in (("P1 row", O.R[0]), ("P2 row", O.R[1])):
        lam = O.om[0] * g.k + O.om[1] * g.l
        nz = np.abs(lam) > 0
        u = Series(g.k[nz], g.l[nz], g.c[nz] / (TP * 1j * lam[nz]))
        g_l1, g_cor = g.norms(A, rho)
        g_sup = 0.0
        for y in O._corners(A, rho):
            g_sup = max(g_sup, float(np.abs(g.grid(2048, 512, y)).max()))
        u_l1, u_cor = u.norms(A, rho - d0)
        Gs = gamma_spec(O.om, d0)
        GR = CR_R * 42 / d0
        print("%s %s: |g| sup %.3e (l1 %.3e)  |u|_{rho-d0}: l1 %.3e corner %.3e | Gamma_spec sup|g| %.3e  "
              "Russmann sup|g| %.3e | ratios: Russmann/measured %.0f, Gamma_spec/measured %.1f" % (
                  which, name, g_sup, g_l1, u_l1, max(u_cor.values()), Gs * g_sup, GR * g_sup,
                  GR * g_sup / max(u_cor.values()), Gs * g_sup / max(u_cor.values())))
