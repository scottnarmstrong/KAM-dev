#!/usr/bin/env python3
"""Which branch of c_* binds as the v2 levers are switched on (package R1), and what removing it would buy.  Input for SHARP-PLUS; an estimate, using thresholds_est.sharp_mod.
Compares with the proved tolerance of PlasmaLean on torus A through the single number 32 kappa (Theorem form e <= delta0^4/(32 kappa), radian strip)."""
import math
from fractions import Fraction as F
import sys, os
import thresholds_est as te
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "apost_sharp"))
import thresholds as TH

p, gamma = TH.package_R1()
base = dict(n=2, tau=1, kappa=1, M=p["M"], sK=p["sK"], sB=p["sB"], sT=p["sT"], mu=p["mu"], rho=p["rho"], rhoinf=p["rhoinf"], gbar=p["gbar"], nu=p["nu"], iso=True)
cR = TH.cohConstR_lean(2, 1)
rows = [("v1", dict(cR=cR)),
        ("+ H_T actual (1.2*1.05+1)", dict(cR=cR, HT=te.Q(1.2 * 1.05 + 1))),
        ("+ M2 = 0.56*7/4*1.05", dict(cR=cR, HT=te.Q(2.26), M2=te.Q(0.56 * 1.75 * 1.05))),
        ("+ c_R = 0.036 (FHL17 classic)", dict(cR=te.Q(0.036), HT=te.Q(2.26), M2=te.Q(1.03))),
        ("+ c_R = 0.0093 (ell^1, PlasmaLean)", dict(cR=te.Q(0.0093), HT=te.Q(2.26), M2=te.Q(1.03))),
        ("+ c_R = 0.003 (frequency-specific)", dict(cR=te.Q(0.003), HT=te.Q(2.26), M2=te.Q(1.03)))]
print("| step | log10 threshold | active | log10 branches E, step, sum, nu |")
print("|---|---:|---|---|")
for name, kw in rows:
    k = te.sharp_mod(**{**base, **kw})
    print("| %s | %.2f | %s | %s |" % (name, TH.lg(TH.threshold(k, gamma)), k["active"], ", ".join("%.2f" % TH.lg(k["terms"][x]) for x in ("E", "step", "sum", "nu"))))
for mu in (F(1, 160), F(1, 40), F(1, 10)):
    k = te.sharp_mod(**{**base, "cR": te.Q(0.036), "HT": te.Q(2.26), "M2": te.Q(1.03), "mu": mu})
    print("mu = %s: log10 threshold %.2f, active %s" % (mu, TH.lg(TH.threshold(k, gamma)), k["active"]))
# effect of a sum-branch reduction by a factor f (better budget split, a twist perturbation bound using actual norms)
print()
d = math.log10(0.1257 / 7)
print("PlasmaLean torus A: log10 e_tol = %.2f (delta0^4/(32 kappa)); strip r = 0.1257 rad = %.4f turns" % (4 * d - math.log10(32 * 5.7e9), 0.1257 / (2 * math.pi)))
