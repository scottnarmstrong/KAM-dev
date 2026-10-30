#!/usr/bin/env python3
"""Magnetic field lines.

1. The tokamak-like model of Valvo-Locatelli 2021 (arXiv:2101.07785, eqs (1)-(3)), uncontrolled:
      H(psi) = psi - (3/4) psi^2 + (1/3) psi^3 - (1/16) psi^4,  v = eps (cos(2 theta - phi) + cos(3 theta - 2 phi)),
   a polynomial Hamiltonian: a HamExpr today, no new primitive.  Barrier frequency 1/q between the resonances 1/2 and 2/3.
2. Our thresholds at PlasmaLean's data for torus A (notes/theory/after-kam.md, KamTorusAExact.lean): gamma = 0.0687, r = 0.1257 rad, frame and torsion bounds as
   declared there.  Not like for like: PlasmaLean's theorem is for a polynomial divergence-free field in ell^1 norms with 2 unknown functions.
"""
import math
import numpy as np
from fractions import Fraction as F

import kamlib as kl
import models as md
import pipeline as pl
import thresholds_est as te

TWO_PI = 2 * math.pi
GOLD = (math.sqrt(5) - 1) / 2


def tok(eps):
    def H(z):
        q1, q2, P1, P2 = z
        psi = P1 * (1 / TWO_PI)
        J = P2 * (1 / TWO_PI)
        th = TWO_PI * q1
        ph = TWO_PI * q2
        h = psi - (psi * psi) * 0.75 + (psi * psi * psi) * (1 / 3) - (psi * psi * psi * psi) * (1 / 16)
        return (J + h + eps * (md.jcos(2 * th - ph) + md.jcos(3 * th - 2 * ph))) * TWO_PI
    return H


def iq(psi):
    return (2 - psi) * (2 - 2 * psi + psi * psi) / 4


def psi_of(w):
    a, b = 0.0, 1.0
    for _ in range(80):
        c = (a + b) / 2
        if iq(c) > w:
            a = c
        else:
            b = c
    return a


def tokamak():
    out = {}
    for name, w in (("golden 0.618", GOLD), ("[0;1,1,2,1bar]", 1 / (1 + 1 / (1 + 1 / (2 + GOLD))))):
        om = (w, 1.0)
        psi0 = psi_of(w)
        g = kl.Grid(320, 256)
        tor = kl.Torus(g, (TWO_PI * psi0, 0.0))
        tor.y[1] -= float(np.real(kl.derivs(tok(0.0), tor.z(), 1, const=True)[0]).mean())
        eps_list = [1e-4 * 1.25 ** j for j in range(30)]
        last = None
        for eps in eps_list:
            E0 = 0.0
            tor2, s, err = kl.solve(tok(eps), tor, om, 1.0, E0=E0, iso=True, tol=2e-13, maxit=30)
            if not np.isfinite(err) or err > 1e-8:
                print(name, "stops at eps %.5f err %.1e" % (eps, err), flush=True)
                break
            tor = tor2
            last = (eps, tor.copy(), s)
            if eps >= 0.0012 and "e1" not in out.get(name, {}):
                H = tok(eps)
                gam = kl.dio_gamma(om)[0] * 0.965
                res = pl.analyse(H, tor, om, s, [1 / 200, 1 / 100, 1 / 50], cs=(0.5, 1.0, 2.0), lams=(1.0, TWO_PI), gamma=gam, mu=1 / 160, coarsen=(128, 96))
                res["eps"] = eps
                out.setdefault(name, {})["e1"] = res
                pl.show("tokamak %s eps %.4f" % (name, eps), res)
        eps, tor, s = last
        H = tok(eps)
        gam = kl.dio_gamma(om)[0] * 0.965
        res = pl.analyse(H, tor, om, s, [1 / 400, 1 / 200, 1 / 100, 1 / 50], cs=(0.5, 1.0, 2.0), lams=(1.0, TWO_PI), gamma=gam, mu=1 / 160, coarsen=(128, 96))
        res["eps"] = eps
        out.setdefault(name, {})["last"] = res
        pl.show("tokamak %s eps %.4f (last)" % (name, eps), res)
    pl.save("tokamak.json", out)


def plasmalean():
    """our v1 at PlasmaLean's strip and gamma, for two norm guesses: frame bounds of cA (bD 1.64, derivative bounds up to 3.09), ||T|| 19.84, twist 0.22."""
    rows = {}
    for tag, sK, sB, M, T in (("cA-like", 3.1, 2.0, 3.0, 19.84), ("R1-like", 1.37, 1.93, 1.9, 3.3)):
        P = dict(M=M, sK=sK, sB=sB, sT=1 / 0.22 + 1 / 160, mu=1 / 160, rho=0.1257 / TWO_PI, Tmax=T, M2=M)
        r = te.columns(P, 0.0687, iso=False)
        rows[tag] = {k: (round(v, 2) if isinstance(v, float) else v) for k, v in r.items()}
        print(tag, rows[tag], flush=True)
    pl.save("plasmalean_cmp.json", dict(rows=rows, plasmalean=dict(e0=5.83e-22, tolerance=5.7e-19, kappa=5.7e9, r=0.1257, delta0=0.1257 / 7, gamma=0.0687, coefficients=2925, peak_GB=4.3)))


if __name__ == "__main__":
    tokamak()
    plasmalean()
