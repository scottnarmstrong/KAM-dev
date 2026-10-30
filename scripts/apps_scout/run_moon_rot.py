#!/usr/bin/env python3
"""Validation on package R1, then rotational barriers: Moon (N = 40..120), Mercury 3:2, Saturnian moons.

Usage: python3 run_moon_rot.py validate | moon | bodies
"""
import math
import sys
import time
import numpy as np

import kamlib as kl
import models as md
import pipeline as pl

G = (math.sqrt(5) - 1) / 2


def barrier(eps, A, delta, N, sign, grid=(192, 48), nst=12):
    nu = sign / (N + G)
    om = (nu, 1.0)
    p0 = delta + nu
    y0 = (p0, -(p0 ** 2 / 2 - delta * p0))
    g = kl.Grid(*grid)
    tor = kl.Torus(g, y0)
    H_of = lambda t: md.spin_rot(eps * t, A, delta)
    tor, s, err, t = pl.continuation(H_of, lambda t: om, tor, [j / nst for j in range(1, nst + 1)])
    return tor, s, err, t, om


def validate():
    """R1 (CONSTANTS-STUDY 2.2, SO-GEN2): p range 0.968007..0.98181; rho' = 1/70: |DK| 1.303, |B| 1.833, torsion inverse 1.022493;
    threshold (iso, c = 7/4) -24.98."""
    eps, e = 69 / 200000, 549 / 10000
    A = md.moon_A(e)
    t0 = time.time()
    tor, s, err, t, om = barrier(eps, A, 1.0, 40, -1, grid=(256, 48))
    H = md.spin_rot(eps, A, 1.0)
    print("p range %.6f %.6f err %.1e time %.1f" % (tor.y[0].min(), tor.y[0].max(), err, time.time() - t0))
    a = pl.analyse(H, tor, om, s, [1 / 70], cs=(1.0, 1.75), gamma=abs(om[0]) * 0.965)
    for r in a["rows"]:
        print("c %.2f M %.4f sK %.4f sB %.4f sT %.4f cur %.2f v1 %.2f v2 %.2f ell1 %.2f" % (r["c"], r["M"], r["sK"], r["sB"], r["sT"], r["current"], r["v1"], r["v2"], r["ell1"]))
    pl.show("moon N=40 lower", a)
    a["p_range"] = [float(tor.y[0].min()), float(tor.y[0].max())]
    pl.save("validate_R1.json", a)


def moon():
    eps, e = 69 / 200000, 549 / 10000
    A = md.moon_A(e)
    H = md.spin_rot(eps, A, 1.0)
    rows = {}
    for N in (40, 50, 60, 80, 100, 120):
        for sign in (-1, 1):
            t0 = time.time()
            tor, s, err, t, om = barrier(eps, A, 1.0, N, sign, grid=(512, 48), nst=14)
            name = "moon N=%d %s" % (N, "lower" if sign < 0 else "upper")
            if t < 1 or err > 1e-9:
                print(name, "FAILED at t", t, "err", err, flush=True)
                rows[name] = dict(failed=True, t=t, err=err)
                continue
            a = pl.analyse(H, tor, om, s, [1 / 400, 1 / 200, 1 / 100, 1 / 70, 1 / 50], cs=(1.0, 1.75), lams=(1.0,), gamma=abs(om[0]) * 0.965, coarsen=(256, 32))
            a["pmax"] = float(np.abs(tor.y[0] - 1).max())
            a["err"] = err
            rows[name] = a
            pl.show(name, a)
            print("    max|p-1| %.5f err %.1e time %.1f" % (a["pmax"], err, time.time() - t0), flush=True)
    pl.save("moon_rot.json", rows)


def shape_eps(a, b):
    """(3/2)(B-A)/C for a homogeneous triaxial body with equatorial semi-axes a > b."""
    return 1.5 * (a * a - b * b) / (a * a + b * b)


# Moon, Mercury: Celletti-Chierchia 1998 Table 1.  Enceladus: axes 256.2/251.4 km (arXiv:1509.07555).  Dione, Rhea axes: Thomas 2010 values,
# quoted from memory and NOT verified; Celletti 1990 used her own eps, unavailable here.  e: mean orbital eccentricities.
BODIES = {
    "Mercury": dict(e=0.2056, eps=1.5e-4, delta=1.5),
    "Rhea": dict(e=0.00126, eps=shape_eps(765.0, 763.1), delta=1.0),
    "Dione": dict(e=0.0022, eps=shape_eps(563.4, 561.3), delta=1.0),
    "Enceladus": dict(e=0.0047, eps=shape_eps(256.2, 251.4), delta=1.0),
}


def bodies():
    out = {}
    for name, b in BODIES.items():
        e, eps, delta = b["e"], b["eps"], b["delta"]
        A = {m: v for m, v in md.hansen_A(e, mmax=16).items() if abs(v) > 1e-14}
        k = {1.0: 2, 1.5: 3}[delta]
        width = 2 * math.sqrt(eps * abs(A[k]))
        H = md.spin_rot(eps, A, delta)
        print("==", name, "e", e, "eps %.3e" % eps, "A_res %.4f separatrix half-width %.4f modes %d" % (A[k], width, len(A)), flush=True)
        for fr in (1.25, 1.05):
            N = max(int(round(fr / width - G)), 2)
            for sign in (-1, 1):
                t0 = time.time()
                tor, s, err, t, om = barrier(eps, A, delta, N, sign, grid=(512, 96 if name == "Mercury" else 48), nst=14)
                nm = "%s N=%d %s" % (name, N, "lower" if sign < 0 else "upper")
                if t < 1 or err > 1e-9:
                    print(nm, "FAILED at t %.3f err %.1e" % (t, err), flush=True)
                    out[nm] = dict(failed=True, t=t, err=err)
                    continue
                gam = kl.dio_gamma(om)[0] * 0.965
                a = pl.analyse(H, tor, om, s, [1 / 200, 1 / 100, 1 / 70, 1 / 50], cs=(0.25, 0.5, 1.0, 1.75), lams=(1.0, 2.0, 4.0), gamma=gam, coarsen=(256, 48 if name == "Mercury" else 32))
                a["pmax"] = float(np.abs(tor.y[0] - delta).max())
                a["sep"] = width
                a["err"] = err
                out[nm] = a
                pl.show(nm, a)
                print("    max|p-res| %.5f (sep %.5f) err %.1e gamma %.4f time %.1f" % (a["pmax"], width, err, gam, time.time() - t0), flush=True)
    pl.save("spin_bodies.json", out)


def kepler():
    """Exact Kepler forcing in the eccentric-anomaly chart (models.spin_kepler), against the Hansen-truncated model at the same frequency."""
    out = {}
    for name, e, eps, delta, Ns in (("Moon exact Kepler", 0.0549, 69 / 200000, 1.0, (40, 60)), ("Mercury exact Kepler", 0.2056, 1.5e-4, 1.5, (74,))):
        for N in Ns:
            nu = -1 / (N + G)
            om = (nu, 1.0)
            p0 = delta + nu
            g = kl.Grid(512, 96)
            tor = kl.Torus(g, (p0, 0.0))
            w = g.t2
            rho = 1 - e * np.cos(2 * np.pi * w)
            tor.u[0] = -p0 * (e / (2 * np.pi)) * np.sin(2 * np.pi * w)
            tor.y[1] = -rho * p0 ** 2 / 2 + delta * p0
            H_of = lambda t: md.spin_kepler(eps * t, e, delta)
            t0 = time.time()
            tor, s, err, t = pl.continuation(H_of, lambda t: om, tor, [j / 14 for j in range(1, 15)], E_of=lambda t: 0.0)
            nm = "%s N=%d lower" % (name, N)
            print(nm, "reached t %.2f err %.1e s %.8f time %.1f" % (t, err, s, time.time() - t0), flush=True)
            if t < 1:
                out[nm] = dict(failed=True, t=t, err=err)
                continue
            gam = kl.dio_gamma(om)[0] * 0.965
            a = pl.analyse(H_of(1.0), tor, om, s, [1 / 200, 1 / 100, 1 / 70, 1 / 50], cs=(1.0, 1.75), gamma=gam, coarsen=(256, 48))
            a["pmax"] = float(np.abs(tor.y[0] - delta).max())
            a["err"] = err
            a["s"] = s
            out[nm] = a
            pl.show(nm, a)
            print("    max|p-res| %.5f s %.8f" % (a["pmax"], s), flush=True)
    pl.save("spin_kepler.json", out)


if __name__ == "__main__":
    {"validate": validate, "moon": moon, "bodies": bodies, "kepler": kepler}[sys.argv[1]]()
