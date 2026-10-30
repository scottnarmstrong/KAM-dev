#!/usr/bin/env python3
"""Librational tori of the synchronous resonance (Moon, Rhea) as PRIMARY tori in a polar chart.

Chart about (Q1, P1) = (0, 1), Q1 = spin angle minus orbital phase, in the rotated frame:
    Q1 = a sqrt(2 I) sin(2 pi th),  P1 = 1 + sqrt(2 I)/a cos(2 pi th),  X = 2 pi I conjugate to th,
so a torus winding once around the synchronous orbit is primary in (th, phi).  No new KAM theorem is needed, only the primitive sqrt.

The torus is found by continuation in the libration frequency nu = [0; N, tail...], downward from the linear value 2 sqrt(eps A2).
Output: amplitude in degrees of the angle x = 2 pi Q1, thresholds, digits.  Usage: python3 run_libration.py moon | rhea
"""
import math
import sys
import time
import numpy as np

import kamlib as kl
import models as md
import pipeline as pl

GOLD = (math.sqrt(5) - 1) / 2


def noble_after(N, b):
    """1/(N + 1/(b + g)), a noble number just below 1/N for b >= 1."""
    return 1 / (N + 1 / (b + GOLD))


def run(name, eps, A, targets, grid=(64, 32), rhos=(1 / 800, 1 / 400, 1 / 200, 1 / 100, 1 / 70), cs=(0.5, 1.0, 1.75, 4.0), lams=None):
    A2 = A[2]
    nu0 = 2 * math.sqrt(eps * A2)
    omega0 = 2 * math.pi * nu0
    a = 1 / math.sqrt(omega0)
    H = md.spin_librational(eps, A, 1.0, a=a)
    g = kl.Grid(*grid)
    # start: flat torus at the action predicted by the twist dnu/dX = -1/2 for the first target
    X = 2 * (nu0 - targets[0][1])
    tor = kl.Torus(g, (X, 0.0))
    gr = kl.derivs(H, tor.z(), 1)[0].real
    out = {}
    nu_start = float(gr[2].mean())
    tor.y[1] += -float(np.real(kl.derivs(H, tor.z(), 1, const=True)[0]).mean())
    print(name, "nu0 %.6f chart a %.4f start X %.3e nu %.6f" % (nu0, a, X, nu_start), flush=True)
    s = 1.0
    nu_cur = nu_start
    for tgt_name, nu_tgt in targets:
        t0 = time.time()
        # geometric steps in the distance from nu0: dnu is a fixed fraction of the current action X/2
        dist, nus = nu0 - nu_cur, []
        while dist * 1.2 < nu0 - nu_tgt:
            dist *= 1.2
            nus.append(nu0 - dist)
        nus.append(nu_tgt)
        H_of = lambda t: H
        def om_of(t):
            return (float(t), 1.0)
        tor2, s2, err, t_ok = pl.continuation(H_of, om_of, tor, list(nus), s=s, E_of=lambda t: 0.0, tol=3e-13, maxerr=1e-7, iso=True)
        if abs(t_ok - nus[-1]) > 1e-15:
            print("  stopped at nu %.6f (target %.6f) err %.1e" % (t_ok, nu_tgt, err), flush=True)
            out[tgt_name] = dict(failed=True, t=t_ok, err=err)
            break
        tor, s = tor2, s2
        nu_cur = nu_tgt
        om = (nu_tgt, 1.0)
        gr = kl.Grid(*grid)
        rvals = tor.z()
        Xv = tor.y[0]
        r = np.sqrt(np.maximum(Xv, 0) / math.pi)
        Q = a * r * np.sin(2 * np.pi * rvals[0])
        P = r / a * np.cos(2 * np.pi * rvals[0])
        amp = float(np.abs(Q).max() * 360)
        pmax = float(np.abs(P).max())
        gam = kl.dio_gamma(om)[0] * 0.965
        Xm = float(Xv.mean())
        ls = lams if lams else tuple(Xm * f for f in (1 / 8, 1 / 2, 1, 4))
        res = pl.analyse(H, tor, om, s, rhos, cs=cs, lams=ls, gamma=gam, mu=1 / 160)
        mono = float((1 + tor.g.d(tor.u[0], 0).real).min())   # the torus is a graph over (th, phi) iff this is positive
        res.update(amp_deg=amp, pmax=pmax, nu=nu_tgt, Xmean=Xm, Xmin=float(Xv.min()), err=err, chart_a=a, mono=mono)
        out[tgt_name] = res
        pl.show("%s %s" % (name, tgt_name), res)
        print("    libration amplitude %.3f deg, max|p-1| %.5f, X mean %.3e min %.3e, min(1+du/dth) %.3f, err %.1e, time %.1f" % (amp, pmax, Xm, res["Xmin"], mono, err, time.time() - t0), flush=True)
    return out


def moon():
    eps, e = 69 / 200000, 549 / 10000
    A = md.moon_A(e)
    nu0 = 2 * math.sqrt(eps * A[2])
    N0 = 1 / nu0
    # nu decreases with amplitude: nu = 1/(N + x); targets by continued fraction
    N = int(N0)
    targets = []
    for x_name, x in (("x1", 1 / (3 + 1 / (2 + GOLD))), ("x2", 1 / (2 + 1 / (3 + GOLD))), ("x3", 1 / (2 + GOLD))):
        if N + x > N0:
            targets.append((x_name, 1 / (N + x)))
    for N2, b in ((N + 1, 1), (N + 2, 1), (N + 4, 1), (N + 7, 1), (N + 12, 1), (N + 25, 1)):
        targets.append(("N%d" % N2, 1 / (N2 + 1 / (b + GOLD))))
    out = run("Moon", eps, A, targets)
    pl.save("moon_lib.json", out)


def rhea():
    e = 0.00126
    eps = 1.5 * (765.0 ** 2 - 763.1 ** 2) / (765.0 ** 2 + 763.1 ** 2)
    A = {m: v for m, v in md.hansen_A(e, mmax=8).items() if abs(v) > 1e-14}
    nu0 = 2 * math.sqrt(eps * A[2])
    N = int(1 / nu0)
    targets = [("N%d" % (N + j), 1 / (N + j + 1 / (1 + GOLD))) for j in (1, 2, 4)]
    out = run("Rhea", eps, A, targets)
    pl.save("rhea_lib.json", out)


if __name__ == "__main__":
    {"moon": moon, "rhea": rhea}[sys.argv[1]]()
