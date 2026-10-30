#!/usr/bin/env python3
"""Three-body candidates.  Usage: python3 run_r3bp.py cc07 | polar | hill | trojan | hh

cc07    the Celletti-Chierchia 2007 truncated Sun-Jupiter-Victoria Hamiltonian in Delaunay variables (primary, sqrt only for e)
polar   the exact PCR3BP at the true mass ratio in the radial polar chart (no Kepler equation at all, sqrt and division)
hill    the planar Hill lunar problem at the true m = 0.0748, e near 0.055, same chart
trojan  exact PCR3BP near L4 in a double polar chart, tadpole tori
hh      Hénon-Heiles loop tori in the plane polar chart

Every H is one of models.py.  Time unit: 2 pi (Jupiter's period = 1, Moon's month = 1), so frequencies are in cycles.
"""
import math
import sys
import time
import numpy as np

import kamlib as kl
import models as md
import pipeline as pl

GOLD = (math.sqrt(5) - 1) / 2
MU_J = 9.5388e-4     # Jupiter/Sun+Jupiter, 1/1047.35 + small
TWO_PI = 2 * math.pi


def cont_float(x, nmax=6, kmax=3):
    """continued fraction partial quotients of x (first nmax)."""
    out = []
    for _ in range(nmax):
        a = math.floor(x)
        out.append(a)
        x = x - a
        if x < 1e-12:
            break
        x = 1 / x
    return out


def from_cf(cf):
    """value of [a0; a1, ..., an, 1, 1, 1, ...]."""
    x = GOLD
    for a in reversed(cf[1:]):
        x = 1 / (a + x)
    return cf[0] + x


# ---------------------------------------------------------------------------------------------

def cc07():
    """Two tori bounding Victoria: L = 0.670 +- 0.001 at energy E* = -1.769 (mp_arc 07-303 sec. 6.4), eps = 1/1000.  Frequencies
    (alpha, -1), alpha = 1/L^3 with the continued fraction tail replaced by ones after order 5, as in the paper."""
    eps = 1e-3
    out = {}
    H_of = lambda t: md.cc07(eps * t)
    for name, Lt in (("L+", 0.671), ("L-", 0.669), ("L0", 0.670)):
        alpha = from_cf(cont_float(1 / Lt ** 3, 5))
        om = (alpha, -1.0)
        E = -1.769 * TWO_PI
        G0 = (-1 / (2 * Lt ** 2) + 1.769)
        g = kl.Grid(128, 128)
        tor = kl.Torus(g, (TWO_PI * Lt, TWO_PI * G0))
        steps = [0.25, 0.5, 0.75, 1.0]
        t0 = time.time()
        tor, s, err, t = pl.continuation(H_of, lambda t: om, tor, steps, E_of=lambda t: E)
        if t < 1:
            print(name, "failed", t, err, flush=True)
            continue
        H = H_of(1.0)
        gam = kl.dio_gamma(om)[0] * 0.965
        res = pl.analyse(H, tor, om, s, [1 / 200, 1 / 100, 1 / 50, 1 / 25, 1 / 15], cs=(0.25, 0.5, 1.0), lams=(1.0, TWO_PI, 4 * TWO_PI), gamma=gam, mu=1 / 160, coarsen=(96, 96))
        res.update(alpha=alpha, cf=cont_float(alpha, 8), s=s, err=err, L_range=[float(tor.y[0].min() / TWO_PI), float(tor.y[0].max() / TWO_PI)],
                   G_range=[float(tor.y[1].min() / TWO_PI), float(tor.y[1].max() / TWO_PI)])
        out[name] = res
        pl.show("CC07 " + name, res)
        print("    alpha %.6f s %.8f err %.1e L in [%.5f, %.5f] time %.1f" % (alpha, s, err, res["L_range"][0], res["L_range"][1], time.time() - t0), flush=True)
    pl.save("cc07.json", out)


# ---------------------------------------------------------------------------------------------

def kepler_torus(g, a, e, r0, kap, mu0=1.0):
    """Unperturbed Kepler torus in the radial polar chart: theta2 = l/2 pi, theta1 = (pomega + l)/2 pi, K primary."""
    l = TWO_PI * g.t2
    u = l + 0.0
    for _ in range(40):
        u = u - (u - e * np.sin(u) - l) / (1 - e * np.cos(u))
    r = a * (1 - e * np.cos(u))
    n = math.sqrt(mu0 / a ** 3)
    pr = n * a * a * e * np.sin(u) / r
    f = np.arctan2(math.sqrt(1 - e * e) * np.sin(u), np.cos(u) - e)
    Gv = math.sqrt(mu0 * a * (1 - e * e))
    al = np.arctan2((r - r0) / kap, kap * pr)
    I = 0.5 * (((r - r0) / kap) ** 2 + (kap * pr) ** 2)
    # unwrap: al - l is periodic in l
    uu0 = np.angle(np.exp(1j * (f - l))) / TWO_PI
    uu1 = np.angle(np.exp(1j * (al - l))) / TWO_PI
    tor = kl.Torus(g, (TWO_PI * Gv, 0.0))
    tor.u[0] = uu0
    tor.u[1] = uu1
    tor.y[1] = TWO_PI * I
    return tor, n, Gv


def polar(eccs=(0.22, 0.12, 0.06)):
    """Exact PCR3BP, a near 2.334 AU / 5.2044 AU = 0.4485; several eccentricities, n near 3.32."""
    out = {}
    a0 = 2.334 / 5.2044
    for e in eccs:
        n0 = a0 ** -1.5
        # frequencies: (n - 1, n) with n noble near the Kepler value
        cf = cont_float(n0, 4)
        n = from_cf(cf)
        a = n ** (-2 / 3)
        om = (n - 1, n)
        kap = 1 / math.sqrt(n)
        H_of = lambda t: md.pcr3bp_polar(MU_J * t, a, kap)
        for grid in ((384, 192) if e > 0.2 else (256, 128),):
            g = kl.Grid(*grid)
            tor, n_, Gv = kepler_torus(g, a, e, a, kap)
            t0 = time.time()
            steps = [0.05 * j for j in range(1, 21)]
            tor, s, err, t = pl.continuation(H_of, lambda t: om, tor, steps, maxerr=1e-6, tol=2e-12)
            nm = "polar e=%.2f" % e
            print(nm, "reached t %.2f err %.1e s %.6f time %.1f" % (t, err, s, time.time() - t0), flush=True)
            if t < 1:
                out[nm] = dict(failed=True, t=t, err=err)
                continue
            H = H_of(1.0)
            gam = kl.dio_gamma(om)[0] * 0.965
            res = pl.analyse(H, tor, om, s, [1 / 200, 1 / 100, 1 / 50, 1 / 25], cs=(0.125, 0.25, 0.5, 1.0), lams=(0.1, 0.25, 0.5, TWO_PI * 0.25, TWO_PI), gamma=gam, mu=1 / 160, coarsen=(128, 96))
            rr = a + kap * np.sqrt(2 * np.maximum(tor.y[1], 0) / TWO_PI) * np.sin(TWO_PI * tor.z()[1])
            res.update(n=n, om=list(om), s=s, err=err, r_range=[float(rr.min()), float(rr.max())], I_range=[float(tor.y[1].min()), float(tor.y[1].max())])
            out[nm] = res
            pl.show(nm, res)
            print("    r in [%.4f, %.4f] (apo/peri of Kepler: %.4f, %.4f) time %.1f" % (rr.min(), rr.max(), a * (1 - e), a * (1 + e), time.time() - t0), flush=True)
    pl.save("polar.json", out)


def polar2():
    """e = 0.22 away from 10:3: noble mean motions on both sides of it, n = [3; 3, 1bar] and [3; 2, 1bar], at the same chart."""
    out = {}
    for label, n in (("n=[3;3,1bar]", 3 + 1 / (3 + GOLD)), ("n=[3;2,1bar]", 3 + 1 / (2 + GOLD)), ("n=[3;1,1,1bar]", 3 + 1 / (1 + 1 / (1 + GOLD)))):
        for e in (0.22, 0.16):
            a = n ** (-2 / 3)
            om = (n - 1, n)
            kap = 1 / math.sqrt(n)
            H_of = lambda t: md.pcr3bp_polar(MU_J * t, a, kap)
            g = kl.Grid(384, 192)
            tor, n_, Gv = kepler_torus(g, a, e, a, kap)
            t0 = time.time()
            tor, s, err, t = pl.continuation(H_of, lambda t: om, tor, [0.05 * j for j in range(1, 21)], maxerr=1e-6, tol=3e-12)
            nm = "polar %s e=%.2f" % (label, e)
            print(nm, "a(AU) %.3f reached t %.2f err %.1e time %.1f" % (a * 5.2044, t, err, time.time() - t0), flush=True)
            if t < 1:
                out[nm] = dict(failed=True, t=t, err=err)
                continue
            gam = kl.dio_gamma(om)[0] * 0.965
            res = pl.analyse(H_of(1.0), tor, om, s, [1 / 200, 1 / 100, 1 / 50], cs=(0.125, 0.25, 0.5, 1.0), lams=(0.25, 0.5, 1.5), gamma=gam, mu=1 / 160, coarsen=(128, 96))
            res.update(n=n, s=s, err=err)
            out[nm] = res
            pl.show(nm, res)
    pl.save("polar2.json", out)


# ---------------------------------------------------------------------------------------------

def hill(es=(0.0549, 0.04, 0.07)):
    """Continuation in the tidal term at prescribed mean actions, then a noble frequency ratio at the same energy."""
    m = 0.0748
    out = {}
    for e in es:
        a = 1.0
        kap = 1.0
        g = kl.Grid(192, 192)
        tor, n_, Gv = kepler_torus(g, a, e, a, kap)
        H_of = lambda t: _hill_t(m, t, a, kap)
        ybar = (float(tor.y[0].mean()), float(tor.y[1].mean()))
        om = (1 - m, 1.0)
        t0 = time.time()
        nm = "Hill e0=%.3f" % e
        for t in [0.1 * j for j in range(1, 11)]:
            tor, om, err = kl.find_freq(H_of(t), tor, om, ybar)
            if not np.isfinite(err) or err > 3e-5:
                print(nm, "free-frequency continuation failed at t", t, "err", err, flush=True)
                break
        else:
            # in the frame rotating at m: om[0] = n - m, om[1] = n - (perigee rate), both per unit time at a = 1 (n is not exactly 1)
            n_true = om[0] + m
            perigee = (n_true - om[1]) / n_true
            print(nm, "true frequencies (%.6f, %.6f) n %.6f perigee rate per mean motion %.6f err %.1e" % (om[0], om[1], n_true, perigee, err), flush=True)
            H = H_of(1.0)
            ratio = om[0] / om[1]
            res = None
            for depth in (6, 5, 4):
                cf = cont_float(ratio, depth)
                om2 = (from_cf(cf) * om[1], om[1])
                E0 = float(np.real(kl.derivs(H, tor.z(), 1, const=True)[0]).mean())
                # ramp to the noble ratio
                tor2, s, err2 = tor, 1.0, None
                ok = True
                for f in (0.0, 0.25, 0.5, 0.75, 1.0):
                    om3 = (om[0] + f * (om2[0] - om[0]), om[1])
                    tor2, s, err2 = kl.solve(H, tor2, om3, s, E0=E0, iso=True, tol=5e-12, maxit=40)
                    print("     depth", depth, "f", f, "err %.2e s %.8f" % (err2, s), flush=True)
                    if not np.isfinite(err2) or err2 > 1e-6:
                        ok = False
                        break
                if ok:
                    res = (tor2, s, err2, om3, cf)
                    break
            if res is None:
                out[nm] = dict(failed=True, stage="noble")
                print(nm, "noble step failed", flush=True)
                continue
            tor2, s, err2, om3, cf = res
            gam = kl.dio_gamma(om3)[0] * 0.965
            ana = pl.analyse(H, tor2, om3, s, [1 / 200, 1 / 100, 1 / 50, 1 / 25, 1 / 15], cs=(0.5, 1.0, 2.0), lams=(0.05, 0.25, 1.0, TWO_PI), gamma=gam, mu=1 / 160, coarsen=(128, 128))
            rr = a + kap * np.sqrt(2 * np.maximum(tor2.y[1], 0) / TWO_PI) * np.sin(TWO_PI * tor2.z()[1])
            ana.update(om_true=list(om), om=list(om3), s=s, err=err2, r_range=[float(rr.min()), float(rr.max())], cf=cf, perigee=perigee)
            out[nm] = ana
            pl.show(nm, ana)
            print("    r in [%.4f, %.4f] cf %s s %.6f time %.1f" % (rr.min(), rr.max(), cf, s, time.time() - t0), flush=True)
    pl.save("hill.json", out)


def _hill_t(m, t, r0, kap):
    """Hill Hamiltonian with the tidal term scaled by t: t = 0 is Kepler in the rotating frame."""
    base = md.hill_polar(m, r0, kap)
    if t == 1.0:
        return base
    def H(z):
        q1, q2, P1, P2 = z
        G = P1 * (1 / TWO_PI)
        I = P2 * (1 / TWO_PI)
        th = TWO_PI * q1
        al = TWO_PI * q2
        rt = md.jsqrt(I * 2.0)
        r = r0 + kap * (rt * md.jsin(al))
        pr = (rt * md.jcos(al)) * (1 / kap)
        c = md.jcos(th)
        return ((pr * pr) * 0.5 + (G * G) * (1 / (r * r)) * 0.5 - m * G - (1 / r)
                - (t * m * m) * ((r * r) * ((c * c) * 3.0 - 1.0) * 0.5)) * TWO_PI
    return H


# ---------------------------------------------------------------------------------------------

def trojan(cases=((0.03, 5.0), (0.05, 10.0), (0.10, 10.0), (0.05, 15.0), (0.10, 15.0), (0.05, 20.0), (0.10, 20.0), (0.10, 25.0))):
    """cases = (e, half libration amplitude in degrees about L4), in the guiding-centre chart models.trojan_shear; continuation in the
    amplitude at prescribed mean actions with the frequency free, then a noble ratio."""
    mu = MU_J
    out = {}
    nu = math.sqrt(27 * mu / 4)
    kap_t = math.sqrt(3 / nu)
    # exact L4: Sun at (-mu, 0), Jupiter at (1 - mu, 0)
    x4, y4 = 0.5 - mu, math.sqrt(3) / 2
    r4 = math.hypot(x4, y4)
    th4 = math.atan2(y4, x4)
    G4 = r4 ** 2
    rho4 = r4 - G4 ** 2
    H = md.trojan_shear(mu, 1.0, kap_t, G0=G4, th0=th4, rho0=rho4)
    for e, D in cases:
        nm = "Trojan e=%.2f D=%g" % (e, D)
        g = kl.Grid(96, 96)
        t0 = time.time()
        fails = False
        fr = [0.03 * 1.25 ** j for j in range(16)] + [1.0]
        fr = [f for f in fr if f <= 1.0]
        for j, f in enumerate(fr):
            amp = math.radians(D) * f
            I0 = TWO_PI * (e * f) ** 2 / 2
            Y0 = TWO_PI * (amp / kap_t) ** 2 / 2
            if j == 0:
                tor = kl.Torus(g, (I0, Y0))
                gr = kl.derivs(H, tor.z(), 1)[0].real
                om = (float(gr[2].mean()), float(gr[3].mean()))
            else:
                q = (f / fr[j - 1]) ** 2
                tor.y *= q
                tor.u *= 1.0
            tor, om, err = kl.find_freq(H, tor, om, (I0, Y0), tol=2e-12)
            if not np.isfinite(err) or err > 1e-5:
                print(nm, "failed at amplitude fraction %.3f err %.1e" % (f, err), flush=True)
                fails = True
                break
        if fails:
            out[nm] = dict(failed=True, frac=f, err=err)
            continue
        ratio = om[0] / abs(om[1])
        cf = cont_float(ratio, 5)
        om2 = (from_cf(cf) * abs(om[1]), om[1])
        E0 = float(np.real(kl.derivs(H, tor.z(), 1, const=True)[0]).mean())
        tor2, s, err2 = kl.solve(H, tor, om2, 1.0, E0=E0, iso=True, tol=2e-12)
        print(nm, "freq (%.5f, %.5f) ratio %.3f cf %s err %.1e s %.6f" % (om[0], om[1], ratio, cf, err2, s), flush=True)
        if not np.isfinite(err2) or err2 > 1e-8:
            out[nm] = dict(failed=True, stage="noble", err=err2)
            continue
        gam = kl.dio_gamma(om2)[0] * 0.965
        ana = pl.analyse(H, tor2, om2, s, [1 / 400, 1 / 200, 1 / 100, 1 / 50, 1 / 25], cs=(0.5, 1.0, 2.0, 4.0), lams=(I0 / 2, I0, Y0, 4 * Y0), gamma=gam, mu=1 / 160)
        ana.update(s=s, err=err2, cf=cf, I0=I0, Y0=Y0, Imin=float(tor2.y[0].min()), Ymin=float(tor2.y[1].min()), om_true=list(om))
        out[nm] = ana
        pl.show(nm, ana)
        print("    min I/mean %.3f min Y/mean %.3f time %.1f" % (ana["Imin"] / I0, ana["Ymin"] / Y0, time.time() - t0), flush=True)
    pl.save("trojan.json", out)


# ---------------------------------------------------------------------------------------------

def isotropic_torus(g, a0, b0, r0, kap):
    """exact torus of the isotropic oscillator: x = a0 cos tau, y = b0 sin tau; theta2 = tau/pi, theta1 = tau/2 pi."""
    tau = np.pi * g.t2
    x, y = a0 * np.cos(tau), b0 * np.sin(tau)
    px, py = -a0 * np.sin(tau), b0 * np.cos(tau)
    r = np.sqrt(x * x + y * y)
    th = np.arctan2(y, x)
    pr = (x * px + y * py) / r
    G = a0 * b0
    al = np.arctan2((r - r0) / kap, kap * pr)
    I = 0.5 * (((r - r0) / kap) ** 2 + (kap * pr) ** 2)
    tor = kl.Torus(g, (TWO_PI * G, 0.0))
    # tau runs over [0, pi) in theta2: alpha advances by 2 pi, theta by pi; theta1 mean = tau/2 pi + (theta1 free), so add g.t1 implicitly
    tor.u[0] = np.angle(np.exp(1j * (th - tau))) / TWO_PI
    tor.u[1] = np.angle(np.exp(1j * (al - 2 * tau))) / TWO_PI
    tor.y[1] = TWO_PI * I
    return tor


def hh(cases=((1 / 24, 0.75), (1 / 12, 0.75), (1 / 8, 0.75), (1 / 8, 0.5), (1 / 6.5, 0.75))):
    """Loop tori at energy E: start from the ellipse with axis ratio b/a at t = 0.  Note the map th -> (theta1, theta2) has theta1 = th/2 pi - theta2/2.
    The torus below uses the unimodular angles (theta1 + theta2/2 is not integral), so it keeps the period-2 orbit structure: the winding is handled
    by taking theta2 as the radial angle and theta1 as the mean polar angle, frequency (1, 2) at t = 0."""
    out = {}
    for E, ratio in cases:
        a0 = math.sqrt(2 * E / (1 + ratio ** 2))
        b0 = ratio * a0
        G0 = a0 * b0
        r0 = math.sqrt(a0 * b0)
        kap = 1 / math.sqrt(2.0)
        g = kl.Grid(128, 128)
        tor = isotropic_torus(g, a0, b0, r0, kap)
        ybar = (float(tor.y[0].mean()), float(tor.y[1].mean()))
        om = (1.0, 2.0)
        nm = "HH E=%.4f b/a=%.2f" % (E, ratio)
        t0 = time.time()
        ok = True
        for t in [0.05 * j for j in range(1, 21)]:
            tor, om, err = kl.find_freq(md.henon_heiles_t(t, r0, kap), tor, om, ybar, tol=2e-12)
            if not np.isfinite(err) or err > 1e-7:
                print(nm, "failed at t %.2f err %.1e" % (t, err), flush=True)
                ok = False
                break
        if not ok:
            out[nm] = dict(failed=True, t=t, err=err)
            continue
        H = md.henon_heiles_t(1.0, r0, kap)
        Ev = float(np.real(kl.derivs(H, tor.z(), 1, const=True)[0]).mean()) / TWO_PI
        ratio_f = om[1] / om[0]
        cf = cont_float(ratio_f, 4)
        om2 = (om[0], from_cf(cf) * om[0])
        tor2, s, err2 = kl.solve(H, tor, om2, 1.0, E0=Ev * TWO_PI, iso=True, tol=2e-12)
        print(nm, "E %.5f freq (%.5f, %.5f) ratio %.4f cf %s err %.1e time %.1f" % (Ev, om[0], om[1], ratio_f, cf, err2, time.time() - t0), flush=True)
        if not np.isfinite(err2) or err2 > 1e-8:
            out[nm] = dict(failed=True, stage="noble", err=err2)
            continue
        gam = kl.dio_gamma(om2)[0] * 0.965
        ana = pl.analyse(H, tor2, om2, s, [1 / 200, 1 / 100, 1 / 50, 1 / 25], cs=(0.5, 1.0, 2.0), lams=(0.25, 1.0, TWO_PI), gamma=gam, mu=1 / 160, coarsen=(96, 96))
        ana.update(s=s, err=err2, cf=cf, E=Ev)
        out[nm] = ana
        pl.show(nm, ana)
    pl.save("hh.json", out)


if __name__ == "__main__":
    {"cc07": cc07, "polar": polar, "polar2": polar2, "hill": hill, "trojan": trojan, "hh": hh}[sys.argv[1]]()
