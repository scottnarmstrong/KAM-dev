#!/usr/bin/env python3
"""HD11964-PILOT: the pinned model, its nominal state and the exact AMD geometry.

Untrusted design tooling (Apache-2.0).  Python 3, numpy, mpmath.  Reads data/hd11964-pilot.json.

Conventions are those of the frozen Lean definitions (track LP):
  * movingHamiltonian 1 1 nu mu: H = sum_i (|p_i|^2/(2 nu_i) - nu_i/|q_i|) + mu f,
    f = |p_1 + p_2|^2/2 - nu_1 nu_2/|q_1 - q_2|  (planet 0 = HD 11964 c, inner; planet 1 = HD 11964 b, outer);
  * keplerAction Lambda_i = nu_i sqrt(a_i), a_i = -nu_i/(2 E_i), E_i = |p_i|^2/(2 nu_i) - nu_i/|q_i|;
  * strongAMD C = sum Lambda_i - |L|, L = sum q_i x p_i;
  * the chart poincareProd nu 1 (KAM/Planetary/Poincare/Chart.lean): w = ((lam, xi), (Lam, eta)) per planet,
    Gamma = (xi^2 + eta^2)/2, K = 1 - Gamma/Lam, v = sqrt((1 - Gamma/(2 Lam))/Lam) (xi, eta) (= eccentricity vector),
    F - v0 sin F + v1 cos F = lam, J = 1 - v.(cos F, sin F),
    q = (Lam^2/nu^2) (K u - v + (v.u/(1+K)) v),  p = (nu^2/(Lam J)) (Ju - (v.u/(1+K)) Jv),  u = (cos F, sin F),
    J(x, y) = (-y, x).
    So (xi, eta) = sqrt(2 Gamma) (cos varpi, sin varpi), F = eccentric longitude, lam = mean longitude.
"""
import json
import math
import os
from fractions import Fraction as Fr

import mpmath as mp


def R(x):
    """mpf from a Fraction (exact numerator / denominator at the working precision)."""
    return mp.mpf(x.numerator) / x.denominator if isinstance(x, Fr) else mp.mpf(x)

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
DATA = os.path.join(ROOT, "data", "hd11964-pilot.json")


def load(path=DATA):
    with open(path) as fh:
        return json.load(fh)


class Model:
    """Exact rational inputs (Fraction) and mpmath derived quantities."""

    def __init__(self, d=None, dps=40):
        mp.mp.dps = dps
        self.d = d or load()
        d = self.d
        self.msun_mearth = Fr(d["constants"]["msun_over_mearth"]["value"])
        self.dpy = Fr(d["constants"]["days_per_year"]["value"])
        self.mstar = Fr(d["star"]["mass_msun"]["value"])
        pl = d["planets"]
        self.names = [p["name"] for p in pl]
        self.P = [Fr(p["period_days"]["value"]) for p in pl]
        self.e = [Fr(p["ecc"]["value"]) for p in pl]
        self.wstar = [Fr(p["omega_star_deg"]["value"]) for p in pl]
        self.msini = [Fr(p["msini_mearth"]["value"]) for p in pl]
        self.tc = [Fr(p["tc_bjd"]["value"]) for p in pl]
        self.epoch = Fr(d["model"]["epoch_bjd"])
        ratios = [m / (self.msun_mearth * self.mstar) for m in self.msini]
        self.mu = max(ratios)
        self.nu = [r / self.mu for r in ratios]  # exact rationals, max = 1
        self.n = len(pl)

    # ---- derived (mpmath) ------------------------------------------------------------------------
    def axis(self, i):
        """Canonical axis of the nominal state, AU: a^3 = M_star (P/yr)^2."""
        return mp.cbrt(R(self.mstar) * (R(self.P[i]) / R(self.dpy)) ** 2)

    def Lam(self, i):
        return R(self.nu[i]) * mp.sqrt(self.axis(i))

    def Gam(self, i, e=None):
        e = R(self.e[i]) if e is None else R(e)
        return self.Lam(i) * (1 - mp.sqrt(1 - e * e))

    def years_per_unit(self):
        """One model time unit in Julian years: 1 / (2 pi sqrt(M_star/M_sun))."""
        return 1 / (2 * mp.pi * mp.sqrt(R(self.mstar)))

    def mean_anomaly(self, i):
        """Mean anomaly at the epoch (radians), radvel convention for tc."""
        e = R(self.e[i])
        w = mp.radians(R(self.wstar[i]))
        f = mp.pi / 2 - w
        E = 2 * mp.atan(mp.tan(f / 2) * mp.sqrt((1 - e) / (1 + e)))
        M_tc = E - e * mp.sin(E)
        return M_tc + 2 * mp.pi * (R(self.epoch) - R(self.tc[i])) / R(self.P[i])

    def varpi(self, i):
        """Longitude of the planet's periastron in the orbital plane (common node): omega_star + pi."""
        return mp.radians(R(self.wstar[i])) + mp.pi

    def chart_nominal(self):
        """Chart coordinates (lam, xi, Lam, eta) per planet of the nominal state."""
        out = []
        for i in range(self.n):
            L = self.Lam(i)
            G = self.Gam(i)
            vp = self.varpi(i)
            lam = mp.fmod(vp + self.mean_anomaly(i), 2 * mp.pi)
            out.append((lam, mp.sqrt(2 * G) * mp.cos(vp), L, mp.sqrt(2 * G) * mp.sin(vp)))
        return out


# ---- the chart and the physical functions (mpmath scalars) -------------------------------------------
def chart_planet(nu, lam, xi, Lam, eta):
    """Lean `poincare nu 1` for one planet; returns q, p (lists of two mpf)."""
    G = (xi * xi + eta * eta) / 2
    K = 1 - G / Lam
    be = mp.sqrt((1 - G / (2 * Lam)) / Lam)
    v0, v1 = be * xi, be * eta
    F = lam + v0 * mp.sin(lam) - v1 * mp.cos(lam)
    for _ in range(200):
        g = F - v0 * mp.sin(F) + v1 * mp.cos(F) - lam
        dg = 1 - v0 * mp.cos(F) - v1 * mp.sin(F)
        step = g / dg
        F -= step
        if abs(step) < mp.mpf(10) ** (-mp.mp.dps + 5):
            break
    u0, u1 = mp.cos(F), mp.sin(F)
    J = 1 - v0 * u0 - v1 * u1
    vu = (v0 * u0 + v1 * u1) / (1 + K)
    s = Lam * Lam / (nu * nu)
    q = [s * (K * u0 - v0 + vu * v0), s * (K * u1 - v1 + vu * v1)]
    c = nu * nu / (Lam * J)
    p = [c * (-u1 + vu * v1), c * (u0 - vu * v0)]
    return q, p


def kepler_energy(nu, q, p):
    return (p[0] ** 2 + p[1] ** 2) / (2 * nu) - nu / mp.sqrt(q[0] ** 2 + q[1] ** 2)


def kepler_action(nu, q, p):
    E = kepler_energy(nu, q, p)
    return nu * mp.sqrt(-nu / (2 * E))


def cross(q, p):
    return q[0] * p[1] - q[1] * p[0]


def strong_amd(nu, Q, P):
    return sum(kepler_action(nu[i], Q[i], P[i]) for i in range(len(nu))) - abs(sum(cross(Q[i], P[i])
                                                                                   for i in range(len(nu))))


def moving_hamiltonian(nu, mu, Q, P):
    h = sum(kepler_energy(nu[i], Q[i], P[i]) for i in range(len(nu)))
    Ps = [sum(P[i][k] for i in range(len(nu))) for k in range(2)]
    f = (Ps[0] ** 2 + Ps[1] ** 2) / 2
    for i in range(len(nu)):
        for j in range(i + 1, len(nu)):
            f -= nu[i] * nu[j] / mp.sqrt((Q[i][0] - Q[j][0]) ** 2 + (Q[i][1] - Q[j][1]) ** 2)
    return h + mu * f


def ecc_deficit(u):
    return 1 - mp.sqrt(1 - u * u)


def pair_threshold_lower(nu0, nu1, I0, I1):
    """Lower bound for the frozen pairThreshold nu I 0 1: every feasible (u, v) has a_1 (1 - v) <= a_0 (1 + u) <= 2 a_0,
    so v >= vmin = 1 - 2 a_0/a_1, and the objective >= I_1 D(v) >= I_1 D(vmin) (D increasing on [0, 1])."""
    a0, a1 = (I0 / nu0) ** 2, (I1 / nu1) ** 2
    vmin = 1 - 2 * a0 / a1
    return I1 * ecc_deficit(max(vmin, mp.mpf(0))), vmin


def geometry_report(m: Model):
    nu = [R(x) for x in m.nu]
    I = [m.Lam(i) for i in range(m.n)]
    G = [m.Gam(i) for i in range(m.n)]
    C0 = sum(G)
    Bp, vmin = pair_threshold_lower(nu[0], nu[1], I[0], I[1])
    out = dict(
        mu=float(m.mu), mu_fraction=f"{m.mu.numerator}/{m.mu.denominator}",
        nu=[float(x) for x in m.nu], nu_fraction=[f"{x.numerator}/{x.denominator}" for x in m.nu],
        a=[float(m.axis(i)) for i in range(m.n)], Lam=[float(x) for x in I], Gam=[float(x) for x in G],
        C0=float(C0), B_star=float(min(I)), B_pair_lower=float(Bp), vmin=float(vmin),
        B_equals_Lam0=bool(Bp > I[0] and I[1] > I[0]), beta=float(C0 / I[0]), delta_nominal=float(I[0] - C0),
        years_per_unit=float(m.years_per_unit()),
        periods_units=[float(R(m.P[i]) / R(m.dpy) / m.years_per_unit()) for i in range(m.n)],
        omega=[float((nu[i] / I[i]) ** 3 * nu[i] ** 0) for i in range(m.n)],
    )
    # mean motions n_i = nu_i^3 / Lam_i^3 = a_i^{-3/2}
    out["omega"] = [float(m.axis(i) ** mp.mpf(-1.5)) for i in range(m.n)]
    out["period_ratio"] = out["omega"][0] / out["omega"][1]
    return out


def nominal_state(m: Model):
    """Cartesian (q, p) of the nominal state through the chart, plus checks of the chart dictionary."""
    nu = [R(x) for x in m.nu]
    ch = m.chart_nominal()
    Q, P = [], []
    for i in range(m.n):
        q, p = chart_planet(nu[i], *ch[i])
        Q.append(q)
        P.append(p)
    checks = dict(
        action_residual=[float(kepler_action(nu[i], Q[i], P[i]) - ch[i][2]) for i in range(m.n)],
        prograde=[float(cross(Q[i], P[i])) for i in range(m.n)],
        amd_residual=float(strong_amd(nu, Q, P) - sum(m.Gam(i) for i in range(m.n))),
    )
    return ch, Q, P, checks


if __name__ == "__main__":
    m = Model()
    rep = geometry_report(m)
    for k, v in rep.items():
        print(f"{k:16s} {v}")
    ch, Q, P, chk = nominal_state(m)
    print("chart", [[float(x) for x in c] for c in ch])
    print("q", [[float(x) for x in q] for q in Q])
    print("p", [[float(x) for x in p] for p in P])
    print("checks", chk)
    print("H", float(moving_hamiltonian([R(x) for x in m.nu], R(m.mu), Q, P)))


# ---- the threshold check, in exact rationals (mirror of the proposed Lean `thresholdOk`) ----------------
def threshold_ok(m: Model, Lbox_lo, Lbox_hi, Cbar, r, d):
    """All inputs Fractions.  U = [Lbox_lo - r, Lbox_hi + r].  Decides, exactly:
      (1) U in the chamber: a_0 < a_1 on U  (a_i = (I_i/nu_i)^2, monotone, so corners suffice);
      (2) I_1 >= I_0 on U;
      (3) pairThreshold >= I_1 D(vmin) > max I_0 on U, with vmin = 1 - 2 a_0max/a_1min and D(v) = 1 - sqrt(1 - v^2)
          bounded below by 1 - s for a rational s with s^2 >= 1 - vmin^2;
      (4) delta = min Lam_0(z0) - Cbar > 0 and 3 r <= delta/4 (Omega_B(r) <= r since B = I_0 on U);
      (5) 2 d <= r.
    Returns (ok, details)."""
    nu = m.nu
    lo = [Lbox_lo[i] - r for i in range(2)]
    hi = [Lbox_hi[i] + r for i in range(2)]
    a0max = (hi[0] / nu[0]) ** 2
    a1min = (lo[1] / nu[1]) ** 2
    c1 = a0max < a1min
    c2 = lo[1] >= hi[0]
    vmin = 1 - 2 * a0max / a1min
    # rational s >= sqrt(1 - vmin^2): take a decimal upper approximation and check s^2 >= 1 - vmin^2
    t = 1 - vmin * vmin
    s = Fr(math.ceil(math.sqrt(float(t)) * 10 ** 12) + 1, 10 ** 12)
    assert s * s >= t
    Dlow = 1 - s
    pair_low = lo[1] * Dlow
    c3 = vmin >= 0 and pair_low > hi[0]
    delta = Lbox_lo[0] - Cbar
    c4 = delta > 0 and 3 * r <= delta / 4
    c5 = 2 * d <= r
    det = dict(U_lo=[float(x) for x in lo], U_hi=[float(x) for x in hi], a0max=float(a0max), a1min=float(a1min),
               vmin=float(vmin), pair_lower=float(pair_low), Lam0_max_on_U=float(hi[0]),
               slack=float(pair_low / hi[0]), delta=float(delta), r=float(r), d=float(d),
               checks=dict(chamber=c1, I1_ge_I0=c2, pair_gt_star=c3, budget=c4, d_le_r_half=c5))
    return all([c1, c2, c3, c4, c5]), det


def baseline_box(m: Model, rho=(Fr(1, 10 ** 4), Fr(3, 10 ** 3)), digits=7):
    """Rational box [Lam_hat - rho, Lam_hat + rho] with endpoints rounded outward to `digits` decimals."""
    q = 10 ** digits
    lo = [Fr(math.floor(float(m.Lam(i)) * q), q) - rho[i] for i in range(2)]
    hi = [Fr(math.ceil(float(m.Lam(i)) * q), q) + rho[i] for i in range(2)]
    return lo, hi
