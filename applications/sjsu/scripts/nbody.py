#!/usr/bin/env python3
"""Planar Sun-Jupiter-Saturn-Uranus N-body integration and averaged semi-major axes.

SLG13 section 2: "we perform a long-term numerical integration of Newton's equations starting
from the initial conditions related to the data reported in Table 1.  After having computed
(a1*, a2*, a3*) [the average values of the semi-major axes during the evolution], we determine
the values Lambda* via the first equation in (2)."  The integration length and the exact
definition of "semi-major axis" are not stated; we report both

  a_P : Poincare (canonical heliocentric) semi-major axis, from r_j and r~_j/beta_j with
        mu_j = G(m0 + m_j)  (the variable whose average defines Lambda* through eq. (2));
  a_H : classical heliocentric osculating semi-major axis, from r_j and dr_j/dt, mu_j.

Initial-data interpretations of Table 1 ("usual heliocentric planar orbital elements"):
  'poincare'    : the elements are Poincare elements (formula (2) applied directly);
  'heliocentric': the elements are heliocentric osculating elements (r_j, dr_j/dt, mu_j);
                  momenta r~_j = m_j * barycentric velocity.

Integrator: Wisdom-Holman map in democratic heliocentric splitting
  H = sum_j [|p_j|^2/(2 m_j) - G m0 m_j/|r_j|] + |sum p_j|^2/(2 m0) - sum_{i<j} G m_i m_j/|r_i - r_j|,
(exactly the SLG13 Hamiltonian (1) in the same canonical variables), composed to fourth order
with Yoshida's triple jump.  Float64 numpy; energy drift is reported.
Usage: python3 -I nbody.py --years 1e6 --dt 0.5 --ic poincare --out results.json
"""
import argparse
import json
import math
import os
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np

from sjsu_common import TABLE1, MASS_RECIPROCALS
from fractions import Fraction

TWO_PI = 2 * math.pi
M0 = 4 * math.pi ** 2
MJ = np.array([M0 / float(Fraction(r)) for r in MASS_RECIPROCALS])
MU = M0 + MJ                     # G (m0 + m_j)
BETA = M0 * MJ / (M0 + MJ)


def elements_to_state(a, e, M, om, mu):
    E = M.copy()
    for _ in range(50):
        E = E - (E - e * np.sin(E) - M) / (1 - e * np.cos(E))
    cE, sE = np.cos(E), np.sin(E)
    sq = np.sqrt(1 - e * e)
    x = a * (cE - e); y = a * sq * sE
    n = np.sqrt(mu / a ** 3)
    dE = n / (1 - e * cE)
    vx = -a * sE * dE; vy = a * sq * cE * dE
    co, so = np.cos(om), np.sin(om)
    r = np.stack([co * x - so * y, so * x + co * y], axis=1)
    v = np.stack([co * vx - so * vy, so * vx + co * vy], axis=1)
    return r, v


def initial_state(ic):
    a = np.array([float(s) for s in TABLE1['a']])
    e = np.array([float(s) for s in TABLE1['e']])
    M = np.array([float(s) for s in TABLE1['M']])
    om = np.array([float(s) for s in TABLE1['omega']])
    r, v = elements_to_state(a, e, M, om, MU)
    if ic == 'poincare':
        p = BETA[:, None] * v                       # r~_j = beta_j v_Kepler
    elif ic == 'heliocentric':
        mtot = M0 + MJ.sum()
        vsun = -(MJ[:, None] * v).sum(axis=0) / mtot  # barycentric Sun velocity
        p = MJ[:, None] * (v + vsun)                  # m_j * barycentric velocity
    else:
        raise ValueError(ic)
    return r, p


def kepler_drift(r, v, mu, dt):
    """Exact Kepler drift (elliptic) for each planet, f and g functions; vectorized."""
    rn = np.sqrt((r * r).sum(1))
    v2 = (v * v).sum(1)
    a = 1.0 / (2.0 / rn - v2 / mu)
    n = np.sqrt(mu / a ** 3)
    rv = (r * v).sum(1)
    ecE = 1 - rn / a
    esE = rv / np.sqrt(mu * a)
    dM = n * dt
    x = dM.copy()
    for _ in range(30):
        s, c = np.sin(x), np.cos(x)
        f = x - ecE * s + esE * (1 - c) - dM
        fp = 1 - ecE * c + esE * s
        dx = -f / fp
        x += dx
        if np.max(np.abs(dx)) < 1e-15:
            break
    s, c = np.sin(x), np.cos(x)
    rnew = a * (1 - ecE * c + esE * s)
    fF = 1 + a / rn * (c - 1)
    gG = dt + (s - x) / n
    fd = -a * a * n * s / (rn * rnew)
    gd = 1 + a / rnew * (c - 1)
    r2 = fF[:, None] * r + gG[:, None] * v
    v2_ = fd[:, None] * r + gd[:, None] * v
    return r2, v2_


def interaction_kick(r, p, dt):
    acc = np.zeros_like(r)
    for i in range(3):
        for j in range(i + 1, 3):
            d = r[i] - r[j]
            d3 = (d @ d) ** 1.5
            f = MJ[i] * MJ[j] * d / d3
            acc[i] -= f
            acc[j] += f
    return p + dt * acc


def sun_drift(r, p, dt):
    return r + dt * p.sum(0) / M0


def dh_step(r, p, dt):
    r = sun_drift(r, p, dt / 2)
    p = interaction_kick(r, p, dt / 2)
    v = p / MJ[:, None]
    r, v = kepler_drift(r, v, M0 * np.ones(3), dt)
    p = v * MJ[:, None]
    p = interaction_kick(r, p, dt / 2)
    r = sun_drift(r, p, dt / 2)
    return r, p


W1 = 1.0 / (2.0 - 2.0 ** (1.0 / 3.0))
W0 = 1.0 - 2.0 * W1


def step4(r, p, dt):
    r, p = dh_step(r, p, W1 * dt)
    r, p = dh_step(r, p, W0 * dt)
    r, p = dh_step(r, p, W1 * dt)
    return r, p


def energy(r, p):
    T = (p * p).sum(1) / (2 * MJ)
    U = -M0 * MJ / np.sqrt((r * r).sum(1))
    Ps = p.sum(0)
    E = T.sum() + U.sum() + (Ps @ Ps) / (2 * M0)
    for i in range(3):
        for j in range(i + 1, 3):
            d = r[i] - r[j]
            E -= MJ[i] * MJ[j] / math.sqrt(d @ d)
    return E


def semimajor(r, p):
    rn = np.sqrt((r * r).sum(1))
    vP = p / BETA[:, None]
    aP = 1.0 / (2.0 / rn - (vP * vP).sum(1) / MU)
    vH = p / MJ[:, None] + p.sum(0) / M0          # dr_j/dt = dH/dp_j
    aH = 1.0 / (2.0 / rn - (vH * vH).sum(1) / MU)
    return aP, aH


def poincare_xieta(r, p):
    """Osculating Poincare (xi_j, eta_j) from (r_j, r~_j/beta_j), mu_j: returns array (2, 3)."""
    v = p / BETA[:, None]
    rn = np.sqrt((r * r).sum(1))
    a = 1.0 / (2.0 / rn - (v * v).sum(1) / MU)
    h = r[:, 0] * v[:, 1] - r[:, 1] * v[:, 0]
    ex = (v[:, 1] * h) / MU - r[:, 0] / rn
    ey = (-v[:, 0] * h) / MU - r[:, 1] / rn
    e = np.sqrt(ex * ex + ey * ey)
    Lam = BETA * np.sqrt(MU * a)
    G = Lam * (1 - np.sqrt(1 - e * e))
    s = np.sqrt(2 * G) / np.where(e > 0, e, 1)
    return np.array([s * ex, -s * ey])      # xi = sqrt(2 Gamma) cos varpi, eta = -sqrt(2 Gamma) sin varpi


def mean_longitude(r, p):
    """Poincare mean longitude lambda = M + varpi from (r_j, r~_j/beta_j), mu_j."""
    v = p / BETA[:, None]
    rn = np.sqrt((r * r).sum(1))
    a = 1.0 / (2.0 / rn - (v * v).sum(1) / MU)
    rv = (r * v).sum(1)
    ecE = 1 - rn / a
    esE = rv / np.sqrt(MU * a)
    h = r[:, 0] * v[:, 1] - r[:, 1] * v[:, 0]
    ex = (v[:, 1] * h) / MU - r[:, 0] / rn
    ey = (-v[:, 0] * h) / MU - r[:, 1] / rn
    varpi = np.arctan2(ey, ex)
    E = np.arctan2(esE, ecE)
    return E - esE + varpi          # M = E - e sin E


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--years', type=float, default=1e5)
    ap.add_argument('--dt', type=float, default=0.5)
    ap.add_argument('--ic', default='poincare', choices=['poincare', 'heliocentric'])
    ap.add_argument('--checkpoints', type=float, nargs='*', default=[1e3, 1e4, 3e4, 1e5, 3e5, 1e6, 3e6])
    ap.add_argument('--out')
    ap.add_argument('--sample', type=float, default=0.0, help='sampling step (yr) of the osculating Poincare (xi, eta)')
    ap.add_argument('--sample-out', help='npz file for the sampled (t, xi, eta)')
    args = ap.parse_args()
    r, p = initial_state(args.ic)
    E0 = energy(r, p)
    nsteps = int(round(args.years / args.dt))
    sumP = np.zeros(3); sumH = np.zeros(3)
    aP, aH = semimajor(r, p)
    # trapezoid in time: weight 1/2 at the ends
    sumP += aP / 2; sumH += aH / 2
    chk = sorted(c for c in args.checkpoints if c <= args.years + 1e-9)
    every = int(round(args.sample / args.dt)) if args.sample > 0 else 0
    samples = [poincare_xieta(r, p)] if every else []
    lam_prev = mean_longitude(r, p)
    lam_unw = lam_prev.copy()
    St = 0.0; St2 = 0.0; Sl = np.zeros(3); Stl = np.zeros(3); Sn = 0
    rows = []
    t0 = time.time()
    ci = 0
    maxdE = 0.0
    for k in range(1, nsteps + 1):
        r, p = step4(r, p, args.dt)
        aP, aH = semimajor(r, p)
        sumP += aP; sumH += aH
        t = k * args.dt
        lam = mean_longitude(r, p)
        d = np.mod(lam - lam_prev + np.pi, 2 * np.pi) - np.pi
        lam_unw = lam_unw + d
        lam_prev = lam
        St += t; St2 += t * t; Sl += lam_unw; Stl += t * lam_unw; Sn += 1
        if every and k % every == 0:
            samples.append(poincare_xieta(r, p))
        if ci < len(chk) and t >= chk[ci] - 1e-9:
            dE = abs(energy(r, p) / E0 - 1)
            maxdE = max(maxdE, dE)
            avgP = (sumP - aP / 2) / k
            avgH = (sumH - aH / 2) / k
            nmm = (Sn * Stl - St * Sl) / (Sn * St2 - St * St)     # least-squares slope of lambda(t)
            rows.append({'t': t, 'aP_mean': [repr(float(x)) for x in avgP], 'aH_mean': [repr(float(x)) for x in avgH],
                         'mean_motion': [repr(float(x)) for x in nmm],
                         'two_n1_minus_five_n2': float(2 * nmm[0] - 5 * nmm[1]),
                         'n1_minus_7n3': float(nmm[0] - 7 * nmm[2]),
                         'three_body': float(3 * nmm[0] - 5 * nmm[1] - 7 * nmm[2]),
                         'rel_energy_error': dE})
            print(f't={t:.0f}  <aP>={avgP}  <aH>={avgH}  n={nmm}  2n1-5n2={2*nmm[0]-5*nmm[1]:.8f} '
                  f'3n1-5n2-7n3={3*nmm[0]-5*nmm[1]-7*nmm[2]:.8f}  dE/E={dE:.2e}  ({time.time()-t0:.0f}s)', flush=True)
            ci += 1
    res = {'ic': args.ic, 'dt': args.dt, 'years': args.years, 'integrator': 'WH-DH Yoshida4, float64',
           'masses': {'m0': M0, 'm': MJ.tolist()}, 'checkpoints': rows, 'max_rel_energy_error': maxdE,
           'cpu_seconds': time.process_time()}
    if args.out:
        with open(args.out, 'w') as fh:
            json.dump(res, fh, indent=1)
    if every and args.sample_out:
        arr = np.array(samples)
        np.savez_compressed(args.sample_out, dt=every * args.dt, xi=arr[:, 0, :], eta=arr[:, 1, :])


if __name__ == '__main__':
    main()
