#!/usr/bin/env python3
"""Map SLG13 Table 1 initial data to the secular coordinates and to Table 2.

Steps (SLG13 sections 2-4; LG00 section 2.2 for the precedent):
 1. Table 1 elements -> Poincare variables (Lambda, lambda, xi, eta).  Two readings:
      'poincare'     : the printed elements are Poincare elements (formula (2) applied directly);
      'heliocentric' : they are heliocentric osculating elements (r_j, dr_j/dt, mu_j); the
                       canonical momentum is r~_j = m_j v_j(barycentric), and the Poincare
                       elements are recomputed from (r_j, r~_j/beta_j).
 2. Secular coordinates: the Kolmogorov-like transformations give old = Phi1(Phi2(new)) with
    Phi = exp(L_chi) id, so new = Phi2^{-1}(Phi1^{-1}(old)).  To first order in the masses
    (LG00: "we limit ourselves to consider the correction O(m/m0)")
        z_sec = z - i d(X1 + X2)/d zbar   evaluated at (lambda, L = Lambda - Lambda*, z);
    'second' adds the second-order Lie terms of both inverse maps.
 3. Linear diagonalization: H2 = (1/2) sum A_ij (xi_i xi_j + eta_i eta_j); A = O diag(nu) O^T,
    (x, y) = (O^T xi, O^T eta), columns ordered by |nu| decreasing and signed to match Table 2.
Outputs the comparison with Table 2 and with the radii printed in SLG13 eq. (24).
"""
from __future__ import annotations

import argparse
import json
import math
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import mpmath
import numpy as np

from sjsu_common import Backend, TABLE1, TABLE2, SLG13_RADII, physical_constants
from sparse import SP, bracket


def elements(ic, consts):
    """Return Poincare (Lambda, lambda, xi, eta) lists (mpf) for the Table 1 data."""
    a = [mpmath.mpf(s) for s in TABLE1['a']]
    e = [mpmath.mpf(s) for s in TABLE1['e']]
    M = [mpmath.mpf(s) for s in TABLE1['M']]
    om = [mpmath.mpf(s) for s in TABLE1['omega']]
    beta, mu, m, m0 = consts['beta'], consts['mu'], consts['m'], consts['m0']
    if ic == 'heliocentric':
        pos, vel = [], []
        for j in range(3):
            E = M[j]
            for _ in range(60):
                E = E - (E - e[j] * mpmath.sin(E) - M[j]) / (1 - e[j] * mpmath.cos(E))
            n = mpmath.sqrt(mu[j] / a[j] ** 3)
            dE = n / (1 - e[j] * mpmath.cos(E))
            r = mpmath.mpc(a[j] * (mpmath.cos(E) - e[j]), a[j] * mpmath.sqrt(1 - e[j] ** 2) * mpmath.sin(E))
            v = mpmath.mpc(-a[j] * mpmath.sin(E) * dE, a[j] * mpmath.sqrt(1 - e[j] ** 2) * mpmath.cos(E) * dE)
            rot = mpmath.exp(1j * om[j])
            pos.append(r * rot); vel.append(v * rot)
        mtot = m0 + sum(m)
        vsun = -sum(m[j] * vel[j] for j in range(3)) / mtot
        a, e, M, om = [], [], [], []
        for j in range(3):
            p = m[j] * (vel[j] + vsun)
            v = p / beta[j]
            r = pos[j]
            rn = abs(r)
            aj = 1 / (2 / rn - abs(v) ** 2 / mu[j])
            h = (mpmath.conj(r) * v).imag
            ecc_vec = (v * mpmath.mpc(0, -h)) / mu[j] - r / rn   # Laplace-Runge-Lenz / mu (planar)
            ej = abs(ecc_vec)
            omj = mpmath.atan2(ecc_vec.imag, ecc_vec.real)
            # eccentric and mean anomaly
            cosE = (1 - rn / aj) / ej
            sinE = (r.real * v.real + r.imag * v.imag) / (ej * mpmath.sqrt(mu[j] * aj))
            Ej = mpmath.atan2(sinE, cosE)
            a.append(aj); e.append(ej); om.append(omj); M.append(Ej - ej * mpmath.sin(Ej))
    Lam = [beta[j] * mpmath.sqrt(mu[j] * a[j]) for j in range(3)]
    lam = [M[j] + om[j] for j in range(3)]
    Gam = [Lam[j] * (1 - mpmath.sqrt(1 - e[j] ** 2)) for j in range(3)]
    xi = [mpmath.sqrt(2 * Gam[j]) * mpmath.cos(om[j]) for j in range(3)]
    eta = [-mpmath.sqrt(2 * Gam[j]) * mpmath.sin(om[j]) for j in range(3)]
    return Lam, lam, xi, eta


def evaluate(sp: SP, lam, L, z):
    bk = sp.bk
    tot = mpmath.mpc(0)
    zb = [mpmath.conj(x) for x in z]
    for k, e, l, cc in zip(sp.K, sp.E, sp.L, sp.C):
        t = bk.to_mpc(cc) * mpmath.expj(int(k[0]) * lam[0] + int(k[1]) * lam[1] + int(k[2]) * lam[2])
        for j in range(3):
            t *= z[j] ** int(e[2 * j]) * zb[j] ** int(e[2 * j + 1])
        if l > 0:
            t *= L[int(l) - 1]
        tot += t
    return tot


def coord(bk, j):
    E = np.zeros((1, 6)); E[0, 2 * j] = 1
    return SP(bk, np.zeros((1, 3)), E, np.zeros(1), bk.array_from([bk.real(1)]))


def inverse_map(X1, X2, lam, L, z, order=1, D=18):
    """z_new from z_old: Phi2^{-1}(Phi1^{-1}(old)), Lie series of the given order."""
    bk = X1.bk
    out = []
    # Phi^{-1} = exp(-L_X) id.  Compose: first apply Phi1^{-1} to the old point, then Phi2^{-1}.
    def apply(X, point_z):
        res = []
        for j in range(3):
            g = coord(bk, j)
            val = evaluate(g, lam, L, point_z)
            term = g
            sgn = -1
            fact = 1
            for s in range(1, order + 1):
                term = bracket(X, term, None, D, 1, None)
                fact *= s
                val += sgn ** s * evaluate(term, lam, L, point_z) / fact
            res.append(val)
        return res
    z1 = apply(X1, z)
    z2 = apply(X2, z1)
    return z2


def diagonalizer(sec_quad: SP):
    """A (3x3) from the secular quadratic part sum A_ij z_i zbar_j; eigen-decomposition."""
    A = np.zeros((3, 3))
    for e, cc in zip(sec_quad.E, sec_quad.C):
        i = [j for j in range(3) if e[2 * j] == 1][0]
        k = [j for j in range(3) if e[2 * j + 1] == 1][0]
        A[i, k] += float(np.real(cc))
    w, V = np.linalg.eigh(A)
    order = np.argsort(-np.abs(w))
    return A, w[order], V[:, order]


def table2_compare(xs, ys, nu):
    x2 = [float(s) for s in TABLE2['x0']]
    y2 = [float(s) for s in TABLE2['y0']]
    nu2 = [float(s) for s in TABLE2['nu']]
    R2 = [math.hypot(x2[j], y2[j]) for j in range(3)]
    R = [math.hypot(xs[j], ys[j]) for j in range(3)]
    rows = []
    for j in range(3):
        rows.append({'mode': j + 1, 'nu': nu[j], 'nu_table2': nu2[j], 'x': xs[j], 'x_table2': x2[j],
                     'y': ys[j], 'y_table2': y2[j], 'R': R[j], 'R_table2': R2[j],
                     'R_eq24': float(SLG13_RADII[j])})
    return rows


def run(astar, ic='poincare', order=1, backend='ld', D=8, log=print):
    from secular import compute_secular
    bk = Backend(backend)
    out = compute_secular(astar, bk, D=D, res=False, log=lambda *a: None, return_intermediates=True)
    c = out['consts']
    sec = SP.concat(bk, [out['first'], out['second_chi1'], out['second_chi2']]).consolidate()
    quad = sec.select(sec.degree() == 2)
    A, nu, V = diagonalizer(quad)
    Lam, lam, xi, eta = elements(ic, c)
    L = [Lam[j] - c['Lambda'][j] for j in range(3)]
    z = [(xi[j] - 1j * eta[j]) / mpmath.sqrt(2) for j in range(3)]
    zs = inverse_map(out['X1'], out['X2'], lam, L, z, order=order, D=D) if order > 0 else z
    xis = np.array([float(mpmath.sqrt(2) * zz.real) for zz in zs])
    etas = np.array([float(-mpmath.sqrt(2) * zz.imag) for zz in zs])
    x = V.T @ xis
    y = V.T @ etas
    # sign convention: make x_j agree in sign with Table 2
    x2 = [float(s) for s in TABLE2['x0']]
    for j in range(3):
        if x[j] * x2[j] < 0:
            V[:, j] *= -1; x[j] *= -1; y[j] *= -1
    rows = table2_compare(x, y, nu)
    return {'astar': [mpmath.nstr(v, 18) for v in astar], 'ic': ic, 'order': order,
            'L_over_Lambda': [float(L[j] / c['Lambda'][j]) for j in range(3)],
            'xi_eta_poincare': [float(v) for v in xi + eta],
            'xi_eta_secular': list(map(float, xis)) + list(map(float, etas)),
            'A': A.tolist(), 'O': V.tolist(), 'rows': rows}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--astar', nargs=3, required=True)
    ap.add_argument('--ic', default='poincare', choices=['poincare', 'heliocentric'])
    ap.add_argument('--order', type=int, default=1)
    ap.add_argument('--json')
    args = ap.parse_args()
    mpmath.mp.dps = 40
    res = run([mpmath.mpf(s) for s in args.astar], args.ic, args.order)
    for r in res['rows']:
        print(f"mode {r['mode']}: nu {r['nu']:.10e} (T2 {r['nu_table2']:.10e})  x {r['x']:+.10e} (T2 {r['x_table2']:+.10e})"
              f"  y {r['y']:+.10e} (T2 {r['y_table2']:+.10e})  R {r['R']:.10e} (T2 {r['R_table2']:.10e}; eq24 {r['R_eq24']:.10e})")
    print('L/Lambda* at Table 1:', res['L_over_Lambda'])
    if args.json:
        with open(args.json, 'w') as fh:
            json.dump(res, fh, indent=1)


if __name__ == '__main__':
    main()
