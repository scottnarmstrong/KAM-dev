"""Planar SJSU model (SLG13 eq. (1), canonical heliocentric Poincare variables) with Taylor jets in the nine slow
variables (dLambda_J,S,U, dxi_J,S,U, deta_J,S,U) on grids of the fast mean longitudes (research scratch).

Units AU, yr, G = 1, m0 = 4 pi^2; masses m0/(1047.355, 3498.5, 22902.98) (same as harmonics.py of the research
plan).  Positions use the eccentric longitude F (lambda = F - k sin F + h cos F, k + i h = e e^{i varpi}), which is
analytic in (xi, eta) at e = 0, so jets have no 1/e cancellations.
  H = sum_j [|p_j|^2/(2 beta_j) - beta_j mu_j/|r_j|] + sum_{i<j} [p_i.p_j/m0 - m_i m_j/|r_i - r_j|].
"""
from __future__ import annotations

import json
import math
import os

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
DATA = os.environ.get('SJSU_DATA') or os.path.abspath(os.path.join(HERE, '..', '..', '..', 'applications', 'sjsu',
                                                                    'validation'))
M0 = 4 * math.pi ** 2
MREC = np.array([1047.355, 3498.5, 22902.98])
MJ = M0 / MREC
MU = M0 + MJ
BETA = M0 * MJ / (M0 + MJ)
_astar = json.load(open(os.path.join(DATA, 'astar.json')))
A_STAR = np.array([float(x) for x in _astar['astar']])
N_NB = np.array([float(x) for x in _astar['measured_mean_motions_1e5yr']])
LAM_STAR = BETA * np.sqrt(MU * A_STAR)
N_KEP_STAR = BETA ** 3 * MU ** 2 / LAM_STAR ** 3
HESS_STAR = -3 * N_KEP_STAR / LAM_STAR
DN_STAR = N_NB - N_KEP_STAR
_smap = json.load(open(os.path.join(DATA, 'table2_map_poincare_order1.json')))
XE = np.array(_smap['xi_eta_secular'])
XI0, ETA0 = XE[:3].copy(), XE[3:].copy()
PAIRS = [(0, 1), (0, 2), (1, 2)]


def n_kep(Lam):
    return BETA ** 3 * MU ** 2 / np.asarray(Lam) ** 3


def planet(B, j, slow, nlam, vmap=None):
    """Jets (X, Y, PX, PY) of planet j on nlam mean longitudes, laid out on axis j of the (J, S, U) grid.
    vmap(j) -> (variable of Lambda_j or None for a constant, variable of xi_j, variable of eta_j)."""
    Lam0, xi0, eta0 = slow[0][j], slow[1][j], slow[2][j]
    shape = [1, 1, 1]; shape[j] = nlam
    from jets import DTYPE
    lam = (2 * np.pi * np.arange(nlam, dtype=DTYPE) / nlam).reshape(shape)
    one = np.ones(shape, dtype=DTYPE)
    vL, vX, vE = (j, 3 + j, 6 + j) if vmap is None else vmap(j)
    L = B.const(Lam0 * one) if vL is None else B.affine(Lam0 * one, vL)
    X = B.affine(xi0 * one, vX)
    E = B.affine(eta0 * one, vE)
    mul, rec, pw = B.mul, B.recip, B.powr
    D = B.D
    Linv = rec(L)
    a = mul(L, L, D) / (BETA[j] ** 2 * MU[j])
    Gam = 0.5 * (mul(X, X, D) + mul(E, E, D))
    g = mul(Gam, Linv, D)
    s = pw(mul(B.const(one) - 0.5 * g, Linv, D), 0.5)
    k = mul(s, X, D)
    h = -mul(s, E, D)
    e2 = mul(k, k, D) + mul(h, h, D)
    b = rec(B.const(one) + pw(B.const(one) - e2, 0.5))
    # Kepler: float solution, then jet Newton steps
    k0, h0 = k[0], h[0]
    F0 = lam.copy() * one
    for _ in range(60):
        F0 = F0 - (F0 - k0 * np.sin(F0) + h0 * np.cos(F0) - lam) / (1 - k0 * np.cos(F0) - h0 * np.sin(F0))
    F = B.const(F0)
    for _ in range(4):
        sF, cF = B.sincos(F)
        num = F - mul(k, sF, D) + mul(h, cF, D) - B.const(lam * one)
        den = B.const(one) - mul(k, cF, D) - mul(h, sF, D)
        F = F - mul(num, rec(den), D)
    sF, cF = B.sincos(F)
    den = B.const(one) - mul(k, cF, D) - mul(h, sF, D)
    hkb = mul(mul(h, k, D), b, D)
    one_h2b = B.const(one) - mul(mul(h, h, D), b, D)
    one_k2b = B.const(one) - mul(mul(k, k, D), b, D)
    Xp = mul(a, mul(one_h2b, cF, D) + mul(hkb, sF, D) - k, D)
    Yp = mul(a, mul(one_k2b, sF, D) + mul(hkb, cF, D) - h, D)
    # a n / den with n = sqrt(mu) a^{-3/2}: a n = sqrt(mu) a^{-1/2}
    fac = math.sqrt(MU[j]) * mul(pw(a, -0.5), rec(den), D)
    VX = mul(fac, mul(hkb, cF, D) - mul(one_h2b, sF, D), D)
    VY = mul(fac, mul(one_k2b, cF, D) - mul(hkb, sF, D), D)
    return Xp, Yp, BETA[j] * VX, BETA[j] * VY


def pair_jets(B, slow, NG, vmap=None):
    """Grid values (real jets) of f_ij(lambda_i, lambda_j), shapes (M, NJ|1, NS|1, NU|1)."""
    P = [planet(B, j, slow, NG[j], vmap) for j in range(3)]
    D = B.D
    out = {}
    for (i, j) in PAIRS:
        Xi, Yi, PXi, PYi = P[i]
        Xj, Yj, PXj, PYj = P[j]
        dx = Xi - Xj
        dy = Yi - Yj
        d2 = B.mul(dx, dx, D) + B.mul(dy, dy, D)
        inv = B.powr(d2, -0.5)
        pp = B.mul(PXi, PXj, D) + B.mul(PYi, PYj, D)
        out[(i, j)] = pp / M0 - MJ[i] * MJ[j] * inv
    return out


def pair_f_float(i, j, slow, NG):
    """Plain float reference (the research plan's harmonics.pair_f, with the classical ellipse)."""
    def pog(jj, n):
        Lam, xi, eta = slow[0][jj], slow[1][jj], slow[2][jj]
        a = Lam ** 2 / (BETA[jj] ** 2 * MU[jj])
        G = 0.5 * (xi * xi + eta * eta)
        e = math.sqrt(max(0.0, 1 - (1 - G / Lam) ** 2))
        vp = math.atan2(-eta, xi)
        lam = 2 * np.pi * np.arange(n) / n
        M = lam - vp
        E = M.copy()
        for _ in range(60):
            E = E - (E - e * np.sin(E) - M) / (1 - e * np.cos(E))
        cE, sE = np.cos(E), np.sin(E)
        sq = math.sqrt(1 - e * e)
        x, y = a * (cE - e), a * sq * sE
        nn = math.sqrt(MU[jj] / a ** 3)
        dE = nn / (1 - e * cE)
        vx, vy = -a * sE * dE, a * sq * cE * dE
        c, s = math.cos(vp), math.sin(vp)
        return np.stack([c * x - s * y, s * x + c * y]), BETA[jj] * np.stack([c * vx - s * vy, s * vx + c * vy])
    ri, pi_ = pog(i, NG[i]); rj, pj = pog(j, NG[j])
    dx = ri[0][:, None] - rj[0][None, :]
    dy = ri[1][:, None] - rj[1][None, :]
    pp = pi_[0][:, None] * pj[0][None, :] + pi_[1][:, None] * pj[1][None, :]
    return pp / M0 - MJ[i] * MJ[j] / np.sqrt(dx * dx + dy * dy)
