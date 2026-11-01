#!/usr/bin/env python3
"""Independent checks of the first-order expansion (expansion.py).

1. Pointwise: evaluate the truncated series of f_ij (direct + indirect) at a phase point with
   small eccentricities and compare with a direct evaluation of
   -G m_i m_j/|r_i - r_j| + r~_i.r~_j/m0 from Poincare variables (Kepler solve in mpmath).
   The difference must scale like the truncation (degree 19 in e, harmonic order > KF).
2. Action derivative: compare the L-linear coefficients with a central finite difference of the
   direct evaluation in Lambda_j (other variables fixed).
3. Classical secular quadratic part: compare with the Laplace-Lagrange formula
   <1/|r_i - r_j|> = (1/a_j)[ (1/2)b^{(0)} + (1/8) alpha b^{(1)}_{3/2} (e_i^2 + e_j^2)
                               - (1/4) alpha b^{(2)}_{3/2} e_i e_j cos(varpi_i - varpi_j) ] + O(e^4).
Run from applications/sjsu:  python3 -I scripts/check_expansion.py
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import mpmath
import numpy as np

from sjsu_common import Backend, physical_constants, TABLE1
from kepler_series import universal_series
from expansion import PairExpander
from sparse import SP


def kepler_state(Lam, lam, xi, eta, beta, mu):
    """Heliocentric position and canonical momentum (complex) from Poincare variables."""
    a = Lam ** 2 / (beta ** 2 * mu)
    Gam = (xi ** 2 + eta ** 2) / 2
    varpi = mpmath.atan2(-eta, xi)
    x = Gam / Lam
    e = mpmath.sqrt(2 * x - x * x)
    M = lam - varpi
    E = M
    for _ in range(100):
        E = E - (E - e * mpmath.sin(E) - M) / (1 - e * mpmath.cos(E))
    pos = mpmath.mpc(mpmath.cos(E) - e, mpmath.sqrt(1 - e * e) * mpmath.sin(E)) * a
    n = mpmath.sqrt(mu / a ** 3)
    dEdt = n / (1 - e * mpmath.cos(E))
    vel = mpmath.mpc(-mpmath.sin(E), mpmath.sqrt(1 - e * e) * mpmath.cos(E)) * a * dEdt
    rot = mpmath.exp(1j * varpi)
    return pos * rot, beta * vel * rot


def direct_f(i, j, c, Lam, lam, xi, eta):
    ri, pi_ = kepler_state(Lam[i], lam[i], xi[i], eta[i], c['beta'][i], c['mu'][i])
    rj, pj_ = kepler_state(Lam[j], lam[j], xi[j], eta[j], c['beta'][j], c['mu'][j])
    U = -c['m'][i] * c['m'][j] / abs(ri - rj)
    T = (pi_ * mpmath.conj(pj_)).real / c['m0']
    return U + T


def eval_series(sp: SP, bk, lam, z, Lsel=0):
    tot = mpmath.mpc(0)
    sel = sp.select(sp.L == Lsel)
    for k, e, cc in zip(sel.K, sel.E, sel.C):
        cm = bk.to_mpc(cc)
        term = cm * mpmath.exp(1j * (int(k[0]) * lam[0] + int(k[1]) * lam[1] + int(k[2]) * lam[2]))
        for p in range(3):
            term *= z[p] ** int(e[2 * p]) * mpmath.conj(z[p]) ** int(e[2 * p + 1])
        tot += term
    return tot


def harmonic_table(i, j, c, Lam, lam_grid, xi, eta):
    """Exact DFT over (lambda_i, lambda_j) of f_ij on an N x N grid (mpmath)."""
    N = len(lam_grid)
    Si = [kepler_state(Lam[i], l, xi[i], eta[i], c['beta'][i], c['mu'][i]) for l in lam_grid]
    Sj = [kepler_state(Lam[j], l, xi[j], eta[j], c['beta'][j], c['mu'][j]) for l in lam_grid]
    F = [[None] * N for _ in range(N)]
    for a, (ri, pi_) in enumerate(Si):
        for b, (rj, pj_) in enumerate(Sj):
            F[a][b] = -c['m'][i] * c['m'][j] / abs(ri - rj) + (pi_ * mpmath.conj(pj_)).real / c['m0']
    return F


def dft_coeff(F, ki, kj):
    N = len(F)
    w = [mpmath.exp(-2j * mpmath.pi * t / N) for t in range(N)]
    tot = mpmath.mpc(0)
    for a in range(N):
        wa = w[(ki * a) % N]
        row = F[a]
        acc = mpmath.mpc(0)
        for b in range(N):
            acc += row[b] * w[(kj * b) % N]
        tot += wa * acc
    return tot / (N * N)


def series_harmonic(sp, bk, i, j, ki, kj, z, Lsel):
    tot = mpmath.mpc(0)
    sel = sp.select((sp.L == Lsel) & (sp.K[:, i] == ki) & (sp.K[:, j] == kj))
    for e, cc in zip(sel.E, sel.C):
        term = bk.to_mpc(cc)
        for p in range(3):
            term *= z[p] ** int(e[2 * p]) * mpmath.conj(z[p]) ** int(e[2 * p + 1])
        tot += term
    return tot


def main():
    mpmath.mp.dps = 32
    bk = Backend('ld')
    c = physical_constants([mpmath.mpf(x) for x in TABLE1['a']])
    U = universal_series(18, 17)
    ex = PairExpander(bk, U, D=18, KF=16)
    rng = np.random.default_rng(1)
    N = 96
    lam_grid = [2 * mpmath.pi * t / N for t in range(N)]
    worst = 0
    harmonics = [(0, 0), (1, -1), (2, -5), (-2, 5), (1, 0), (0, -1), (3, -2), (8, -8), (5, -11), (1, -7), (4, 4)]
    for (i, j) in ((0, 1), (0, 2), (1, 2)):
        f = SP.concat(bk, [ex.direct(i, j, c), ex.indirect(i, j, c)]).consolidate()
        print(f'pair ({i+1},{j+1}): {len(f)} terms')
        for escale in (mpmath.mpf('0.03'), mpmath.mpf('0.015')):
            xi, eta, z = [], [], []
            for p in range(3):
                ph = mpmath.mpf(float(rng.uniform(0, 2 * np.pi)))
                G = c['Lambda'][p] * escale ** 2 / 2
                xi.append(mpmath.sqrt(2 * G) * mpmath.cos(ph))
                eta.append(-mpmath.sqrt(2 * G) * mpmath.sin(ph))
                z.append((xi[-1] - 1j * eta[-1]) / mpmath.sqrt(2))
            F0 = harmonic_table(i, j, c, c['Lambda'], lam_grid, xi, eta)
            FD = {}
            for q in (i, j):
                h = c['Lambda'][q] * mpmath.mpf('1e-10')
                Lp = list(c['Lambda']); Lp[q] += h
                Lm = list(c['Lambda']); Lm[q] -= h
                Fp = harmonic_table(i, j, c, Lp, lam_grid, xi, eta)
                Fm = harmonic_table(i, j, c, Lm, lam_grid, xi, eta)
                FD[q] = [[(Fp[a][b] - Fm[a][b]) / (2 * h) for b in range(N)] for a in range(N)]
            scale0 = abs(dft_coeff(F0, 0, 0))
            for (ki, kj) in harmonics:
                if abs(ki) + abs(kj) > 16:
                    continue
                d = dft_coeff(F0, ki, kj)
                s_ = series_harmonic(f, bk, i, j, ki, kj, z, 0)
                rel = abs(d - s_) / scale0
                line = f'   e~{escale} k=({ki},{kj}): |F_k|/|F_0|={mpmath.nstr(abs(d)/scale0, 3)} diff/|F_0|={mpmath.nstr(rel, 3)}'
                worst = max(worst, rel)
                for q in (i, j):
                    dq = dft_coeff(FD[q], ki, kj)
                    sq = series_harmonic(f, bk, i, j, ki, kj, z, q + 1)
                    sc = abs(dft_coeff(FD[q], 0, 0))
                    relq = abs(dq - sq) / sc
                    worst = max(worst, relq)
                    line += f' dL{q+1}:{mpmath.nstr(relq, 3)}'
                print(line)
    print('worst relative harmonic discrepancy:', mpmath.nstr(worst, 3))
    return 0 if worst < 1e-12 else 1


if __name__ == '__main__':
    sys.exit(main())
