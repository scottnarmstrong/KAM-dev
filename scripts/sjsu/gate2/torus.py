#!/usr/bin/env python3
"""Stage 1: near-torus approximate integrals about constant reference actions (floating).

Run with /usr/bin/python3 (numpy). Pipeline:
  1. Fourier-Taylor expansion of the modal Hamiltonian about reference actions I* (ft.py).
  2. Kolmogorov-type steps (frequency left free): remove angle terms of p-degree 0 and 1.
  3. Birkhoff steps around the torus: remove angle terms of p-degree 2..LB.
  4. F_j = p_j pulled back through all generators (literal Fourier-Taylor functions of (p, q)).
  5. Recentre I* so that F(nominal point) ~ 0, and repeat.
  6. Torus graph tau(phi): solve F(tau(phi), phi) = c on a phi-grid (c = F(nominal)).
The expansion about a constant I* must straddle the +-10% oscillation of the torus; stage 2
(torus2.py) re-expands H exactly about the torus graph and measures the tube (measure.py).
"""
from __future__ import annotations

import argparse
import json
import math
import multiprocessing as mp
import os
import time

import numpy as np

import ft
from common import modal_model, polar, terms_of

LOG = []


def log(*a):
    s = ' '.join(str(x) for x in a)
    LOG.append(s)
    print(s, flush=True)


def normalize(S, Hf, n_kol, LB, rho_ref, tol=1e-30):
    gens = []
    H = Hf
    info = []
    for it in range(n_kol):
        for degs in ({0}, {1}):
            om = S.omega(H)
            chi, dmin = S.homological(H, om, degs)
            sizeA = S.norm(S.angle_part(H, {0}), rho_ref)
            sizeB = S.norm(S.angle_part(H, {1}), rho_ref)
            H = S.lie(H, chi, rho=rho_ref)
            gens.append(chi)
        info.append({'iter': it, 'A_before': sizeA, 'B_before': sizeB, 'omega': S.omega(H).tolist(),
                     'min_divisor': dmin})
        log(f'  kolmogorov {it}: |A|={sizeA:.3e} |B|={sizeB:.3e} omega={S.omega(H)} min|k.w|={dmin:.3e}')
        if max(sizeA, sizeB) < tol:
            break
    for s in range(2, LB + 1):
        om = S.omega(H)
        size = S.norm(S.angle_part(H, {s}), rho_ref)
        chi, dmin = S.homological(H, om, {s})
        H = S.lie(H, chi, rho=rho_ref)
        gens.append(chi)
        log(f'  birkhoff p-degree {s}: |angle part|={size:.3e}')
        info.append({'birkhoff': s, 'size_before': size})
    resid = S.norm_by_degree(S.angle_part(H, set(range(S.L + 1))), rho_ref)
    log('  remaining angle part by p-degree (rho_ref):', ' '.join(f'{x:.1e}' for x in resid))
    return gens, H, info


_GENS = {}


def _pull(j):
    S, gens, rho = _GENS['S'], _GENS['gens'], _GENS['rho']
    F = S.var(j)
    for chi in reversed(gens):
        F = S.lie(F, chi, sign=-1.0, rho=rho)
    return F


def pullback(S, gens, rho):
    """F_j = p_j pulled back; FT_PULL_PROCS=3 runs the three in forked processes (default serial)."""
    _GENS.update(S=S, gens=gens, rho=rho)
    procs = int(os.environ.get('FT_PULL_PROCS', '1'))
    if procs > 1:
        with mp.get_context('fork').Pool(min(procs, 3)) as pool:
            Fs = pool.map(_pull, [0, 1, 2])
    else:
        Fs = [_pull(j) for j in range(3)]
    _GENS.clear()
    return Fs


def grid_values(S, f, G2):
    """Values of the coefficient functions of f (shape M x G x G) on a finer G2 x G2 phi-grid."""
    c = np.zeros((f.shape[0], G2, G2), dtype=complex)
    sel = S.kabs <= S.K
    k1, k2 = S.K1[sel], S.K2[sel]
    c[:, k1 % G2, k2 % G2] = f[:, sel]
    return np.fft.ifft2(c, axes=(-2, -1)) * (G2 * G2)


def eval_grid(S, fv, p):
    """f(p(phi), phi) on the grid; fv: grid values (M, G2, G2), p: (3, G2, G2)."""
    out = np.zeros(fv.shape[1:], dtype=complex)
    pw = [[np.ones_like(p[j])] for j in range(3)]
    for j in range(3):
        for e in range(1, S.L + 1):
            pw[j].append(pw[j][-1] * p[j])
    for i, m in enumerate(S.mons):
        out += fv[i] * pw[0][m[0]] * pw[1][m[1]] * pw[2][m[2]]
    return out


def solve_torus(S, Fs, c, G2, iters=30):
    """tau(phi) with F_j(tau, phi) = c_j at every grid angle (Newton)."""
    Fv = [grid_values(S, F, G2) for F in Fs]
    dFv = [[grid_values(S, S.d_p(F, i), G2) for i in range(3)] for F in Fs]
    p = np.zeros((3, G2, G2))
    for j in range(3):
        p[j] = c[j] - (eval_grid(S, Fv[j], p).real - p[j])
    for it in range(iters):
        r = np.stack([eval_grid(S, Fv[j], p).real - c[j] for j in range(3)])
        J = np.stack([np.stack([eval_grid(S, dFv[j][i], p).real for i in range(3)]) for j in range(3)])
        Jt = np.moveaxis(J, (0, 1), (-2, -1))
        dp = np.linalg.solve(Jt, np.moveaxis(r, 0, -1)[..., None])[..., 0]
        p = p - np.moveaxis(dp, -1, 0)
        if np.abs(r).max() < 1e-22:
            break
    return p, float(np.abs(r).max()), J


def useries_monomials(Lu):
    return ft.monomials(Lu)


def compose_F(S, Fv, tau, Lu):
    """u-series of f(tau(phi) + u, phi): dict u-monomial -> grid values."""
    umons = useries_monomials(Lu)
    out = {m: np.zeros(tau.shape[1:], dtype=complex) for m in umons}
    tp = [[np.ones_like(tau[j])] for j in range(3)]
    for j in range(3):
        for e in range(1, S.L + 1):
            tp[j].append(tp[j][-1] * tau[j])
    for i, m in enumerate(S.mons):
        for um in umons:
            if any(um[j] > m[j] for j in range(3)):
                continue
            coef = 1.0
            arr = fv_i = Fv[i]
            for j in range(3):
                coef *= math.comb(m[j], um[j])
            out[um] += coef * fv_i * tp[0][m[0] - um[0]] * tp[1][m[1] - um[1]] * tp[2][m[2] - um[2]]
    return out


def umul(a, b, Lu):
    out = {}
    for ma, va in a.items():
        for mb, vb in b.items():
            m = (ma[0] + mb[0], ma[1] + mb[1], ma[2] + mb[2])
            if sum(m) > Lu:
                continue
            out[m] = out.get(m, 0) + va * vb
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--L', type=int, default=10)
    ap.add_argument('--K', type=int, default=40)
    ap.add_argument('--LB', type=int, default=6)
    ap.add_argument('--kol', type=int, default=8)
    ap.add_argument('--recenter', type=int, default=2)
    ap.add_argument('--G2', type=int, default=128)
    ap.add_argument('--tag', default='')
    args = ap.parse_args()
    t0 = time.time()
    Hz, Hw, nu, V, z0, w0 = modal_model()
    terms = terms_of(Hw)
    I0 = [abs(x) ** 2 for x in w0]
    C0 = sum(I0)
    # reference actions: orbit means rescaled to the nominal AMD
    Imean = [3.17139361e-04, 6.69453863e-04, 2.98474556e-05]
    s = C0 / sum(Imean)
    Istar = [x * s for x in Imean]
    S = ft.Space(L=args.L, K=args.K)
    log(f'space L={S.L} K={S.K} G={S.G} M={S.M}; I*={Istar}; C0={C0}')
    rho_ref = [3e-6, 3e-6, 3e-7]
    for rc in range(args.recenter + 1):
        Hf = ft.from_modal_poly(S, terms, Istar)
        log(f'[pass {rc}] expanded H about I* ({time.time() - t0:.1f}s)')
        gens, Hn, info = normalize(S, Hf, args.kol, args.LB, rho_ref)
        log(f'  normalized: {len(gens)} generators ({time.time() - t0:.1f}s)')
        Fs = pullback(S, gens, rho_ref)
        p, phi = polar(w0, Istar)
        c = np.array([S.eval(F, p, phi).real for F in Fs])
        log(f'  F(nominal) = {c}  sum = {c.sum():.3e}  (p nominal = {p}) ({time.time() - t0:.1f}s)')
        if rc < args.recenter:
            Istar = [Istar[j] + c[j] for j in range(3)]
    om = S.omega(Hn)
    log('torus frequencies omega =', om, ' (orbit NAFF: -1.3514e-4, -2.0291e-5, -1.1667e-5)')
    # torus graph (stage 2, torus2.py, re-expands H about it and measures the tube)
    G2 = args.G2
    tau, res, J = solve_torus(S, Fs, c, G2)
    log(f'torus graph: Newton residual {res:.2e}; tau range', [(float(tau[j].min()), float(tau[j].max()))
                                                                for j in range(3)])
    rep = {'args': vars(args), 'Istar': Istar, 'omega': om.tolist(), 'c': c.tolist(), 'info': info,
           'tau_range': [(float(tau[j].min()), float(tau[j].max())) for j in range(3)],
           'log': LOG, 'seconds': time.time() - t0}
    out = ft.__file__.rsplit('/', 1)[0] + '/results'
    tag = args.tag or f'torus-L{args.L}-K{args.K}-LB{args.LB}'
    with open(f'{out}/{tag}.json', 'w') as fh:
        json.dump(rep, fh, indent=1, default=float)
    np.savez(f'{out}/{tag}-F.npz', F0=Fs[0], F1=Fs[1], F2=Fs[2], Istar=np.array(Istar), c=c)
    log(f'done in {time.time() - t0:.1f}s')


if __name__ == '__main__':
    main()
