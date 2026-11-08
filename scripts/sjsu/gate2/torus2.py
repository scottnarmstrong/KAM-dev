#!/usr/bin/env python3
"""Stage 2: approximate integrals expanded about the torus graph (measured, floating).

Run with /usr/bin/python3 after torus.py (stage 1). From the stage-1 integrals, the torus through
the nominal point is p = tau(phi); its gradient part c0 + grad_q S(phi) defines the exactly canonical
change (I, q) -> (u, q), I = B0(phi) + u, B0 = I* + c0 + grad_q S. The Hamiltonian is re-expanded
EXACTLY about B0 at every grid angle (binomial series in u, no expansion about a constant action),
normalized again (Kolmogorov + Birkhoff, u-degree L2), and the literal brackets {F_j, H} with the
full degree-18 model are measured on a tube around the stage-2 torus, as in torus.py.
"""
from __future__ import annotations

import argparse
import json
import time
from collections import defaultdict

import numpy as np

import ft
import torus as T1
from common import modal_model, polar, terms_of
from measure import measure_profiles, observable_profiles, profile
from torus import log


def kgrid(G2):
    k = np.rint(np.fft.fftfreq(G2, 1.0 / G2)).astype(int)
    return np.meshgrid(k, k, indexing='ij')


def h_useries(terms, B, Lu):
    """u-series of H(B(phi) + u, phi) on the grid: dict u-monomial -> complex grid values.

    H = sum c prod_j I_j^{n_j/2} e^{i k.q}; the coefficient of u^m is
    sum_n T_n(phi) prod_j binom(n_j/2, m_j) B_j^{n_j/2 - m_j}, T_n = sum_{terms with n} c e^{i k.phi},
    accumulated one variable at a time.
    """
    G2 = B[0].shape[0]
    groups = defaultdict(list)
    for e, c in terms:
        n = (e[0] + e[3], e[1] + e[4], e[2] + e[5])
        groups[n].append(((e[0] - e[3]) % G2, (e[1] - e[4]) % G2, c))
    T = {}
    for n, lst in groups.items():
        arr = np.zeros((G2, G2), dtype=complex)
        for a, b, c in lst:
            arr[a, b] += c
        T[n] = np.fft.ifft2(arr) * (G2 * G2)
    logB = [np.log(b) for b in B]
    cache = {}

    def pw(j, e2):
        if (j, e2) not in cache:
            cache[(j, e2)] = np.exp(0.5 * e2 * logB[j])
        return cache[(j, e2)]

    def bn(nj, mj):
        return ft.gbinom(np.array(nj / 2.0), mj).item()

    U = defaultdict(dict)
    for n, Tn in T.items():
        for m2 in range(Lu + 1):
            b = bn(n[2], m2)
            if b == 0.0:
                continue
            d = U[(n[0], n[1])]
            d[m2] = d.get(m2, 0) + b * pw(2, n[2] - 2 * m2) * Tn
    Vd = defaultdict(dict)
    for (n0, n1), d in U.items():
        for m2, arr in d.items():
            for m1 in range(Lu + 1 - m2):
                b = bn(n1, m1)
                if b == 0.0:
                    continue
                e = Vd[n0]
                e[(m1, m2)] = e.get((m1, m2), 0) + b * pw(1, n1 - 2 * m1) * arr
    out = {}
    for n0, d in Vd.items():
        for (m1, m2), arr in d.items():
            for m0 in range(Lu + 1 - m1 - m2):
                b = bn(n0, m0)
                if b == 0.0:
                    continue
                key = (m0, m1, m2)
                out[key] = out.get(key, 0) + b * pw(0, n0 - 2 * m0) * arr
    return out


def grid_to_space(S, v):
    """Fourier coefficients (hexagon |k|_1 <= S.K) of grid values v (G2 x G2) in S's layout."""
    G2 = v.shape[0]
    c = np.fft.fft2(v) / (G2 * G2)
    K1, K2 = kgrid(G2)
    kabs = np.abs(K1) + np.abs(K2) + np.abs(K1 + K2)
    sel = kabs <= S.K
    out = np.zeros((S.G, S.G), dtype=complex)
    out[K1[sel] % S.G, K2[sel] % S.G] = c[sel]
    tail = float(np.abs(c[~sel]).sum())
    return out, tail


def spectral_dphi(v, a):
    G2 = v.shape[0]
    K1, K2 = kgrid(G2)
    K = K1 if a == 0 else K2
    return np.fft.ifft2(np.fft.fft2(v) * (1j * K))


def compose_dict(series, tau, Lv):
    """v-series of sum_m h_m(phi) (tau(phi) + v)^m (series: dict m -> grid)."""
    import math
    out = {}
    Lmax = max(sum(m) for m in series)
    tp = [[np.ones_like(tau[j])] for j in range(3)]
    for j in range(3):
        for e in range(1, Lmax + 1):
            tp[j].append(tp[j][-1] * tau[j])
    for m, h in series.items():
        for vm in ft.monomials(min(Lv, sum(m))):
            if any(vm[j] > m[j] for j in range(3)):
                continue
            coef = math.comb(m[0], vm[0]) * math.comb(m[1], vm[1]) * math.comb(m[2], vm[2])
            out[vm] = out.get(vm, 0) + coef * h * tp[0][m[0] - vm[0]] * tp[1][m[1] - vm[1]] * \
                tp[2][m[2] - vm[2]]
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--stage1', required=True, help='tag of a torus.py run (results/<tag>.json)')
    ap.add_argument('--L', type=int, default=8)
    ap.add_argument('--K', type=int, default=50)
    ap.add_argument('--LB', type=int, default=6)
    ap.add_argument('--kol', type=int, default=4)
    ap.add_argument('--KS', type=int, default=60, help='Fourier cutoff of the shift S')
    ap.add_argument('--G2', type=int, default=192)
    ap.add_argument('--Lv', type=int, default=12)
    ap.add_argument('--dw', default='1,1,1', help='tube weights: delta_j = delta * w_j')
    ap.add_argument('--kappa', type=float, default=2.0)
    ap.add_argument('--prune', default='0', help='comma list of pruning thresholds for F (0: none)')
    ap.add_argument('--prune-delta', type=float, default=1e-6, help='tube width used in the pruning weight')
    ap.add_argument('--tag', default='')
    args = ap.parse_args()
    t0 = time.time()
    out_dir = ft.__file__.rsplit('/', 1)[0] + '/results'
    st1 = json.load(open(f'{out_dir}/{args.stage1}.json'))
    z = np.load(f'{out_dir}/{args.stage1}-F.npz')
    S1 = ft.Space(L=st1['args']['L'], K=st1['args']['K'])
    F1 = [z['F0'], z['F1'], z['F2']]
    Istar = list(z['Istar'])
    c1 = z['c']
    Hz, Hw, nu, V, z0, w0 = modal_model()
    terms = terms_of(Hw)
    G2 = args.G2
    K1g, K2g = kgrid(G2)
    k = np.arange(G2) * 2 * np.pi / G2
    phi_grid = np.meshgrid(k, k, indexing='ij')
    # 1. stage-1 torus through the nominal point and its gradient (Lagrangian) part
    tau, res, _ = T1.solve_torus(S1, F1, c1, G2)
    tc = [np.fft.fft2(tau[j]) / (G2 * G2) for j in range(3)]
    kk = [K1g, K2g, -K1g - K2g]
    ksq = (K1g ** 2 + K2g ** 2 + (K1g + K2g) ** 2).astype(float)
    kabs = np.abs(K1g) + np.abs(K2g) + np.abs(K1g + K2g)
    s_hat = np.where(ksq > 0, -1j * (kk[0] * tc[0] + kk[1] * tc[1] + kk[2] * tc[2]) / np.where(ksq > 0, ksq, 1), 0)
    s_hat[kabs > args.KS] = 0
    c0 = [tc[j][0, 0].real for j in range(3)]
    grad_hat = [1j * kk[j] * s_hat for j in range(3)]
    nongrad = max(float(np.abs(tc[j] - grad_hat[j] - (c0[j] if True else 0) * (ksq == 0)).sum()) for j in range(3))
    s_tail = float(np.abs(s_hat[kabs > 0.8 * args.KS]).sum())
    log(f'stage-1 torus: Newton residual {res:.1e}; non-gradient part (l1 of coef) {nongrad:.2e}; '
        f'S coef mass beyond 0.8 KS: {s_tail:.2e}')
    B0 = [Istar[j] + c0[j] + np.fft.ifft2(grad_hat[j]).real * (G2 * G2) for j in range(3)]
    log('B0 range', [(float(b.min()), float(b.max())) for b in B0], f'({time.time() - t0:.1f}s)')
    # 2. H about B0, exactly
    Lv = args.Lv
    Hs = h_useries(terms, B0, max(args.L, Lv) + 1)
    log(f'u-series of H about B0: {len(Hs)} monomials ({time.time() - t0:.1f}s)')
    S = ft.Space(L=args.L, K=args.K)
    Ht = S.zeros()
    tails = 0.0
    for m, v in Hs.items():
        if sum(m) > args.L:
            continue
        arr, tail = grid_to_space(S, v)
        Ht[S.idx[m]] = arr
        rho = [3e-8, 3e-8, 3e-8]
        tails += tail * rho[0] ** m[0] * rho[1] ** m[1] * rho[2] ** m[2]
    log(f'stage-2 space L={S.L} K={S.K} G={S.G} M={S.M}; Fourier tail of H beyond K (rho 3e-8): {tails:.2e}')
    # check: H at the nominal point
    p_nom, phi_nom = polar(w0, Istar)
    e = np.exp(1j * (K1g * phi_nom[0] + K2g * phi_nom[1]))
    B0_nom = [float((np.fft.fft2(B0[j]) / (G2 * G2) * e).sum().real) for j in range(3)]
    u_nom = [abs(w0[j]) ** 2 - B0_nom[j] for j in range(3)]
    log('nominal point: u =', u_nom, ' H~ =', S.eval(Ht, u_nom, phi_nom).real,
        ' H =', complex(sum(c * np.prod([w0[j] ** ee[j] * np.conj(w0[j]) ** ee[j + 3] for j in range(3)])
                            for ee, c in terms)).real)
    # 3. normalize again
    rho_ref = [3e-8, 3e-8, 3e-8]
    gens, Hn, info = T1.normalize(S, Ht, args.kol, args.LB, rho_ref)
    log(f'  normalized: {len(gens)} generators ({time.time() - t0:.1f}s)')
    Fs = T1.pullback(S, gens, rho_ref)
    c = np.array([S.eval(F, u_nom, phi_nom).real for F in Fs])
    om = S.omega(Hn)
    log(f'  F(nominal) = {c} ; omega = {om} ({time.time() - t0:.1f}s)')
    # 4. stage-2 torus and tube measurement (one observable at a time, to bound memory)
    tau2, res2, _ = T1.solve_torus(S, Fs, c, G2)
    log(f'stage-2 torus: Newton residual {res2:.1e}; |tau2| max', [float(np.abs(t).max()) for t in tau2])
    # H derivatives at fixed u: du_i from the u-series, dq_i spectrally (includes the S-Hessian term)
    dIu = []
    for i in range(3):
        d = {}
        for m, v in Hs.items():
            if m[i] == 0:
                continue
            mm = list(m)
            mm[i] -= 1
            d[tuple(mm)] = m[i] * v
        dIu.append(compose_dict(d, tau2, Lv))
    dph = [{m: spectral_dphi(v, a) for m, v in Hs.items() if sum(m) <= Lv} for a in range(2)]
    del Hs
    dqu = [compose_dict(dph[0], tau2, Lv), compose_dict(dph[1], tau2, Lv)]
    del dph
    dqu.append({m: -(dqu[0].get(m, 0) + dqu[1].get(m, 0)) for m in set(dqu[0]) | set(dqu[1])})
    PdI = [profile(s) for s in dIu]
    Pdq = [profile(s) for s in dqu]
    log(f'composed H on the tube ({time.time() - t0:.1f}s)')
    hess = [[float(np.abs(kk[i] * kk[l] * s_hat).sum()) for l in range(3)] for i in range(3)]
    Bmin = [float((B0[j] + tau2[j]).min()) for j in range(3)]
    Bmax = [float((B0[j] + tau2[j]).max()) for j in range(3)]
    dw = [float(x) for x in args.dw.split(',')]
    rho_p = [args.kappa * args.prune_delta] * 3
    prune_rows = []
    rows = None
    for thr in [float(x) for x in args.prune.split(',')]:
        # literal observables kept: coefficients with |c| (kappa delta_p)^m >= thr (thr = 0: all)
        w = S.weights(rho_p)[:, None, None]
        Fp = [np.where(np.abs(F) * w >= thr, F, 0) if thr > 0 else F for F in Fs]
        kept = [int(np.count_nonzero(F)) for F in Fp]
        cp = np.array([S.eval(F, u_nom, phi_nom).real for F in Fp])
        obs, g0 = [], []
        for j in range(3):
            Fu = T1.compose_F(S, T1.grid_values(S, Fp[j], G2), tau2, Lv)
            dpF = [T1.compose_F(S, T1.grid_values(S, S.d_p(Fp[j], i), G2), tau2, Lv) for i in range(3)]
            dphF = [T1.compose_F(S, T1.grid_values(S, S.d_phi(Fp[j], a), G2), tau2, Lv) for a in range(2)]
            dqF = [dphF[0], dphF[1], {m: -(dphF[0].get(m, 0) + dphF[1].get(m, 0))
                                      for m in set(dphF[0]) | set(dphF[1])}]
            G = {}
            for i in range(3):
                for m, v in T1.umul(dqF[i], dIu[i], Lv).items():
                    G[m] = G.get(m, 0) - v
                for m, v in T1.umul(dpF[i], dqu[i], Lv).items():
                    G[m] = G.get(m, 0) + v
            g0.append(G[(0, 0, 0)])
            obs.append(observable_profiles(G, dqF, dpF, Fu, j, cp[j]))
            del Fu, dpF, dphF, dqF, G
        amd = float(np.abs(g0[0] + g0[1] + g0[2]).max())
        log(f'[prune {thr:g}] kept coefficients {kept} of {[int(np.count_nonzero(F)) for F in Fs]}; '
            f'max |{{F_j,H}}| on the torus grid {[float(np.abs(g).max()) for g in g0]}; AMD defect {amd:.1e}')
        r_thr = measure_profiles(obs, PdI, Pdq, terms, Bmin, Bmax, hess, Lv, args.kappa, dw, log=log)
        prune_rows.append({'threshold': thr, 'rho': rho_p, 'kept': kept, 'amd_defect': amd, 'rows': r_thr})
        if rows is None:
            rows = r_thr
    tag = args.tag or f'torus2-{args.stage1}-L{args.L}-K{args.K}-LB{args.LB}'
    rep = {'args': vars(args), 'Istar': Istar, 'c0': c0, 'omega': om.tolist(), 'c': c.tolist(),
           'info': info, 'rows': rows, 'prune': prune_rows, 'log': T1.LOG, 'seconds': time.time() - t0}
    with open(f'{out_dir}/{tag}.json', 'w') as fh:
        json.dump(rep, fh, indent=1, default=float)
    np.savez(f'{out_dir}/{tag}-F.npz', F0=Fs[0], F1=Fs[1], F2=Fs[2], s_hat=s_hat, Istar=np.array(Istar),
             c0=np.array(c0), c=c)
    log(f'done in {time.time() - t0:.1f}s')


if __name__ == '__main__':
    main()
