#!/usr/bin/env python3
"""Floating normal-form gate for SJSU18-O2 (measured, not certified).

Birkhoff normal form around the origin in modal coordinates through degree K, approximate
integrals F_j = I_j o Psi^{-1} pulled back to the modal coordinates, full brackets {F_j, H}
against the whole degree-18 model, and two region geometries:
  * 'polydisk': the scout's region I_j < R^2 s_j^2 around the origin (reproduction);
  * 'annulus': a thin action box around the nominal orbit, I_j in I0_j (1 +- R'), initial box
    I0_j (1 +- r'); gap m_j = (R' - r') I0_j - 2 eps_j, majorants at the outer radius.
Usage: python3 run_nf.py --K 8 [--small-divisor 0]
"""
from __future__ import annotations

import argparse
import json
import math
import os
import time
from pathlib import Path

import poly as P

HERE = Path(__file__).resolve().parent
MODEL = Path(os.environ.get('SJSU_APP', HERE.parents[2] / 'applications' / 'sjsu'))

# nominal secular point (README "Nominal initial point"; validation/table2_map_poincare_order1.json)
XI = [0.03446271128616895, -0.0014352339355918572, -0.010122263133599879]
ETA = [-0.009080669615926963, -0.025602508346796338, -0.0016540224121661881]


def jacobi_eig(A, sweeps=60):
    """Eigen-decomposition of a real symmetric 3x3 matrix: A = V diag(lam) V^T (columns of V)."""
    n = 3
    a = [row[:] for row in A]
    V = [[float(i == j) for j in range(n)] for i in range(n)]
    for _ in range(sweeps):
        off = sum(a[i][j] ** 2 for i in range(n) for j in range(n) if i != j)
        if off < 1e-60:
            break
        for p in range(n):
            for q in range(p + 1, n):
                if a[p][q] == 0:
                    continue
                theta = (a[q][q] - a[p][p]) / (2 * a[p][q])
                t = math.copysign(1.0, theta) / (abs(theta) + math.sqrt(theta * theta + 1))
                c = 1 / math.sqrt(t * t + 1)
                s = t * c
                for k in range(n):
                    akp, akq = a[k][p], a[k][q]
                    a[k][p], a[k][q] = c * akp - s * akq, s * akp + c * akq
                for k in range(n):
                    apk, aqk = a[p][k], a[q][k]
                    a[p][k], a[q][k] = c * apk - s * aqk, s * apk + c * aqk
                for k in range(n):
                    vkp, vkq = V[k][p], V[k][q]
                    V[k][p], V[k][q] = c * vkp - s * vkq, s * vkp + c * vkq
    lam = [a[i][i] for i in range(n)]
    order = sorted(range(n), key=lambda i: lam[i])  # most negative first (Jupiter-like mode)
    lam = [lam[i] for i in order]
    V = [[V[r][i] for i in order] for r in range(n)]
    for j in range(n):  # deterministic sign: largest component positive
        big = max(range(n), key=lambda r: abs(V[r][j]))
        if V[big][j] < 0:
            for r in range(n):
                V[r][j] = -V[r][j]
    return lam, V


def load_model():
    data = json.loads((MODEL / 'data/sjsu18-o2.json').read_text())
    H = {}
    for t in data['complex_form']['terms']:
        zJ, zbJ, zS, zbS, zU, zbU, c = t
        H[P.key_of((zJ, zS, zU, zbJ, zbS, zbU))] = float(c)
    return H, data


def to_modal(Hz, V):
    """Substitute z_j = sum_k V[j][k] w_k, zbar_j = sum_k V[j][k] wbar_k (V real orthogonal)."""
    Lw = [{P.UNIT[k]: V[j][k] for k in range(3)} for j in range(3)]
    Lb = [{P.UNIT[k + 3]: V[j][k] for k in range(3)} for j in range(3)]
    powers_w = [[{0: 1.0}] for _ in range(3)]
    powers_b = [[{0: 1.0}] for _ in range(3)]
    for j in range(3):
        for _ in range(20):
            powers_w[j].append(P.mul(powers_w[j][-1], Lw[j]))
            powers_b[j].append(P.mul(powers_b[j][-1], Lb[j]))
    memo_w, memo_b = {}, {}

    def part(e, powers, memo):
        if e not in memo:
            p = {0: 1.0}
            for j in range(3):
                if e[j]:
                    p = P.mul(p, powers[j][e[j]])
            memo[e] = p
        return memo[e]

    out = {}
    for k, c in Hz.items():
        e = P.exps(k)
        pw = part(e[:3], powers_w, memo_w)
        pb = part(e[3:], powers_b, memo_b)
        for kw, cw in pw.items():
            cc = c * cw
            for kb, cb in pb.items():
                m = kw + kb
                out[m] = out.get(m, 0) + cc * cb
    return out


def normal_form(Hw, nu, K, small=0.0):
    """Birkhoff normalization through degree K; returns generators and the normalized H."""
    Hk = P.truncate(Hw, K)
    gens, info = [], []
    for s in range(4, K + 1, 2):
        hs = P.by_degree(Hk, s)
        chi, divs, kept = {}, [], 0
        for k, c in hs.items():
            ch = P.charge(k)
            if ch == (0, 0, 0):
                continue
            d = ch[0] * nu[0] + ch[1] * nu[1] + ch[2] * nu[2]
            if abs(d) <= small:
                kept += 1
                continue
            chi[k] = 1j * c / d
            divs.append(abs(d))
        Hk = P.lie(Hk, chi, K)
        resid = [abs(c) for k, c in P.by_degree(Hk, s).items()
                 if P.charge(k) != (0, 0, 0)]
        info.append({'degree': s, 'generator_terms': len(chi), 'kept_resonant': kept,
                     'min_divisor': min(divs) if divs else None,
                     'max_residual_coef': max(resid) if resid else 0.0})
        gens.append(chi)
        print(f'  normalized degree {s}: {len(chi)} generator terms, '
              f'min divisor {info[-1]["min_divisor"]}', flush=True)
    return gens, Hk, info


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--K', type=int, default=6)
    ap.add_argument('--small-divisor', type=float, default=0.0)
    args = ap.parse_args()
    t0 = time.time()
    Hz, data = load_model()
    A = [[0.0] * 3 for _ in range(3)]
    for k, c in Hz.items():
        e = P.exps(k)
        if sum(e) == 2:
            j = [i for i in range(3) if e[i]][0]
            l = [i for i in range(3) if e[i + 3]][0]
            A[j][l] = c
    nu, V = jacobi_eig(A)
    print('frequencies nu (rad/yr):', nu, flush=True)
    Hw = to_modal(Hz, V)
    print(f'modal H: {len(Hw)} terms ({time.time() - t0:.1f}s)', flush=True)
    # nominal point
    z0 = [complex(XI[j], -ETA[j]) / math.sqrt(2) for j in range(3)]
    w0 = [sum(V[j][k] * z0[j] for j in range(3)) for k in range(3)]  # w = V^T z
    I0 = [abs(x) ** 2 for x in w0]
    print('nominal modal actions I0 =', I0, ' sum =', sum(I0), flush=True)
    hz = P.evaluate(Hz, z0)
    hw = P.evaluate(Hw, w0)
    print('H(z0) =', hz, ' H(w0) =', hw, flush=True)
    quad_off = max(abs(c) for k, c in P.by_degree(Hw, 2).items() if P.charge(k) != (0, 0, 0))
    print('max off-diagonal quadratic coef after diagonalization:', quad_off, flush=True)
    # exact AMD integral: C = sum w_j wbar_j; {C, H} must vanish identically
    C = {P.UNIT[j] + P.UNIT[j + 3]: 1.0 for j in range(3)}
    bC = P.bracket(C, Hw)
    print('max |coef| of {C, H}:', max((abs(c) for c in bC.values()), default=0.0), flush=True)

    gens, Hk, info = normal_form(Hw, nu, args.K, args.small_divisor)
    Is = [{P.UNIT[j] + P.UNIT[j + 3]: 1.0} for j in range(3)]
    Fs = []
    for I in Is:
        F = dict(I)
        for chi in reversed(gens):
            F = P.lie(F, chi, args.K, sign=-1.0)
        Fs.append(F)
    print('F terms:', [len(F) for F in Fs], f'({time.time() - t0:.1f}s)', flush=True)
    Bs = [P.bracket(F, Hw) for F in Fs]
    print('bracket terms:', [len(B) for B in Bs], f'({time.time() - t0:.1f}s)', flush=True)
    low = [max((abs(c) for k, c in B.items() if P.degree(k) <= args.K), default=0.0) for B in Bs]
    corr = [P.add(F, I, -1.0) for F, I in zip(Fs, Is)]
    s0 = [math.sqrt(x) for x in I0]
    rep = {'K': args.K, 'small_divisor': args.small_divisor, 'nu': nu, 'I0': I0,
           'normalization': info, 'F_terms': [len(F) for F in Fs],
           'bracket_terms': [len(B) for B in Bs], 'bracket_lowdeg_max': low,
           'polydisk': [], 'annulus': []}
    # polydisk geometry (scout eq. (4)): Q = {I_j <= r^2 I0_j}, D = {I_j < R^2 I0_j}
    for r in [0.3, 0.5, 0.7, 1.0]:
        best = None
        for f in [1.025, 1.05, 1.1, 1.2, 1.3, 1.5, 2.0]:
            R = f * r
            rho = [R * x for x in s0]
            eta = [P.majorant(B, rho) for B in Bs]
            eps = [P.majorant(c, rho) for c in corr]
            m = [(R * R - r * r) * I0[j] - 2 * eps[j] for j in range(3)]
            T = min(m[j] / eta[j] for j in range(3))
            if best is None or T > best['T']:
                best = {'r': r, 'R': R, 'T': T, 'eta': eta, 'eps': eps}
        rep['polydisk'].append(best)
    # annulus geometry: Q = {|I_j - I0_j| <= r' I0_j}, D = {|I_j - I0_j| < R' I0_j}
    for rp in [1e-6, 1e-3, 1e-2]:
        best = None
        for Rp in [0.002, 0.005, 0.01, 0.02, 0.05, 0.1, 0.2, 0.3, 0.5]:
            if Rp <= rp:
                continue
            rho = [math.sqrt((1 + Rp) * I0[j]) for j in range(3)]
            eta = [P.majorant(B, rho) for B in Bs]
            eps = [P.majorant(c, rho) for c in corr]
            m = [(Rp - rp) * I0[j] - 2 * eps[j] for j in range(3)]
            T = min(m[j] / eta[j] for j in range(3))
            if best is None or T > best['T']:
                best = {'r_rel': rp, 'R_rel': Rp, 'T': T, 'eta': eta, 'eps': eps, 'margin': m}
        rep['annulus'].append(best)
    rep['seconds'] = time.time() - t0
    for row in rep['polydisk']:
        print(f"polydisk r={row['r']}: T={row['T']:.3e} yr at R={row['R']:.3f}", flush=True)
    for row in rep['annulus']:
        print(f"annulus r'={row['r_rel']}: T={row['T']:.3e} yr at R'={row['R_rel']}, "
              f"eta={['%.2e' % x for x in row['eta']]}, eps={['%.2e' % x for x in row['eps']]}",
              flush=True)
    out = HERE / 'results'
    out.mkdir(exist_ok=True)
    tag = f"nf-K{args.K}" + (f"-res{args.small_divisor:g}" if args.small_divisor else '')
    (out / f'{tag}.json').write_text(json.dumps(rep, indent=1, default=str) + '\n')
    print(f'done in {time.time() - t0:.1f}s', flush=True)


if __name__ == '__main__':
    main()
