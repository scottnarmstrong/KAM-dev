#!/usr/bin/env python3
"""G2: frequency modulation of the divisors over the R4 tube (research scratch; float64, sampled).

At every slow point of points.json (and the nominal point): the first-order osculating offset
Lambda - Lambda' = d_lambda chi1 (keep52 generator, exact Kepler divisors at the point, pair grids), its range
over the fast torus, scaled by the N-body/first-order ratio measured at the nominal point (E9: the first-order
offset underestimates the N-body range).  Then, over every harmonic of the G1 grid box that the keep52nr normal
form divides by (|k_J| <= KB[0], |k_S| <= KB[1], |k_U| <= KB[2], not kept), the lower bound
  min over the torus |k.n(Lambda)| >= |k.n0| - sum_j |k_j| (3 n_j/Lambda_j) max|Lambda_j - Lambda'_j|,
and, for the listed near-resonant harmonics, the exact sampled minimum of |k.n0 + sum_j k_j A_j (Lambda - Lambda')_j|
over the fast grid.  The rate floor of the unnormalized near-resonant harmonics comes from the G1 ladders
(floor_nr); this script records the kept set.
usage: g2_modulation.py POINTS.json OUT.json [--grid 128,128,64] [--box 32,32,16]
"""
import argparse, json, os, sys, time
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import model as M, nf

NB_RANGE = np.array([3.2e-4, 4.0e-4, 5.6e-5])      # N-body ranges of Lambda - <Lambda> (research plan E9)
LISTED = [(2, -5, 0), (2, -6, 3), (4, -11, 3), (3, -5, -7), (6, -17, 6), (1, 0, -7), (0, 1, -3), (1, -4, 4)]


def kf(n):
    return np.round(np.fft.fftfreq(n, 1.0 / n)).astype(int)


def offsets(slow, ng, dn):
    n0 = M.n_kep(slow[0]) + dn
    d = [np.zeros(ng) for _ in range(3)]
    for (i, j) in M.PAIRS:
        v = M.pair_f_float(i, j, slow, ng)
        c = np.fft.fft2(v) / v.size
        ki = kf(ng[i])[:, None]; kj = kf(ng[j])[None, :]
        kn = ki * n0[i] + kj * n0[j]
        kvec = {i: ki * np.ones_like(kj), j: kj * np.ones_like(ki)}
        kJ = kvec.get(0, 0); kS = kvec.get(1, 0); kU = kvec.get(2, 0)
        kept = ((ki == 0) & (kj == 0)) | ((5 * np.asarray(kJ) + 2 * np.asarray(kS) == 0) & (np.asarray(kU) == 0))
        with np.errstate(divide='ignore', invalid='ignore'):
            chi = np.where(kept, 0, c / (1j * kn))
        for q, kq in ((i, ki), (j, kj)):
            g = (np.fft.ifft2(1j * kq * chi) * v.size).real
            shape = [1, 1, 1]; shape[i] = ng[i]; shape[j] = ng[j]
            d[q] = d[q] + g.reshape(shape)
    return n0, d


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('points'); ap.add_argument('out')
    ap.add_argument('--grid', default='128,128,64'); ap.add_argument('--box', default='32,32,16')
    a = ap.parse_args()
    t0 = time.process_time()
    ng = tuple(int(x) for x in a.grid.split(','))
    KB = tuple(int(x) for x in a.box.split(','))
    P = json.load(open(a.points))
    pts = [dict(P['nominal'], kind='nominal')] + P['points']
    nom = P['nominal']
    slow_nom = tuple(np.array(nom[k], float) for k in ('Lambda', 'xi', 'eta'))
    # first-order offsets at the nominal point -> scale to the N-body range
    _, dnom = offsets(slow_nom, ng, M.DN_STAR)
    rng_nom = np.array([float(x.max() - x.min()) for x in dnom])
    scale = NB_RANGE / rng_nom
    kJ = np.arange(-KB[0], KB[0] + 1)[:, None, None]
    kS = np.arange(-KB[1], KB[1] + 1)[None, :, None]
    kU = np.arange(-KB[2], KB[2] + 1)[None, None, :]
    g_nom = None
    rows = []
    for idx, pt in enumerate(pts):
        slow = tuple(np.array(pt[k], float) for k in ('Lambda', 'xi', 'eta'))
        # Kolmogorov shift as in ladder.py: DN* + grad<f>(pt) - grad<f>(nominal), grad by central differences
        def gradavg(s):
            g = np.zeros(3)
            for q in range(3):
                h = 1e-6 * s[0][q]
                sp = (s[0].copy(), s[1], s[2]); sm = (s[0].copy(), s[1], s[2])
                sp[0][q] += h; sm[0][q] -= h
                fp = sum(M.pair_f_float(i, j, sp, ng).mean() for (i, j) in M.PAIRS)
                fm = sum(M.pair_f_float(i, j, sm, ng).mean() for (i, j) in M.PAIRS)
                g[q] = (fp - fm) / (2 * h)
            return g
        if g_nom is None:
            g_nom = gradavg(slow_nom)
        dn = M.DN_STAR + gradavg(slow) - g_nom
        n0, d = offsets(slow, ng, dn)
        half = np.array([float(np.abs(x - x.mean()).max()) for x in d]) * scale     # scaled max |Lambda - <Lambda>|
        A = 3 * M.n_kep(slow[0]) / slow[0]
        kn = kJ * n0[0] + kS * n0[1] + kU * n0[2]
        modb = np.abs(kJ) * A[0] * half[0] + np.abs(kS) * A[1] * half[1] + np.abs(kU) * A[2] * half[2]
        mod_rule = np.abs(kJ) * A[0] * nf.OSC_HALF[0] + np.abs(kS) * A[1] * nf.OSC_HALF[1] \
            + np.abs(kU) * A[2] * nf.OSC_HALF[2]
        zero = (kJ == 0) & (kS == 0) & (kU == 0)
        fam = (5 * kJ + 2 * kS == 0) & (kU == 0)
        nr = (np.abs(kn) - mod_rule < nf.NR_THRESH) & ~(zero | fam)
        normalized = ~(zero | fam | nr)
        lb = np.abs(kn) - modb
        lbn = np.where(normalized, lb, np.inf)
        w = np.unravel_index(np.argmin(lbn), lbn.shape)
        worst = [int(kJ.ravel()[w[0]]), int(kS.ravel()[w[1]]), int(kU.ravel()[w[2]])]
        listed = {}
        for k in LISTED:
            shift = sum(k[q] * (-A[q]) * (d[q] - d[q].mean()) * scale[q] for q in range(3))
            nu = float(np.dot(k, n0))
            listed[str(k)] = {'divisor_mean': nu, 'shift_min': float(shift.min()), 'shift_max': float(shift.max()),
                              'min_abs_over_torus': float(np.abs(nu + shift).min()),
                              'status': 'kept_52' if (5 * k[0] + 2 * k[1] == 0 and k[2] == 0) else
                              ('kept_nr' if bool(nr[k[0] + KB[0], k[1] + KB[1], k[2] + KB[2]]) else 'normalized')}
        row = {'index': idx - 1, 'kind': pt.get('kind'), 't_end_yr': pt.get('t_end_yr'),
               'osc_half_scaled': half.tolist(), 'osc_half_rule': nf.OSC_HALF.tolist(),
               'osc_within_rule': bool(np.all(half <= nf.OSC_HALF)),
               'n_kept_nr': int(nr.sum()), 'n_normalized': int(normalized.sum()),
               'min_normalized_divisor_lower_bound': float(lbn.min()), 'worst_k': worst,
               'worst_k_divisor': float(np.dot(worst, n0)), 'listed': listed}
        if idx == 0:
            kk = np.argwhere(nr)
            row['kept_nr_set'] = sorted(
                [{'k': [int(kJ.ravel()[i]), int(kS.ravel()[j]), int(kU.ravel()[l])],
                  'divisor': float(kn[i, j, l]), 'mod_bound_rule': float(mod_rule[i, j, l])}
                 for i, j, l in kk if (kJ.ravel()[i], kS.ravel()[j], kU.ravel()[l]) > (0, 0, 0)
                 or (kJ.ravel()[i] == 0 and (kS.ravel()[j], kU.ravel()[l]) > (0, 0))],
                key=lambda r: abs(r['divisor']))
        rows.append(row)
        print(idx - 1, pt.get('kind'), 'half', ['%.2e' % x for x in half], 'minLB %.3e' % lbn.min(), worst,
              '(2,-6,3) min %.2e' % listed['(2, -6, 3)']['min_abs_over_torus'], flush=True)
    out = {'grid': ng, 'box': KB, 'nbody_range_E9': NB_RANGE.tolist(), 'first_order_range_nominal': rng_nom.tolist(),
           'scale_nbody_over_first_order': scale.tolist(), 'threshold': nf.NR_THRESH, 'points': rows,
           'min_over_points_normalized_divisor_lower_bound': min(r['min_normalized_divisor_lower_bound'] for r in rows),
           'all_osc_within_rule': all(r['osc_within_rule'] for r in rows),
           'cpu_s': time.process_time() - t0,
           'status': 'measured (float64, first-order offsets scaled to the N-body range, sampled grids)'}
    json.dump(out, open(a.out, 'w'), indent=1)
    print('min LB over points %.3e' % out['min_over_points_normalized_divisor_lower_bound'],
          'osc within rule', out['all_osc_within_rule'], 'cpu', out['cpu_s'])


if __name__ == '__main__':
    main()
