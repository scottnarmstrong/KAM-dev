#!/usr/bin/env python3
"""G6: model gap of the averaged secular Hamiltonian H-bar at mass orders 2..4 against the 1-Gyr N-body run.

H-bar: the repository's SLG13 Lie steps kept to mass order N (applications/sjsu/scripts/lie_mimic.lie_secular,
n* corrected, a* of validation/astar.json), secular part to degree Dfinal in (z, zbar).  Its secular flow
dz/dt = -i dH/dzbar (RK4) is started at the N-body block mean (xi, eta) of the first 4416-yr block and compared
over the first T years with the N-body block means:
  * fundamental frequencies of the modal signals (Hann window + golden-section peak, as freq_check.py), against
    the same analysis of the N-body block means over the same window;
  * the modal actions I_j = (x_j^2 + y_j^2)/2 in SJSU18-O2's eigenbasis O (as torus_offset.py): mean, min, max.
PASS iff every |g_model/g_Nbody - 1| <= 1e-4 and every mean/min/max difference of I_j <= delta/3 (delta = 1e-5).
usage: g6_model_gap.py MAIN.bin OUT.json [--orders 2,3,4] [--dfinal 4] [--years 1e7] [--dt 50]
"""
import argparse, json, math, os, sys, time
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, '..', '..', '..'))
sys.path.insert(0, os.path.join(REPO, 'applications', 'sjsu', 'scripts'))
import mpmath
from sjsu_common import Backend, physical_constants
from kepler_series import universal_series
from expansion import first_order_hamiltonian
from secular import nstar_split
from lie_mimic import lie_secular
from sparse import SP
from freq_check import ComplexPoly, rk4, fundamental_frequency


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('main_bin'); ap.add_argument('out')
    ap.add_argument('--orders', default='2,3,4'); ap.add_argument('--dfinal', type=int, default=4)
    ap.add_argument('--years', type=float, default=1e7); ap.add_argument('--dt', type=float, default=50.0)
    a = ap.parse_args()
    t0 = time.process_time()
    orders = [int(x) for x in a.orders.split(',')]
    mpmath.mp.dps = 40
    astar = [mpmath.mpf(s) for s in json.load(open(os.path.join(REPO, 'applications/sjsu/validation/astar.json')))['astar']]
    bk = Backend('ld')
    c = physical_constants(astar)
    D = a.dfinal + max(orders)
    U = universal_series(D, 18)
    f = first_order_hamiltonian(bk, U, c, D=D, KF=16, log=lambda *x: None)
    nvec, f, corr = nstar_split(f, c, bk, 'corrected')
    K2pp = [bk.real(x) for x in c['K2pp']]
    # N-body block means over the window
    rows = np.fromfile(a.main_bin, dtype=np.float64).reshape(-1, 26)
    tb = rows[:, 0]
    nwin = int(round(a.years / (tb[1] - tb[0])))
    R = rows[:nwin]
    O = np.array(json.load(open(os.path.join(REPO, 'applications/sjsu/validation/table2_map_poincare_order1.json')))['O'])
    xb, yb = R[:, 1:4] @ O, R[:, 4:7] @ O
    Inb = 0.5 * (xb ** 2 + yb ** 2)
    hb = tb[1] - tb[0]
    g_nb = [abs(fundamental_frequency(xb[:, j] + 1j * yb[:, j], hb)) for j in range(3)]
    z0 = (R[0, 1:4] - 1j * R[0, 4:7]) / math.sqrt(2)
    out = {'window_years': a.years, 'dfinal': a.dfinal, 'nbody': {'g': g_nb, 'I_mean': Inb.mean(0).tolist(),
           'I_min': Inb.min(0).tolist(), 'I_max': Inb.max(0).tolist()}, 'models': {}}
    every = int(round(hb / a.dt))
    for N in orders:
        t = time.time()
        sec = lie_secular(f, nvec, K2pp, N, D, log=lambda *x: None, Dfinal=a.dfinal)
        S = SP.concat(bk, list(sec.values())).consolidate()
        terms = [tuple(int(x) for x in e) + (complex(bk.to_mpc(cc)),) for e, cc in zip(S.E, S.C)]
        tsec = time.time() - t
        poly = ComplexPoly(terms)
        nsteps = int(round(a.years / a.dt))
        traj = rk4(poly, z0.astype(complex), a.dt, nsteps, every)[: len(R)]
        xi = math.sqrt(2) * traj.real; eta = -math.sqrt(2) * traj.imag
        xm, ym = xi @ O, eta @ O
        Im = 0.5 * (xm ** 2 + ym ** 2)
        g = [abs(fundamental_frequency(xm[:, j] + 1j * ym[:, j], hb)) for j in range(3)]
        d = {'terms': len(terms), 'secular_cpu_s': tsec, 'g': g,
             'g_rel_diff': [g[j] / g_nb[j] - 1 for j in range(3)],
             'I_mean_diff': (Im.mean(0) - Inb.mean(0)).tolist(), 'I_min_diff': (Im.min(0) - Inb.min(0)).tolist(),
             'I_max_diff': (Im.max(0) - Inb.max(0)).tolist(),
             'I_pointwise_maxdiff': np.abs(Im - Inb).max(0).tolist()}
        d['freq_pass'] = bool(max(abs(x) for x in d['g_rel_diff']) <= 1e-4)
        d['torus_pass'] = bool(max(max(abs(x) for x in d[k]) for k in ('I_mean_diff', 'I_min_diff', 'I_max_diff')) <= 1e-5 / 3)
        out['models'][str(N)] = d
        print(N, 'terms', len(terms), 'g rel', ['%+.3e' % x for x in d['g_rel_diff']],
              'I mean/min/max diff', ['%+.2e' % x for x in d['I_mean_diff']], ['%+.2e' % x for x in d['I_min_diff']],
              ['%+.2e' % x for x in d['I_max_diff']], 'sec %.0fs' % tsec, flush=True)
    out['cpu_s'] = time.process_time() - t0
    out['status'] = 'measured (H-bar coefficients in long double, flows float64 RK4, N-body block means)'
    json.dump(out, open(a.out, 'w'), indent=1)


if __name__ == '__main__':
    main()
