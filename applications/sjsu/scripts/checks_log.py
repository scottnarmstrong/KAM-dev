#!/usr/bin/env python3
"""Spot checks quoted in the report, stored in validation/checks.json (about 1 CPU-minute).

  1. Exact Kepler series (degree 18) vs a direct Kepler solve in mpmath, e = 0.06, 0.03, 0.015:
     the error must scale like e^19.
  2. Laplace coefficients b_{1/2}^{(k)} and alpha d/dalpha b vs quadrature (k = 0, 1, 2).
  3. The order-tracked Lie engine (lie_mimic.py, N = 2) vs the strict order-two code (secular.py):
     every coefficient of degree <= 4 (D = 6).
  4. N-body step size: 2000-yr averages of a_P at dt = 0.5 and 0.25 yr.
The harmonic-by-harmonic DFT check of the expansion is stored separately as
validation/check_expansion.log (python3 -I applications/sjsu/scripts/check_expansion.py).
Usage: python3 -I applications/sjsu/scripts/checks_log.py
"""
import json
import os
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
APP = os.path.abspath(os.path.join(HERE, '..'))

import mpmath


def kepler_check():
    from kepler_series import kepler_Z
    mpmath.mp.dps = 50
    Z = kepler_Z(18)
    out = {}
    for es in ('0.06', '0.03', '0.015'):
        e, varpi, M = mpmath.mpf(es), mpmath.mpf('0.3'), mpmath.mpf(1)
        E = M
        for _ in range(80):
            E = E - (E - e * mpmath.sin(E) - M) / (1 - e * mpmath.cos(E))
        Zd = mpmath.mpc(mpmath.cos(E) - e, mpmath.sqrt(1 - e * e) * mpmath.sin(E)) * mpmath.exp(-1j * M)
        u = mpmath.sqrt(2 * (1 - mpmath.sqrt(1 - e * e))) * mpmath.exp(1j * varpi)
        w = mpmath.exp(1j * (M + varpi))
        Zs = sum(mpmath.mpf(c.numerator) / c.denominator * u ** p * mpmath.conj(u) ** q * w ** (q - p)
                 for (p, q), c in Z.items())
        out[es] = float(abs(Zs - Zd))
    return out


def laplace_check():
    from laplace import laplace_derivatives
    mpmath.mp.dps = 40
    al = mpmath.mpf('0.5455')
    T = laplace_derivatives(al, 3, 3)
    worst = 0.0
    for k in range(3):
        q = mpmath.quad(lambda p: mpmath.cos(k * p) / mpmath.sqrt(1 + al ** 2 - 2 * al * mpmath.cos(p)), [0, mpmath.pi]) * 2 / mpmath.pi
        d = mpmath.diff(lambda x: mpmath.quad(lambda p: mpmath.cos(k * p) / mpmath.sqrt(1 + x ** 2 - 2 * x * mpmath.cos(p)),
                                              [0, mpmath.pi]) * 2 / mpmath.pi, al) * al
        worst = max(worst, float(abs(T[k][0] - q)), float(abs(T[k][1] - d)))
    return {'alpha': '0.5455', 'max_abs_difference': worst}


def lie_check():
    from sjsu_common import Backend, physical_constants
    from kepler_series import universal_series
    from expansion import first_order_hamiltonian
    from secular import compute_secular, nstar_split
    from lie_mimic import lie_secular
    from sparse import SP
    mpmath.mp.dps = 40
    bk = Backend('ld')
    astar = [mpmath.mpf(s) for s in json.load(open(os.path.join(APP, 'validation', 'astar.json')))['astar']]
    D = 6
    ref = compute_secular(astar, bk, D=D, res=False, nstar='corrected', log=lambda *a: None)
    strict = SP.concat(bk, [ref['first'], ref['second_chi1'], ref['second_chi2']]).consolidate()
    c = physical_constants(astar)
    f = first_order_hamiltonian(bk, universal_series(D, 18), c, D=D, KF=16, log=lambda *a: None)
    nvec, f, _ = nstar_split(f, c, bk, 'corrected')
    out = lie_secular(f, nvec, [bk.real(x) for x in c['K2pp']], 2, D, log=lambda *a: None, Dfinal=4)
    mimic = SP.concat(bk, list(out.values())).consolidate()
    a = {tuple(int(x) for x in e): bk.to_mpc(v) for e, v in zip(strict.E, strict.C) if 0 < sum(e) <= 4}
    b = {tuple(int(x) for x in e): bk.to_mpc(v) for e, v in zip(mimic.E, mimic.C) if 0 < sum(e) <= 4}
    worst = max(float(abs(a.get(k, 0) - b.get(k, 0)) / abs(a[k])) for k in a)
    return {'terms_compared': len(a), 'extra_terms_in_mimic': len(set(b) - set(a)), 'max_rel_difference': worst}


def nbody_dt_check():
    res = {}
    for dt in ('0.5', '0.25'):
        out = os.path.join(APP, '..', '..', '.nbody_dt_check.json')
        subprocess.run([sys.executable, '-I', os.path.join(HERE, 'nbody.py'), '--years', '2000', '--dt', dt,
                        '--checkpoints', '2000', '--out', out], check=True, capture_output=True)
        res[dt] = [float(x) for x in json.load(open(out))['checkpoints'][-1]['aP_mean']]
        os.remove(out)
    rel = [abs(res['0.5'][j] - res['0.25'][j]) / res['0.25'][j] for j in range(3)]
    return {'aP_mean_2000yr': res, 'max_rel_difference': max(rel)}


def main():
    report = {'kepler_series_abs_error_by_e': kepler_check(), 'laplace_vs_quadrature': laplace_check(),
              'lie_mimic_N2_vs_secular_degree_le_4': lie_check(), 'nbody_step_size_2000yr': nbody_dt_check()}
    with open(os.path.join(APP, 'validation', 'checks.json'), 'w') as fh:
        json.dump(report, fh, indent=1)
    print(json.dumps(report, indent=1))


if __name__ == '__main__':
    main()
