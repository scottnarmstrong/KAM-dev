#!/usr/bin/env python3
"""Fit the reference semi-major axes a*_j to SLG13 Appendix A coefficients.

The model coefficients are smooth functions of a* (through Lambda*, n*, alpha and the
Laplace coefficients).  We solve the nonlinear least-squares problem by Gauss-Newton with
central-difference Jacobians, using relative residuals (model - printed)/|printed|.

--set quad   : the 6 independent quadratic coefficients (xi-block; the eta-block is identical
               to rounding), 3 unknowns -> 3 degrees of freedom of over-determination.
--set two    : quadratic + every two-planet quartic coefficient.
--set all    : all 78 printed coefficients.
Usage: python3 -I applications/sjsu/scripts/fit_astar.py --set quad [--start a1 a2 a3]
"""
import argparse
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

import mpmath
import numpy as np

from compare_appendix_a import load_table, real_model
from sjsu_common import TABLE1


NSTAR = ['kepler']


def residuals(astar, table, order=2, D=4):
    real, _ = real_model(astar, order=order, D=D, nstar=NSTAR[0])
    r = []
    for powers, cs in table:
        ref = mpmath.mpf(cs)
        v = real.get(powers, mpmath.mpc(0)).real
        r.append(float((v - ref) / abs(ref)))
    return np.array(r)


def select(table, which):
    out = []
    for powers, cs in table:
        d = sum(powers)
        planets = sum(1 for j in range(3) if powers[j] + powers[3 + j] > 0)
        if which == 'quad' and d == 2 and sum(powers[3:]) == 0:
            out.append((powers, cs))
        elif which == 'two' and (d == 2 or planets <= 2):
            out.append((powers, cs))
        elif which == 'all':
            out.append((powers, cs))
    return out


def fit(table, start, order=2, iters=8, log=print):
    D = 4 if max(sum(p) for p, _ in table) <= 2 else 6
    x = [mpmath.mpf(s) for s in start]
    for it in range(iters):
        r0 = residuals(x, table, order, D)
        J = np.zeros((len(r0), 3))
        for j in range(3):
            h = x[j] * mpmath.mpf('1e-7')
            xp = list(x); xp[j] += h
            xm = list(x); xm[j] -= h
            J[:, j] = (residuals(xp, table, order, D) - residuals(xm, table, order, D)) / float(2 * h)
        step, *_ = np.linalg.lstsq(J, -r0, rcond=None)
        x = [x[j] + mpmath.mpf(float(step[j])) for j in range(3)]
        log(f'  it {it}: rms rel residual {np.sqrt(np.mean(r0**2)):.3e} max {np.max(np.abs(r0)):.3e} '
            f'step {np.max(np.abs(step)):.2e}  a* = {[mpmath.nstr(v, 16) for v in x]}')
        if np.max(np.abs(step)) < 1e-15 * 20:
            break
    r = residuals(x, table, order, D)
    # covariance-like sensitivity: d a / d (relative coefficient) via pseudo-inverse
    return x, r, J


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--set', default='quad', choices=['quad', 'two', 'all'])
    ap.add_argument('--order', type=int, default=2)
    ap.add_argument('--start', nargs=3, default=list(TABLE1['a']))
    ap.add_argument('--json')
    ap.add_argument('--nstar', default='kepler', choices=['kepler', 'corrected'])
    args = ap.parse_args()
    NSTAR[0] = args.nstar
    mpmath.mp.dps = 40
    table = select(load_table(), args.set)
    print(f'fitting a* to {len(table)} printed coefficients (set {args.set}, order {args.order}, n* {args.nstar})')
    x, r, J = fit(table, args.start, args.order)
    for (powers, cs), ri in zip(table, r):
        print(f'   {powers}  {cs:>26s}  rel residual {ri:+.3e}')
    print('a* =', [mpmath.nstr(v, 18) for v in x])
    print(f'rms relative residual {np.sqrt(np.mean(r**2)):.3e}, max {np.max(np.abs(r)):.3e}')
    if args.json:
        with open(args.json, 'w') as fh:
            json.dump({'set': args.set, 'order': args.order, 'nstar': args.nstar, 'astar': [mpmath.nstr(v, 20) for v in x],
                       'residuals': [{'powers': list(p), 'printed': c, 'rel_residual': float(ri)}
                                     for (p, c), ri in zip(table, r)]}, fh, indent=1)


if __name__ == '__main__':
    main()
