#!/usr/bin/env python3
"""Precision of the SJSU18-O2 coefficients: float64, long double and mpmath (40 digits) against
mpmath at 50 digits.  Writes validation/precision.json (maximal relative difference per degree).
Usage: python3 -I applications/sjsu/scripts/precision_check.py [--D 18] [--out path]   (~8 CPU-min)
"""
import argparse
import json
import os
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
APP = os.path.abspath(os.path.join(HERE, '..'))

import mpmath

from sjsu_common import Backend
from secular import compute_secular


def run(name, dps, astar_s, D):
    bk = Backend(name, dps=dps)
    mpmath.mp.dps = dps
    astar = [mpmath.mpf(x) for x in astar_s]
    t = time.time()
    out = compute_secular(astar, bk, D=D, res=(D >= 16), nstar='corrected', log=lambda *a: None)
    tot = out['total']
    res = {tuple(int(x) for x in e): bk.to_mpc(c) for e, c in zip(tot.E, tot.C)}
    return res, time.time() - t


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--D', type=int, default=18)
    ap.add_argument('--out', default=os.path.join(APP, 'validation', 'precision.json'))
    args = ap.parse_args()
    astar_s = json.load(open(os.path.join(APP, 'validation', 'astar.json')))['astar']
    runs = {}
    for name, dps in (('f64', 40), ('ld', 40), ('mp', 40), ('mp', 50)):
        key = f'{name}{dps}' if name == 'mp' else name
        runs[key], dt = run(name, dps, astar_s, args.D)
        print(key, f'{dt:.1f}s', len(runs[key]), flush=True)
    mpmath.mp.dps = 50
    ref = runs['mp50']
    report = {'D': args.D, 'reference': 'mpmath 50 digits', 'max_relative_difference_by_degree': {}}
    for key in ('f64', 'ld', 'mp40'):
        bydeg = {}
        for k, v in ref.items():
            if sum(k) == 0 or v == 0:
                continue
            r = float(abs(runs[key].get(k, 0) - v) / abs(v))
            d = str(sum(k))
            bydeg[d] = max(bydeg.get(d, 0.0), r)
        report['max_relative_difference_by_degree'][key] = bydeg
        print(key, {d: '%.1e' % x for d, x in sorted(bydeg.items(), key=lambda t: int(t[0]))})
    report['note'] = ('Coefficients near exact cancellation lose up to ~5 digits at degree 14-18. The published '
                      'file is the mpmath 40-digit build written to 25 significant digits; its agreement with the '
                      '50-digit build bounds the arithmetic error of the published digits.')
    with open(args.out, 'w') as fh:
        json.dump(report, fh, indent=1)


if __name__ == '__main__':
    main()
