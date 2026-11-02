#!/usr/bin/env python3
"""Compare the reconstructed secular Hamiltonian (degrees 2 and 4) with SLG13 Appendix A.

Usage (from the repository root):
  python3 -I applications/sjsu/scripts/compare_appendix_a.py --astar A1 A2 A3 [--order 1|2] [--csv out.csv]
Only degrees <= 4 are needed, so the expansion is run with D = 6 (all contributions to degree <= 4
are included: see secular.py).  The table JSON is scripts/sjsu/slg13_quartic.json (78 terms).
"""
import argparse
import csv
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
REPO = os.path.abspath(os.path.join(HERE, '..', '..', '..'))

import mpmath

from sjsu_common import Backend, TABLE1
from secular import compute_secular, to_real
from sparse import SP


def load_table():
    with open(os.path.join(REPO, 'scripts', 'sjsu', 'slg13_quartic.json')) as fh:
        d = json.load(fh)
    return [(tuple(t['powers']), t['coefficient']) for t in d['terms']]


def real_model(astar, order=2, backend='ld', D=6, quiet=True, D1=6, nstar='kepler'):
    bk = Backend(backend)
    out = compute_secular(astar, bk, D=D, D1=D1, res=False, log=(lambda *a: None) if quiet else print, nstar=nstar)
    comps = [out['first']]
    if order >= 2:
        comps += [out['second_chi1'], out['second_chi2']]
    tot = SP.concat(bk, comps).consolidate()
    return to_real(tot), out


def compare(real, table):
    rows = []
    for powers, cs in table:
        ref = mpmath.mpf(cs)
        v = real.get(powers, mpmath.mpc(0))
        rows.append((powers, cs, v.real, v.imag, (v.real - ref) / abs(ref)))
    return rows


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--astar', nargs=3, default=list(TABLE1['a']))
    ap.add_argument('--order', type=int, default=2)
    ap.add_argument('--backend', default='ld')
    ap.add_argument('--csv')
    args = ap.parse_args()
    mpmath.mp.dps = 40
    real, out = real_model([mpmath.mpf(x) for x in args.astar], args.order, args.backend)
    rows = compare(real, load_table())
    worst = 0
    for powers, cs, re, im, rel in rows:
        worst = max(worst, abs(rel))
        print(f'{str(powers):22s} {cs:>26s} {mpmath.nstr(re, 17):>26s} rel {mpmath.nstr(rel, 3):>10s} im {mpmath.nstr(im, 2)}')
    print('worst relative deviation:', mpmath.nstr(worst, 3))
    if args.csv:
        with open(args.csv, 'w', newline='') as fh:
            w = csv.writer(fh)
            w.writerow(['powers_xiJ_xiS_xiU_etaJ_etaS_etaU', 'slg13_printed', 'reconstructed', 'relative_deviation'])
            for powers, cs, re, im, rel in rows:
                w.writerow([' '.join(map(str, powers)), cs, mpmath.nstr(re, 20), mpmath.nstr(rel, 6)])


if __name__ == '__main__':
    main()
