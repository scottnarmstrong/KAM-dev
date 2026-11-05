#!/usr/bin/env python3
"""Mass-order study: the SLG13 Lie steps kept to mass order N = 2..Nmax, compared with Appendix A.

For each N the secular Hamiltonian up to degree Dfinal is computed with lie_mimic.lie_secular
(exact pruning; the source's truncations at every stage) and compared with the 78 printed
coefficients.  N = 2 coincides with secular.py (strict order two).
Usage (repository root):
  python3 -I applications/sjsu/scripts/order_study.py --dfinal 4 --nmax 4 --nstar corrected \
      --astar-json applications/sjsu/validation/astar.json --csv applications/sjsu/validation/order_study_d4.csv
Cost (measured): N = 3 about 8 s, N = 4 about 4 min, N = 5 hours (single core).
"""
import argparse
import csv
import json
import os
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

import mpmath

from sjsu_common import Backend, physical_constants
from kepler_series import universal_series
from expansion import first_order_hamiltonian
from secular import to_real, nstar_split
from lie_mimic import lie_secular
from sparse import SP
from compare_appendix_a import load_table


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--dfinal', type=int, default=4)
    ap.add_argument('--nmax', type=int, default=4)
    ap.add_argument('--nstar', default='corrected', choices=['kepler', 'corrected'])
    ap.add_argument('--astar', nargs=3)
    ap.add_argument('--astar-json')
    ap.add_argument('--csv')
    args = ap.parse_args()
    mpmath.mp.dps = 40
    if args.astar:
        astar = [mpmath.mpf(s) for s in args.astar]
    else:
        astar = [mpmath.mpf(s) for s in json.load(open(args.astar_json))['astar']]
    bk = Backend('ld')
    c = physical_constants(astar)
    D = args.dfinal + args.nmax
    U = universal_series(D, 18)
    f = first_order_hamiltonian(bk, U, c, D=D, KF=16, log=lambda *a: None)
    nvec, f, corr = nstar_split(f, c, bk, args.nstar)
    K2pp = [bk.real(x) for x in c['K2pp']]
    table = [(p, cs) for p, cs in load_table() if sum(p) <= args.dfinal]
    cols = {}
    for N in range(2, args.nmax + 1):
        t = time.time()
        out = lie_secular(f, nvec, K2pp, N, D, log=lambda *a: None, Dfinal=args.dfinal)
        r = to_real(SP.concat(bk, list(out.values())).consolidate())
        cols[N] = {p: r.get(p, mpmath.mpc(0)).real for p, _ in table}
        print(f'N={N}: {time.time()-t:.1f}s', flush=True)
        for p, cs in table:
            ref = mpmath.mpf(cs)
            print(f'   {str(p):20s} printed {float(ref):+.6e}  N={N} {float(cols[N][p]):+.6e} '
                  f'rel {float((cols[N][p]-ref)/abs(ref)):+.3e}', flush=True)
        if args.csv:
            with open(args.csv, 'w', newline='') as fh:
                w = csv.writer(fh)
                w.writerow(['powers_xiJ_xiS_xiU_etaJ_etaS_etaU', 'planets', 'slg13_printed']
                           + sum([[f'order{M}', f'order{M}_rel_dev'] for M in sorted(cols)], []))
                for p, cs in table:
                    ref = mpmath.mpf(cs)
                    row = [' '.join(map(str, p)), sum(1 for j in range(3) if p[j] + p[3 + j]), cs]
                    for M in sorted(cols):
                        v = cols[M][p]
                        row += [mpmath.nstr(v, 17), mpmath.nstr((v - ref) / abs(ref), 4)]
                    w.writerow(row)


if __name__ == '__main__':
    main()
