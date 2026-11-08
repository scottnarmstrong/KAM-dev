#!/usr/bin/env python3
"""Sensitivity of SJSU18-O2 to the recipe choices the sources leave open.

Variants (each a full degree-18 run in long double, about 20 s):
  base        : n* corrected, D1 = 6, eq. (12) weight 1/2 (the published file's choices)
  res_lie     : weight 1 on the part of h_res_0 that chi_res does not remove (exact Lie coefficient)
  D1_9        : chi_1, chi_2 up to degree 9 (SLG13's closing remark) instead of 6 (eqs. (6)-(7), GLS17)
  nstar_kepler: Kepler frequencies at Lambda* in the homological equations
  astar_3e5   : a* averaged over 3e5 instead of 1e6 years (window dependence)
For each variant the maximal and median relative change of the coefficients, per degree, with
respect to the base is written to validation/sensitivity.json.
Usage: python3 -I applications/sjsu/scripts/sensitivity.py
"""
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

A_3E5 = ['5.2023752', '9.55443776', '19.21504489']   # nbody.py checkpoint t = 3e5 yr (validation/astar.json run)


def run(astar, **kw):
    bk = Backend('ld')
    t = time.time()
    out = compute_secular([mpmath.mpf(s) for s in astar], bk, D=18, res=True, log=lambda *a: None, **kw)
    tot = out['total']
    return {tuple(int(x) for x in e): bk.to_mpc(c).real for e, c in zip(tot.E, tot.C) if sum(e) > 0}, time.time() - t


def main():
    mpmath.mp.dps = 40
    astar = json.load(open(os.path.join(APP, 'validation', 'astar.json')))['astar']
    base, _ = run(astar, nstar='corrected', D1=6, res_weight='printed')
    variants = {
        'res_lie': dict(astar=astar, nstar='corrected', D1=6, res_weight='lie'),
        'D1_9': dict(astar=astar, nstar='corrected', D1=9, res_weight='printed'),
        'nstar_kepler': dict(astar=astar, nstar='kepler', D1=6, res_weight='printed'),
        'astar_3e5': dict(astar=A_3E5, nstar='corrected', D1=6, res_weight='printed'),
    }
    report = {'base': 'n* corrected, D1 = 6, eq. (12) weight 1/2, a* = validation/astar.json', 'variants': {}}
    for name, kw in variants.items():
        a = kw.pop('astar')
        res, dt = run(a, **kw)
        bydeg = {}
        for k, v in base.items():
            d = str(sum(k))
            r = float(abs(res.get(k, 0) - v) / abs(v)) if v != 0 else 0.0
            bydeg.setdefault(d, []).append(r)
        summary = {d: {'max': max(r), 'median': sorted(r)[len(r) // 2]} for d, r in bydeg.items()}
        report['variants'][name] = {'settings': kw | {'astar': a}, 'relative_change_by_degree': summary,
                                    'seconds': dt}
        print(name, {d: '%.1e/%.1e' % (s['median'], s['max']) for d, s in sorted(summary.items(), key=lambda t: int(t[0]))},
              flush=True)
    with open(os.path.join(APP, 'validation', 'sensitivity.json'), 'w') as fh:
        json.dump(report, fh, indent=1)


if __name__ == '__main__':
    main()
