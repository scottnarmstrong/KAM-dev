#!/usr/bin/env python3
"""Finite-time transport diagnostic, not a proof of nonexistence of a circle."""
import argparse
import json
import resource
import time
from pathlib import Path
import numpy as np
from diagnostics import flow


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--out', required=True)
    ap.add_argument('--periods', type=int, default=1024)
    ap.add_argument('--steps', type=int, default=32)
    a = ap.parse_args()
    t0, c0 = time.time(), time.process_time()
    rows = []
    for eps in (.0012, .003):
        for controlled in (False, True):
            initial = np.arange(64)/64
            q, p = initial.copy(), np.full(64, .31 if eps == .0012 else .27)
            target = .39 if eps == .0012 else .45
            pmax = p.copy()
            first = np.full(64, -1, dtype=int)
            for period in range(a.periods):
                q, p = flow(q % 1, p, eps, controlled, a.steps)
                pmax = np.maximum(pmax, p)
                first[(p > target) & (first < 0)] = period+1
            earliest = int(np.argmin(np.where(first < 0, a.periods+1, first)))
            row = dict(eps=eps, controlled=controlled, steps=a.steps, periods=a.periods,
                       initial_p=.31 if eps == .0012 else .27, target=target,
                       max_p=float(np.max(pmax)), crossings=int(np.sum(first >= 0)),
                       earliest_period=int(first[earliest]), initial_q=float(initial[earliest]))
            if first[earliest] > 0:
                for steps in (64, 128, 256):
                    qx, px = np.array([initial[earliest]]), np.array([row['initial_p']])
                    maxx = px[0]
                    for _ in range(first[earliest]):
                        qx, px = flow(qx % 1, px, eps, controlled, steps)
                        maxx = max(maxx, float(px[0]))
                    row[f'refine_{steps}_maxp'] = maxx
                    row[f'refine_{steps}_endp'] = float(px[0])
            rows.append(row)
            print(json.dumps(row), flush=True)
    result = dict(rows=rows, wall_seconds=time.time()-t0, cpu_seconds=time.process_time()-c0,
                  maxrss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)
    Path(a.out).write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='rows'}), flush=True)


if __name__ == '__main__':
    main()
