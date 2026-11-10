#!/usr/bin/env python3
"""Slow sample points of the R4 tube (research scratch).

Points 0..47: block means (xi, eta, Lambda) of the 1-Gyr N-body run (4416-yr blocks) every 24 blocks
(~106 kyr) over the first ~5.1 Myr, i.e. across >= 9 cycles of the slowest secular mode.  Points 48..55: the
eight corners dLambda_j = +/- 5e-5 (Lambda''-windows of width 1e-4) at the first block mean.  The nominal point
(Table-1 secular xi, eta at Lambda*) is recorded separately; it is the point of E6.
usage: make_points.py MAIN.bin OUT.json
"""
import itertools, json, os, sys
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import model as M

rows = np.fromfile(sys.argv[1], dtype=np.float64).reshape(-1, 26)
pts = []
for i in range(48):
    r = rows[24 * i]
    pts.append({'kind': 'orbit_block_mean', 't_end_yr': float(r[0]), 'xi': r[1:4].tolist(), 'eta': r[4:7].tolist(),
                'Lambda': r[7:10].tolist()})
r = rows[0]
for s in itertools.product((1, -1), repeat=3):
    L = r[7:10] + 5e-5 * np.array(s)
    pts.append({'kind': 'window_corner', 'signs': list(s), 't_end_yr': float(r[0]), 'xi': r[1:4].tolist(),
                'eta': r[4:7].tolist(), 'Lambda': L.tolist()})
out = {'nominal': {'xi': M.XI0.tolist(), 'eta': M.ETA0.tolist(), 'Lambda': M.LAM_STAR.tolist()},
       'points': pts, 'source': os.path.basename(sys.argv[1])}
json.dump(out, open(sys.argv[2], 'w'), indent=1)
print(len(pts), 'points')
