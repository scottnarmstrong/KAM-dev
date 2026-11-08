#!/usr/bin/env python3
"""Write jobs.tsv for the SJSU-FULL gates lam batch (G1, G1 grid check, G3, G3 grid check, G6, G5).
Caps are 1.5-2x the peaks extrapolated from local tiny runs (memory ~ grid points): G1 64x64x32 N=5 ~21 GB,
G3 48x48x24 ~28 GB, G1 128x128x64 N=4 ~45-60 GB, G3 64x64x32 ~66 GB; G5 kernel blocks unknown (G8k: 4.9 GB)."""
import json, sys
out = sys.argv[1]
n_g5 = int(sys.argv[2])
F = 'cd {REPO}/scripts/sjsu/full && '
rows = []
idx = list(range(-1, 56))
# grid checks and census first (largest caps)
for i in (-1, 0):
    rows.append(('g1c_p%d' % i, '100G', 21600, 'g1', F + '{PY} ladder.py points.json %d {RES}/g1/check128_p%d.json --grid 128,128,64 --N 4 --quiet' % (i, i)))
    rows.append(('g3c_p%d' % i, '110G', 21600, 'g3', F + '{PY} stage2.py points.json %d {RES}/g3/check64_p%d.json --grid 64,64,32 --NI 3 --M 6 --quiet' % (i, i)))
for i in idx:
    extra = ' --census' if i in (-1, 0) else ''
    rows.append(('g1_p%d' % i, '48G' if extra else '32G', 14400, 'g1',
                 F + '{PY} ladder.py points.json %d {RES}/g1/p%d.json --grid 64,64,32 --N 5 --quiet%s' % (i, i, extra)))
for i in idx:
    rows.append(('g3_p%d' % i, '44G', 21600, 'g3', F + '{PY} stage2.py points.json %d {RES}/g3/p%d.json --grid 48,48,24 --NI 3 --M 6 --quiet' % (i, i)))
for (N, d) in ((4, 6), (4, 8), (2, 10), (3, 10)):
    rows.append(('g6_n%dd%d' % (N, d), '32G', 43200, 'g6',
                 F + '{PY} g6_model_gap.py {REPO}/data/main_20Myr.bin {RES}/g6/n%dd%d.json --orders %d --dfinal %d --years 1e7' % (N, d, N, d)))
for b in range(n_g5):
    rows.append(('g5k_B%03d' % b, '48G', 7200, 'g5k', 'cd {G5} && LEAN_PATH={G5}/.lake/build/lib/lean LEAN_NUM_THREADS=1 {LEAN} Kernel/B%03d.lean' % b))
    rows.append(('g5n_B%03d' % b, '24G', 7200, 'g5n', 'cd {G5} && LEAN_PATH={G5}/.lake/build/lib/lean LEAN_NUM_THREADS=1 {LEAN} Native/B%03d.lean' % b))
rows.append(('g5exe', '32G', 7200, 'g5exe', '{G5}/.lake/build/bin/g5check {G5}/blocks.txt'))
with open(out, 'w') as f:
    f.write('# id\tcap\ttimeout_s\tkind\tcommand\n')
    for r in rows:
        f.write('\t'.join(str(x) for x in r) + '\n')
print(len(rows), 'jobs')
