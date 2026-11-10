#!/usr/bin/env python3
"""Gate verdicts G1-G6 from the lam results and the local runs (research scratch).

usage: analyze_gates.py RESULTS_DIR G2.json G6_LOCAL_DIR OUT.json
RESULTS_DIR is an unpacked lam return (res/, out/, log/).  Criteria (research plan section 4.3, literal):
  G1 PASS iff the F1 and Lambda_U gains at orders 3-5 are >= 20 per order at every sampled point, and the order-3
     rate is <= 2e-9 per yr.   (gains: remainder rates; order-3 rate: remainder + kept near-resonant floor)
  G2 PASS iff every normalized divisor stays >= 3e-3 at osculating Lambda for the R4 orders, and floor x 1e4 yr
     <= 1e-5.   (floor: kept near-resonant harmonics through order 3, from the G1 ladders)
  G3 PASS iff the Stage-II gains are >= 6 per order through order 4 and eps52 <= 0.15 over the tube.
  G4 PASS iff the R4 certificate is <= 1e8 coefficients after pruning.
  G6 PASS iff the secular frequencies agree to <= 1e-4 and the torus location is inside delta/3.
"""
import glob, json, os, re, sys
import numpy as np

R, G2F, G6D, OUT = sys.argv[1:5]
res = {}


def load(p):
    try:
        return json.load(open(p))
    except (OSError, ValueError):
        return None


# ---------------------------------------------------------------- G1 (+ G2 floor)
g1 = {}
for p in sorted(glob.glob(os.path.join(R, 'out/g1/p*.json'))):
    d = load(p)
    if d:
        g1[d['index']] = d
rows, fails = [], []
for i, d in sorted(g1.items()):
    L = d['ladder']
    row = {'index': i, 'kind': d['point'].get('kind', 'nominal')}
    for o in ('F1', 'LU'):
        row[o + '_rem'] = [L[r][o]['remainder'] for r in range(len(L))]
        row[o + '_gain'] = [L[r][o].get('gain_remainder') for r in range(1, len(L))]
        row[o + '_total3'] = L[3][o]['total']
        row[o + '_floor3'] = L[3][o]['floor_nr']
    rows.append(row)
    for o in ('F1', 'LU'):
        for r in (3, 4, 5):
            g = row[o + '_gain'][r - 1]
            if g is None or g < 20:
                fails.append({'index': i, 'obs': o, 'order': r, 'gain': g})
        if row[o + '_total3'] > 2e-9:
            fails.append({'index': i, 'obs': o, 'order3_total': row[o + '_total3']})
if rows:
    G = {o: np.array([r[o + '_gain'] for r in rows], dtype=float) for o in ('F1', 'LU')}
    REM = {o: np.array([r[o + '_rem'] for r in rows], dtype=float) for o in ('F1', 'LU')}
    res['G1'] = {'points': len(rows),
                 'gain_min_per_order': {o: G[o].min(0).tolist() for o in G},
                 'gain_median_per_order': {o: np.median(G[o], 0).tolist() for o in G},
                 'gain_max_per_order': {o: G[o].max(0).tolist() for o in G},
                 'rem_max_per_order': {o: REM[o].max(0).tolist() for o in REM},
                 'rem_median_per_order': {o: np.median(REM[o], 0).tolist() for o in REM},
                 'order3_total_max': {o: max(r[o + '_total3'] for r in rows) for o in ('F1', 'LU')},
                 'n_failing_terms': len(fails), 'failing_terms_first': fails[:30],
                 'points_failing': sorted({f['index'] for f in fails}),
                 'PASS': not fails}
    floor = {o: max(r[o + '_floor3'] for r in rows) for o in ('F1', 'LU')}
    res['G2_floor'] = {'floor3_max': floor, 'floor_x_1e4': {o: v * 1e4 for o, v in floor.items()},
                       'PASS_floor': all(v * 1e4 <= 1e-5 for v in floor.values())}
    cen = [d for d in g1.values() if d.get('census')]
    res['G4_census'] = {str(d['index']): d['census'] for d in cen}
# grid check
chk = {}
for p in sorted(glob.glob(os.path.join(R, 'out/g1/check128_p*.json'))):
    d = load(p)
    if d and d['index'] in g1:
        a, b = d['ladder'], g1[d['index']]['ladder']
        chk[d['index']] = {o: [a[r][o]['remainder'] / b[r][o]['remainder'] - 1 for r in range(len(a))]
                           for o in ('F1', 'LU')}
res['G1_grid_check_128_vs_64'] = chk

# ---------------------------------------------------------------- G2 divisors (local)
g2 = load(G2F)
if g2:
    res['G2_divisors'] = {'min_normalized_divisor_lower_bound': g2['min_over_points_normalized_divisor_lower_bound'],
                          'all_osc_within_rule': g2['all_osc_within_rule'],
                          'n_kept_nr_nominal': g2['points'][0]['n_kept_nr'],
                          'PASS_divisors': g2['min_over_points_normalized_divisor_lower_bound'] >= 3e-3
                          and g2['all_osc_within_rule']}
if 'G2_floor' in res and 'G2_divisors' in res:
    res['G2'] = {'PASS': res['G2_floor']['PASS_floor'] and res['G2_divisors']['PASS_divisors']}

# ---------------------------------------------------------------- G3
g3 = {}
for p in sorted(glob.glob(os.path.join(R, 'out/g3/p*.json'))):
    d = load(p)
    if d:
        g3[d['index']] = d
if g3:
    fails3 = []
    GS = []
    for i, d in sorted(g3.items()):
        L = d['stage2_ladder']
        gs = [L[r]['LS'].get('gain_remainder') for r in range(1, len(L))]
        gj = [L[r]['LJ'].get('gain_remainder') for r in range(1, len(L))]
        GS.append(gs)
        for r in range(1, 5):
            for nm, g in (('LS', gs[r - 1]), ('LJ', gj[r - 1])):
                if g is None or g < 6:
                    fails3.append({'index': i, 'obs': nm, 'order': r, 'gain': g})
        if d['eps52'] > 0.15:
            fails3.append({'index': i, 'eps52': d['eps52']})
    GS = np.array(GS, dtype=float)
    eps = [d['eps52'] for d in g3.values()]
    res['G3'] = {'points': len(g3), 'LS_gain_min_per_order': GS.min(0).tolist(),
                 'LS_gain_median_per_order': np.median(GS, 0).tolist(),
                 'LS_rem_median_per_order': np.median([[r['LS']['remainder'] for r in d['stage2_ladder']]
                                                       for d in g3.values()], 0).tolist(),
                 'eps52_range': [min(eps), max(eps)], 'n_failing_terms': len(fails3),
                 'failing_terms_first': fails3[:30], 'PASS': not fails3}

# ---------------------------------------------------------------- G5
def secs(s):
    m = re.match(r'([0-9.]+)(ms|s)', s)
    return float(m.group(1)) / (1000 if m.group(2) == 'ms' else 1)


kern, nat, walls = {}, {}, {}
for p in glob.glob(os.path.join(R, 'log/g5k_B*.out')):
    b = os.path.basename(p)[4:8]
    t = re.findall(r'type checking took ([0-9.]+m?s)', open(p).read())
    if t:
        kern[b] = max(secs(x) for x in t)
for p in glob.glob(os.path.join(R, 'log/g5n_B*.out')):
    b = os.path.basename(p)[4:8]
    t = re.findall(r'interpretation of \S+native_decide\S* took ([0-9.]+m?s)', open(p).read())
    if t:
        nat[b] = sum(secs(x) for x in t)
for p in glob.glob(os.path.join(R, 'res/g5*.json')):
    d = load(p)
    walls[d['id']] = (d['wall_s'], d.get('peak_rss_kb'))
exe = {}
try:
    for l in open(os.path.join(R, 'log/g5exe.out')):
        m = re.match(r'block (B\d+) ok=(\w+) best_ns=(\d+)', l)
        if m:
            exe[m.group(1)] = int(m.group(3)) / 1e9
except OSError:
    pass
if kern:
    K, Nn, X = sum(kern.values()), sum(nat.values()), sum(exe.values())
    kw = sum(v[0] for k, v in walls.items() if k.startswith('g5k'))
    nw = sum(v[0] for k, v in walls.items() if k.startswith('g5n'))
    res['G5'] = {'blocks': len(kern), 'kernel_typecheck_s': K, 'native_decide_interp_s': Nn, 'exe_compiled_s': X,
                 'kernel_file_wall_s': kw, 'native_file_wall_s': nw,
                 'ratio_kernel_over_native_decide': K / Nn if Nn else None,
                 'ratio_kernel_over_exe': K / X if X else None,
                 'ratio_file_wall_kernel_over_native': kw / nw if nw else None,
                 'kernel_peak_rss_gb_max': max((v[1] or 0) for k, v in walls.items() if k.startswith('g5k')) / 1048576,
                 'per_block_kernel_s_max': max(kern.values()), 'per_block_kernel_s_median': float(np.median(list(kern.values())))}

# ---------------------------------------------------------------- G6
g6 = {}
for p in sorted(glob.glob(os.path.join(R, 'out/g6/*.json'))) + sorted(glob.glob(os.path.join(G6D, '*.json'))):
    d = load(p)
    if d and 'models' in d:
        for N, m in d['models'].items():
            g6['N%s_d%d' % (N, d['dfinal'])] = {'g_rel_diff': m['g_rel_diff'], 'I_mean_diff': m['I_mean_diff'],
                                                 'I_min_diff': m['I_min_diff'], 'I_max_diff': m['I_max_diff'],
                                                 'freq_pass': m['freq_pass'], 'torus_pass': m['torus_pass'],
                                                 'nbody_g': d['nbody']['g'], 'window_years': d['window_years']}
res['G6'] = g6
json.dump(res, open(OUT, 'w'), indent=1, default=float)
print(json.dumps({k: (v.get('PASS') if isinstance(v, dict) and 'PASS' in v else '...') for k, v in res.items()}))
