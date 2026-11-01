#!/usr/bin/env python3
"""Write validation/astar.json from the N-body runs (the a* input of build_model.py).

  python3 -I applications/sjsu/scripts/nbody.py --years 1e6 --dt 0.5 --ic poincare --out run1e6.json
  python3 -I applications/sjsu/scripts/nbody.py --years 1e5 --dt 0.5 --ic poincare --out run1e5.json
  python3 -I applications/sjsu/scripts/write_astar.py run1e6.json run1e5.json [--out validation/astar.json]

a* is the 1 Myr time average of the Poincare semi-major axes (checkpoint t = 1e6 of the first run,
copied as written by nbody.py); the window dependence compares it with the t = 3e5 checkpoint; the
mean motions come from the last checkpoint of the second run (least-squares slopes of the mean
longitudes).  The 1e6-yr run must have been made with a version of nbody.py that records the
checkpoints 3e5 and 1e6 (the default checkpoint list).
"""
import argparse
import json
import os

APP = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('run1e6')
    ap.add_argument('run1e5')
    ap.add_argument('--out', default=os.path.join(APP, 'validation', 'astar.json'))
    args = ap.parse_args()
    d = json.load(open(args.run1e6))
    mm = json.load(open(args.run1e5))
    cp = {int(c['t']): c for c in d['checkpoints']}
    a = cp[1000000]['aP_mean']
    rel = [abs(float(cp[1000000]['aP_mean'][j]) - float(cp[300000]['aP_mean'][j])) / float(a[j]) for j in range(3)]
    out = {'astar': a,
           'definition': ('time average over 0 <= t <= 1e6 yr of the Poincare semi-major axes a_j (from r_j and '
                          'r~_j/beta_j with mu_j = G(m0+m_j)) along the planar SJSU N-body flow from SLG13 Table 1 read '
                          'as Poincare elements; WH democratic-heliocentric map, Yoshida 4th order, dt = 0.5 yr, '
                          'float64 (scripts/nbody.py)'),
           'window_dependence_rel_1e6_vs_3e5': rel,
           'measured_mean_motions_1e5yr': mm['checkpoints'][-1]['mean_motion'],
           'measured_2n1_minus_5n2': mm['checkpoints'][-1]['two_n1_minus_five_n2'],
           'measured_3n1_minus_5n2_minus_7n3': mm['checkpoints'][-1]['three_body'],
           'heliocentric_osculating_average_1e6yr': cp[1000000]['aH_mean'],
           'max_rel_energy_error': d['max_rel_energy_error'],
           'command': 'python3 -I applications/sjsu/scripts/nbody.py --years 1e6 --dt 0.5 --ic poincare',
           'status': 'measured (floating point); SLG13 do not print their a*_j nor the integration length'}
    with open(args.out, 'w') as fh:
        json.dump(out, fh, indent=1)


if __name__ == '__main__':
    main()
