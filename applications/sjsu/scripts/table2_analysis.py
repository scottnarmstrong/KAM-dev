#!/usr/bin/env python3
"""Consistency analysis of SLG13 Table 2 / eq. (24) with Table 1 (source issue SJSU-E2).

For a rotation-invariant quadratic part H2 = (1/2) sum A_ij (xi_i xi_j + eta_i eta_j), every
symplectic diagonalization (xi, eta) = D(x, y) is, for distinct frequencies, an orthogonal O applied
to x and to y alike, up to independent rotations of each mode plane.  Hence the modal amplitudes
R_j = sqrt(x_j^2 + y_j^2) are fixed by the point, and the 2x2 Gram matrix
G = [[|xi|^2, xi.eta], [xi.eta, |eta|^2]] = [[|x|^2, x.y], [x.y, |y|^2]] is fixed up to a common
rotation of all planes (which preserves tr G and det G).  We compare these invariants for the
Table 1 point (raw Poincare and first-order secular), Table 2, and eq. (24).
Writes validation/table2_analysis.json.
"""
import itertools
import json
import math
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
APP = os.path.abspath(os.path.join(HERE, '..'))

import numpy as np

from sjsu_common import TABLE2, SLG13_RADII


def gram(a, b):
    return np.array([[a @ a, a @ b], [a @ b, b @ b]])


def main():
    m = json.load(open(os.path.join(APP, 'validation', 'table2_map_poincare_order1.json')))
    m0 = json.load(open(os.path.join(APP, 'validation', 'table2_map_poincare_order0.json')))
    O = np.array(m['O'])
    xiP = np.array(m['xi_eta_poincare'][:3]); etaP = np.array(m['xi_eta_poincare'][3:])
    xiS = np.array(m['xi_eta_secular'][:3]); etaS = np.array(m['xi_eta_secular'][3:])
    x2 = np.array([float(s) for s in TABLE2['x0']]); y2 = np.array([float(s) for s in TABLE2['y0']])
    R24 = np.array([float(s) for s in SLG13_RADII])
    out = {}
    for name, (a, b) in {'table1_poincare_raw': (xiP, etaP), 'table1_secular_first_order': (xiS, etaS),
                         'table2_xy': (x2, y2)}.items():
        G = gram(a, b)
        out[name] = {'AMD_C': float(np.trace(G) / 2), 'gram_trace': float(np.trace(G)), 'gram_det': float(np.linalg.det(G))}
    out['R_table2'] = list(np.hypot(x2, y2))
    out['R_eq24'] = list(R24)
    out['R_eq24_AMD_C'] = float((R24 ** 2).sum() / 2)
    out['R_model_first_order'] = [r['R'] for r in m['rows']]
    out['R_model_raw'] = [r['R'] for r in m0['rows']]
    # best eigenvector-sign choice mapping Table 2 into (xi, eta) closest to the secular Table 1 point
    best = []
    for signs in itertools.product((1, -1), repeat=3):
        S = O * np.array(signs)
        xi2, eta2 = S @ x2, S @ y2
        d = math.sqrt(((xi2 - xiS) ** 2).sum() + ((eta2 - etaS) ** 2).sum())
        best.append((d, signs, list(xi2), list(eta2)))
    best.sort(key=lambda t: t[0])
    out['sign_search'] = [{'distance_to_table1_secular': d, 'signs': s, 'xi': xi, 'eta': eta} for d, s, xi, eta in best]
    out['table1_secular_norm'] = float(math.sqrt((xiS ** 2).sum() + (etaS ** 2).sum()))
    with open(os.path.join(APP, 'validation', 'table2_analysis.json'), 'w') as fh:
        json.dump(out, fh, indent=1)
    for k in ('table1_poincare_raw', 'table1_secular_first_order', 'table2_xy'):
        print(k, out[k])
    print('R table2', out['R_table2'], ' R eq24', out['R_eq24'], 'C(eq24)', out['R_eq24_AMD_C'])
    print('R model (first-order map)', out['R_model_first_order'])
    print('best sign choice', best[0][1], 'distance', best[0][0], 'vs |point|', out['table1_secular_norm'],
          '; worst', best[-1][0])


if __name__ == '__main__':
    main()
