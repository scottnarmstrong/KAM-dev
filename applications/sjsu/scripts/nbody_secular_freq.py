#!/usr/bin/env python3
"""Secular frequencies of the full planar N-body flow versus the SJSU18 model (physical check).

Input: the osculating Poincare (xi, eta) sampled along the N-body run
  python3 -I nbody.py --years 3e6 --dt 0.5 --ic poincare --sample 50 --sample-out samples.npz
The modal signals x_j + i y_j = (O^T xi)_j + i (O^T eta)_j, with O the eigenvectors of the model's
quadratic part, are frequency-analysed (Hann window, refined peak; freq_check.fundamental_frequency).
Frequencies are intrinsic, so the osculating short-period terms only add small lines.
They are compared with the model's own frequencies from the Table 1 point
(validation/frequencies_table1secular.json, frequencies_table1raw.json).
Writes validation/nbody_secular_frequencies.json.
Usage: python3 -I applications/sjsu/scripts/nbody_secular_freq.py samples.npz
"""
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
APP = os.path.abspath(os.path.join(HERE, '..'))

import numpy as np

from freq_check import ComplexPoly, from_model, fundamental_frequency


def main():
    path = sys.argv[1]
    d = np.load(path)
    h = float(d['dt'])
    xi, eta = d['xi'], d['eta']
    poly = ComplexPoly(from_model(os.path.join(APP, 'data', 'sjsu18-o2.json')))
    A = poly.quad_matrix()
    A = 0.5 * (A + A.T)
    w, V = np.linalg.eigh(A)
    order = np.argsort(-np.abs(w)); w = w[order]; V = V[:, order]
    X = xi @ V
    Y = eta @ V
    res = {'samples': len(xi), 'sampling_yr': h, 'span_yr': h * (len(xi) - 1), 'nu_linear_model': w.tolist()}
    om = []
    for span in (len(xi), len(xi) // 2):
        om.append([fundamental_frequency(X[:span, j] + 1j * Y[:span, j], h) for j in range(3)])
    res['omega_nbody_full_span'] = om[0]
    res['omega_nbody_half_span'] = om[1]
    res['modal_R_mean'] = list(np.mean(np.hypot(X, Y), axis=0))
    for name in ('table1secular', 'table1raw'):
        f = os.path.join(APP, 'validation', f'frequencies_{name}.json')
        if os.path.exists(f):
            r = [x for x in json.load(open(f)) if x['label'].startswith('sjsu18')][0]
            res[f'omega_model_{name}'] = r['omega']
            res[f'rel_diff_model_{name}'] = [(r['omega'][j] - om[0][j]) / abs(om[0][j]) for j in range(3)]
    with open(os.path.join(APP, 'validation', 'nbody_secular_frequencies.json'), 'w') as fh:
        json.dump(res, fh, indent=1)
    print(json.dumps(res, indent=1))


if __name__ == '__main__':
    main()
