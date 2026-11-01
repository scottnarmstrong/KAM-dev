#!/usr/bin/env python3
"""Regression test for the committed SJSU18 model file(s).

Default (fast, ~1 minute):
  1. data/MANIFEST.sha256 matches every listed file.
  2. Structure of each model JSON: all complex monomials charge-balanced (rotation invariance);
     reversibility (c_PQ = c_QP, real form even in eta); even degrees 2..D; complex and real
     forms agree on every monomial of degree <= 6 (recomputed); components sum to the total.
  3. Recomputation: the degree <= 4 part is recomputed from scratch (D = 6 run, same parameters;
     degree D of a run also needs f of degree D + 1, so only degrees <= D - 2 are compared)
     and compared with the file (relative tolerance 1e-15 on coefficients above 1e-6 of the max).
  4. Laplace-Lagrange: the first-order quadratic part agrees with the classical formula.
--full recomputes the whole model in mpmath (about 3 CPU-min) and compares every coefficient with
the 25 written digits (tolerance 1e-23 relative).
Exit status 0 on success.
Usage: python3 -I applications/sjsu/scripts/test_regression.py [--full]
"""
import argparse
import hashlib
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
APP = os.path.abspath(os.path.join(HERE, '..'))

import mpmath
import numpy as np

from sjsu_common import Backend
from secular import compute_secular, to_real
from sparse import SP

FAIL = []


def check(cond, msg):
    print(('PASS: ' if cond else 'FAIL: ') + msg)
    if not cond:
        FAIL.append(msg)


def manifest():
    path = os.path.join(APP, 'data', 'MANIFEST.sha256')
    ok = True
    n = 0
    with open(path) as fh:
        for line in fh:
            if not line.strip():
                continue
            h, name = line.split(None, 1)
            name = name.strip()
            got = hashlib.sha256(open(os.path.join(APP, 'data', name), 'rb').read()).hexdigest()
            ok &= (got == h)
            n += 1
    check(ok and n > 0, f'data/MANIFEST.sha256: {n} files match')


def structure(model):
    terms = model['complex_form']['terms']
    D = model['truncations']['degree_xi_eta']
    E = np.array([t[:6] for t in terms])
    C = {tuple(t[:6]): mpmath.mpf(t[6]) for t in terms}
    charge = E[:, 0::2].sum(1) - E[:, 1::2].sum(1)
    check(bool((charge == 0).all()), f'{model["name"]}: all {len(terms)} complex monomials charge-balanced')
    deg = E.sum(1)
    check(bool((deg % 2 == 0).all() and deg.min() >= 2 and deg.max() <= D), 'even degrees in [2, D]')
    sym = True
    for k, v in C.items():
        kk = (k[1], k[0], k[3], k[2], k[5], k[4])
        w = C.get(kk)
        if w is None or abs(w - v) > mpmath.mpf('1e-17') * max(abs(v), mpmath.mpf('1e-300')) + mpmath.mpf('1e-40'):
            sym = False
            break
    check(sym, 'reversibility: c_PQ = c_QP')
    rterms = model['real_form']['terms']
    check(all(sum(t[3:6]) % 2 == 0 for t in rterms), f'real form ({len(rterms)} terms) even in eta')
    # components sum to the total
    tot = {}
    for name, ct in model['components_complex_form'].items():
        for t in ct:
            tot[tuple(t[:6])] = tot.get(tuple(t[:6]), 0) + mpmath.mpf(t[6])
    worst = max(abs(tot.get(k, 0) - v) / abs(v) for k, v in C.items() if v != 0)
    check(worst < 1e-17, f'components sum to the total (max rel {mpmath.nstr(worst, 3)})')
    # complex -> real on degree <= 6
    bk = Backend('ld')
    low = [t for t in terms if sum(t[:6]) <= 6]
    sp = SP(bk, np.zeros((len(low), 3)), np.array([t[:6] for t in low]), np.zeros(len(low)),
            bk.array_from([bk.real(t[6]) for t in low]))
    real = to_real(sp)
    rmap = {tuple(t[:6]): mpmath.mpf(t[6]) for t in rterms if sum(t[:6]) <= 6}
    scale = max(abs(v) for v in rmap.values())
    worst = max(abs(real.get(k, 0).real - v) for k, v in rmap.items()) / scale
    check(worst < 1e-17, f'real form = expansion of complex form, degree <= 6 (max diff/scale {mpmath.nstr(worst, 3)})')
    return C


def recompute(model, C, D):
    p = model['parameters']
    tr = model['truncations']
    full = (D == tr['degree_xi_eta'])
    bk = Backend('mp' if full else 'ld')      # the file is the mpmath build; ld suffices for degree <= 4
    astar = [mpmath.mpf(s) for s in p['astar_AU']]
    out = compute_secular(astar, bk, D=D, D1=tr['chi1_chi2_degree'], res=(D >= 16), nstar=tr['nstar'],
                          res_weight=tr['resonant_step']['weight_on_h_res_0'], log=lambda *a: None)
    tot = out['total']
    new = {tuple(int(x) for x in e): bk.to_mpc(c).real for e, c in zip(tot.E, tot.C)}
    Dcmp = D if D == model['truncations']['degree_xi_eta'] else D - 2   # degree D also needs f of degree D+1
    keys = [k for k in C if sum(k) <= Dcmp]
    scale = max(abs(C[k]) for k in keys)
    worst = 0
    for k in keys:
        if not full and abs(C[k]) < scale * mpmath.mpf('1e-12'):
            continue
        worst = max(worst, abs(new.get(k, 0) - C[k]) / abs(C[k]))
    missing = [k for k in new if 0 < sum(k) <= Dcmp and k not in C and abs(new[k]) > scale * mpmath.mpf('1e-30')]
    tol = 1e-23 if full else 1e-15      # full: 25 written digits; quick: long double vs mpmath
    check(worst < tol and not missing,
          f'recomputed degree <= {Dcmp}: max rel diff {mpmath.nstr(worst, 3)} over {len(keys)} terms, {len(missing)} missing')
    return out


def laplace_lagrange(out):
    c = out['consts']
    sec = out['first']
    d = {tuple(int(x) for x in e): out['first'].bk.to_mpc(cc).real for e, cc in zip(sec.E, sec.C)}
    worst = 0
    for (i, j) in ((0, 1), (0, 2), (1, 2)):
        alpha = c['a'][i] / c['a'][j]
        b1 = mpmath.quad(lambda x: mpmath.cos(x) / (1 + alpha**2 - 2*alpha*mpmath.cos(x))**1.5, [0, mpmath.pi]) * 2 / mpmath.pi
        b2 = mpmath.quad(lambda x: mpmath.cos(2*x) / (1 + alpha**2 - 2*alpha*mpmath.cos(x))**1.5, [0, mpmath.pi]) * 2 / mpmath.pi
        pref = -c['m'][i] * c['m'][j] / c['a'][j]
        e = [0] * 6; e[2 * i] = 1; e[2 * j + 1] = 1
        ref = -pref * alpha * b2 / 4 / mpmath.sqrt(c['Lambda'][i] * c['Lambda'][j])
        worst = max(worst, abs(d[tuple(e)] - ref) / abs(ref))
    check(worst < 1e-17, f'Laplace-Lagrange off-diagonal secular coefficients (max rel {mpmath.nstr(worst, 3)})')


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--full', action='store_true')
    ap.add_argument('--model', default=os.path.join(APP, 'data', 'sjsu18-o2.json'))
    args = ap.parse_args()
    mpmath.mp.dps = 40
    manifest()
    with open(args.model) as fh:
        model = json.load(fh)
    C = structure(model)
    out = recompute(model, C, 6 if not args.full else model['truncations']['degree_xi_eta'])
    laplace_lagrange(out)
    print('STATUS:', 'all checks passed' if not FAIL else f'{len(FAIL)} check(s) failed')
    return 0 if not FAIL else 1


if __name__ == '__main__':
    sys.exit(main())
