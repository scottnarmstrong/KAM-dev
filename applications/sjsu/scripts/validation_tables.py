#!/usr/bin/env python3
"""Validation tables against SLG13 Appendix A (78 printed coefficients).

Writes validation/appendixA_comparison.csv with, for each printed monomial:
  printed value; its rotation-invariant projection and non-invariant remainder (the printed
  quartic is converted to z = (xi - i eta)/sqrt 2 exactly, monomials with unequal z and zbar
  degree are the non-invariant part); the SJSU18-O2 value (data file) with its first-order,
  chi_1 and chi_2 components; relative deviations; number of planets involved.
Also writes validation/appendixA_noninvariant.csv (the non-invariant complex monomials of the
printed table) and prints summary statistics.
Usage: python3 -I applications/sjsu/scripts/validation_tables.py
"""
import csv
import json
import os
import sys
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
APP = os.path.abspath(os.path.join(HERE, '..'))

import mpmath
import sympy as sp

from compare_appendix_a import load_table


def printed_complex(table):
    xi = sp.symbols('x1:4'); eta = sp.symbols('y1:4'); z = sp.symbols('z1:4'); w = sp.symbols('w1:4')
    H = 0
    for powers, cs in table:
        fr = Fraction(cs)
        m = sp.Rational(fr.numerator, fr.denominator)
        for j in range(3):
            m *= xi[j] ** powers[j] * eta[j] ** powers[3 + j]
        H += m
    sub = {}
    for j in range(3):
        sub[xi[j]] = (z[j] + w[j]) / sp.sqrt(2)
        sub[eta[j]] = sp.I * (z[j] - w[j]) / sp.sqrt(2)
    P = sp.Poly(sp.expand(H.subs(sub)), *z, *w)
    inv, non = 0, 0
    noninv = []
    for mon, c in P.terms():
        charge = sum(mon[:3]) - sum(mon[3:])
        term = c
        for j in range(3):
            term *= z[j] ** mon[j] * w[j] ** mon[3 + j]
        if charge == 0:
            inv += term
        else:
            non += term
            noninv.append((mon, charge, c))
    back = {}
    for name, part in (('inv', inv), ('non', non)):
        sub2 = {}
        for j in range(3):
            sub2[z[j]] = (xi[j] - sp.I * eta[j]) / sp.sqrt(2)
            sub2[w[j]] = (xi[j] + sp.I * eta[j]) / sp.sqrt(2)
        Q = sp.Poly(sp.expand(sp.sympify(part).subs(sub2)), *xi, *eta)
        back[name] = {tuple(m): c for m, c in Q.terms()}
    return back, noninv


def main():
    mpmath.mp.dps = 40
    table = load_table()
    back, noninv = printed_complex(table)
    model = json.load(open(os.path.join(APP, 'data', 'sjsu18-o2.json')))
    real = {tuple(t[:6]): mpmath.mpf(t[6]) for t in model['real_form']['terms']}
    # components in real form, degree <= 4
    from secular import to_real
    from sjsu_common import Backend
    from sparse import SP
    import numpy as np
    bk = Backend('mp')
    comp_real = {}
    for name, terms in model['components_complex_form'].items():
        low = [t for t in terms if sum(t[:6]) <= 4]
        spc = SP(bk, np.zeros((len(low), 3)), np.array([t[:6] for t in low]), np.zeros(len(low)),
                 bk.array_from([mpmath.mpc(mpmath.mpf(t[6]), 0) for t in low]))
        comp_real[name] = {k: v.real for k, v in to_real(spc).items()}
    out = os.path.join(APP, 'validation', 'appendixA_comparison.csv')
    stats = {}
    with open(out, 'w', newline='') as fh:
        w = csv.writer(fh)
        w.writerow(['powers_xiJ_xiS_xiU_etaJ_etaS_etaU', 'planets', 'slg13_printed', 'printed_invariant_projection',
                    'printed_noninvariant_part', 'sjsu18_o2', 'rel_dev_vs_printed', 'rel_dev_vs_invariant_projection',
                    'o2_first_order', 'o2_second_order_chi1', 'o2_second_order_chi2'])
        for powers, cs in table:
            ref = mpmath.mpf(cs)
            inv = back['inv'].get(powers, 0)
            non = back['non'].get(powers, 0)
            inv_f = mpmath.mpf(sp.N(inv, 30)) if inv != 0 else mpmath.mpf(0)
            non_f = mpmath.mpf(sp.N(sp.re(non), 30)) if non != 0 else mpmath.mpf(0)
            v = real.get(powers, mpmath.mpf(0))
            npl = sum(1 for j in range(3) if powers[j] + powers[3 + j])
            rd = (v - ref) / abs(ref)
            ri = (v - inv_f) / abs(inv_f) if inv_f != 0 else mpmath.mpf('nan')
            key = ('quadratic' if sum(powers) == 2 else f'quartic_{npl}planet')
            stats.setdefault(key, []).append(abs(float(rd)))
            w.writerow([' '.join(map(str, powers)), npl, cs, mpmath.nstr(inv_f, 17), mpmath.nstr(non_f, 6),
                        mpmath.nstr(v, 17), mpmath.nstr(rd, 4), mpmath.nstr(ri, 4),
                        mpmath.nstr(comp_real['first_order'].get(powers, 0), 12),
                        mpmath.nstr(comp_real['second_order_chi1'].get(powers, 0), 12),
                        mpmath.nstr(comp_real['second_order_chi2'].get(powers, 0), 12)])
    with open(os.path.join(APP, 'validation', 'appendixA_noninvariant.csv'), 'w', newline='') as fh:
        w = csv.writer(fh)
        w.writerow(['z_J', 'zbar_J', 'z_S', 'zbar_S', 'z_U', 'zbar_U', 'charge', 'coefficient'])
        for mon, charge, c in sorted(noninv, key=lambda t: -abs(complex(t[2]))):
            w.writerow([mon[0], mon[3], mon[1], mon[4], mon[2], mon[5], charge, sp.N(sp.re(c), 8)])
    for k, v in sorted(stats.items()):
        print(f'{k:18s} n={len(v):2d}  median |rel dev| {sorted(v)[len(v)//2]:.2e}  max {max(v):.2e}')
    big = [(m, ch, complex(c)) for m, ch, c in noninv if abs(complex(c)) > 1e-12]
    print(f'non-invariant complex monomials in the printed table: {len(noninv)} (|c| > 1e-12: {len(big)}); '
          f'largest |c| = {max(abs(t[2]) for t in big):.3e}; charges present: {sorted(set(t[1] for t in big))}')


if __name__ == '__main__':
    main()
