#!/usr/bin/env python3
"""SR-1 EXACT-MODEL: exact identities of SJSU18-O2 in rational arithmetic (standard library only).

The model of record is the real form (xi, eta) of applications/sjsu/data/sjsu18-o2.json, each
25-digit decimal read as an exact rational (docs/explorations/sjs-rigor-plan.md 1.1). Checks:

  1. census: 38,466 real terms, even degrees 2..18, no duplicate exponents;
  2. reversibility: every real term has even total eta-degree (H(xi, -eta) = H(xi, eta));
  3. exact complex form: substitute xi = (z + zbar)/sqrt2, eta = i (z - zbar)/sqrt2 (z = (xi - i eta)/sqrt2)
     in Q(i); every monomial z^a zbar^b with charge a - b != 0 must have coefficient exactly 0
     (rotation invariance: functions depend on the angles only through q_j - q_3), every coefficient
     must be real (reversibility) and c_{a,b} = c_{b,a} (reality);
  4. {C, H} = 0 exactly in the real form, C = sum_j (xi_j^2 + eta_j^2)/2 (the AMD), with {eta_j, xi_j} = 1;
  5. the nominal point z* (validation/table2_map_poincare_order1.json, xi_eta_secular) parsed from its
     decimal text exactly; H(z*) and C(z*) computed exactly and printed to 30 digits;
  6. comparison of the exact complex form of the real form with the published complex form
     (independently rounded to 25 digits: agreement to rounding, not identity, is expected).

Variant C (the published complex form, 7,941 terms, each 25-digit decimal an exact rational):
  C1. every term has charge sum(a - b) = 0;  C2. every coefficient real and c_{a,b} = c_{b,a} exactly;
  C3. {C, H} = 0 exactly ({z_j, zbar_j} = -i, C = sum z_j zbar_j);  C4. H(z*) exactly in Q (degree even).

PASS iff items 1-5 hold with zero defect (real form), resp. C1-C4 (complex form).
Usage: python3 sr1_exact_model.py
"""
from __future__ import annotations

import json
import re
import sys
import time
from collections import defaultdict
from fractions import Fraction
from math import comb
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
DATA = ROOT / 'applications/sjsu/data/sjsu18-o2.json'
NOMINAL = ROOT / 'applications/sjsu/validation/table2_map_poincare_order1.json'
OUT = Path(__file__).resolve().parent / 'results'


def frac(s: str) -> Fraction:
    return Fraction(s)  # exact decimal (Fraction parses '1.23e-5' exactly)


def raw_decimals(path: Path, key: str) -> list[str]:
    """The decimal text of a JSON float array, as written in the file (no binary rounding)."""
    txt = path.read_text()
    m = re.search(r'"%s"\s*:\s*\[([^\]]*)\]' % re.escape(key), txt)
    return [x.strip() for x in m.group(1).split(',')]


def main():
    t0 = time.time()
    data = json.loads(DATA.read_text())
    report = {'gate': 'SR-1 EXACT-MODEL', 'data': str(DATA.relative_to(ROOT))}
    real = data['real_form']['terms']
    assert data['real_form']['monomial_order'] == ['xi_J', 'xi_S', 'xi_U', 'eta_J', 'eta_S', 'eta_U']
    H = {}
    dup = 0
    for t in real:
        e = tuple(t[:6])
        if e in H:
            dup += 1
        H[e] = frac(t[6])
    degs = defaultdict(int)
    for e in H:
        degs[sum(e)] += 1
    census_ok = (len(real) == 38466 and dup == 0 and all(d % 2 == 0 and 2 <= d <= 18 for d in degs)
                 and all(c != 0 for c in H.values()))
    report['census'] = {'terms': len(real), 'duplicates': dup, 'by_degree': dict(sorted(degs.items())),
                        'nonzero_coefficients': all(c != 0 for c in H.values()), 'pass': census_ok}
    # 2. reversibility
    odd_eta = sum(1 for e in H if (e[3] + e[4] + e[5]) % 2)
    report['reversibility'] = {'terms_odd_in_eta': odd_eta, 'pass': odd_eta == 0}
    # 3. exact complex form. xi_j^P eta_j^Q = 2^{-(P+Q)/2} (z+zb)^P (i(z-zb))^Q; per planet a dict
    # (a, b) -> Gaussian integer (re, im) of (z+zb)^P (i (z - zb))^Q, cached.
    cache = {}

    def planet(P, Q):
        key = (P, Q)
        if key in cache:
            return cache[key]
        out = defaultdict(lambda: [0, 0])
        iq = [(1, 0), (0, 1), (-1, 0), (0, -1)][Q % 4]  # i^Q
        for s in range(P + 1):          # (z + zb)^P: C(P, s) z^s zb^(P-s)
            for r in range(Q + 1):      # (z - zb)^Q: C(Q, r) z^r (-zb)^(Q-r)
                c = comb(P, s) * comb(Q, r) * (-1) ** (Q - r)
                k = (s + r, P - s + Q - r)
                out[k][0] += c * iq[0]
                out[k][1] += c * iq[1]
        cache[key] = {k: tuple(v) for k, v in out.items() if v != [0, 0]}
        return cache[key]

    Z = defaultdict(lambda: [Fraction(0), Fraction(0)])
    for e, c in H.items():
        d = sum(e)
        scale = c / (2 ** (d // 2))
        A = planet(e[0], e[3])
        B = planet(e[1], e[4])
        C = planet(e[2], e[5])
        for ka, va in A.items():
            for kb, vb in B.items():
                re1 = va[0] * vb[0] - va[1] * vb[1]
                im1 = va[0] * vb[1] + va[1] * vb[0]
                for kc, vc in C.items():
                    re2 = re1 * vc[0] - im1 * vc[1]
                    im2 = re1 * vc[1] + im1 * vc[0]
                    key = (ka[0], ka[1], kb[0], kb[1], kc[0], kc[1])  # zJ zbJ zS zbS zU zbU
                    z = Z[key]
                    if re2:
                        z[0] += scale * re2
                    if im2:
                        z[1] += scale * im2
    Zc = {k: v for k, v in Z.items() if v[0] != 0 or v[1] != 0}
    charged = [k for k in Zc if (k[0] - k[1]) + (k[2] - k[3]) + (k[4] - k[5]) != 0]
    imag = [k for k in Zc if Zc[k][1] != 0]
    asym = [k for k in Zc if Zc.get((k[1], k[0], k[3], k[2], k[5], k[4]), [0, 0])[0] != Zc[k][0]]
    report['complex_form_exact'] = {
        'nonzero_monomials': len(Zc), 'charged_nonzero': len(charged), 'nonreal': len(imag),
        'asymmetric_c_ab_vs_c_ba': len(asym),
        'pass': not charged and not imag and not asym}
    # 6. comparison with the published complex form
    pub = {}
    assert data['complex_form']['monomial_order'] == ['z_J', 'zbar_J', 'z_S', 'zbar_S', 'z_U', 'zbar_U']
    for t in data['complex_form']['terms']:
        pub[tuple(t[:6])] = frac(t[6])
    keys = set(pub) | set(Zc)
    worst_rel, worst_key = Fraction(0), None
    for k in keys:
        a = pub.get(k, Fraction(0))
        b = Zc.get(k, [Fraction(0)])[0]
        if a == b:
            continue
        rel = abs(a - b) / max(abs(a), abs(b))
        if rel > worst_rel:
            worst_rel, worst_key = rel, k
    report['vs_published_complex_form'] = {
        'published_terms': len(pub), 'exact_terms': len(Zc), 'same_support': set(pub) == set(Zc),
        'identical_coefficients': sum(1 for k in pub if k in Zc and Zc[k][0] == pub[k]),
        'max_relative_difference': float(worst_rel), 'at': worst_key,
        'note': 'independently rounded to 25 digits; agreement to rounding expected, identity not'}
    # 4. {C, H} in the real form: {f, g} = sum_j (d_eta f d_xi g - d_xi f d_eta g), C = sum (xi^2+eta^2)/2
    # => {C, H} = sum_j (eta_j d_xi_j H - xi_j d_eta_j H)
    br = defaultdict(Fraction)
    for e, c in H.items():
        for j in range(3):
            if e[j]:  # eta_j * d_xi_j
                k = list(e)
                k[j] -= 1
                k[j + 3] += 1
                br[tuple(k)] += c * e[j]
            if e[j + 3]:  # - xi_j * d_eta_j
                k = list(e)
                k[j + 3] -= 1
                k[j] += 1
                br[tuple(k)] -= c * e[j + 3]
    nz = {k: v for k, v in br.items() if v != 0}
    report['amd_bracket'] = {'bracket_monomials_checked': len(br), 'nonzero': len(nz), 'pass': not nz}
    # 5. nominal point, exact
    txt = raw_decimals(NOMINAL, 'xi_eta_secular')
    zs = [frac(s) for s in txt]
    xs = zs[:3]
    es = zs[3:]
    Hval = Fraction(0)
    pw = [[Fraction(1)] for _ in range(6)]
    for j in range(6):
        v = zs[j]
        for _ in range(18):
            pw[j].append(pw[j][-1] * v)
    for e, c in H.items():
        t = c
        for j in range(6):
            if e[j]:
                t *= pw[j][e[j]]
        Hval += t
    Cval = sum(x * x + y * y for x, y in zip(xs, es)) / 2

    def dec(x, n=30):
        from decimal import Decimal, getcontext
        getcontext().prec = n
        return str(Decimal(x.numerator) / Decimal(x.denominator))
    report['nominal'] = {'source': str(NOMINAL.relative_to(ROOT)) + ':xi_eta_secular', 'decimals': txt,
                         'order': 'xi_J, xi_S, xi_U, eta_J, eta_S, eta_U',
                         'H_exact_30': dec(Hval), 'C_exact_30': dec(Cval),
                         'H_denominator_bits': Hval.denominator.bit_length(), 'pass': len(zs) == 6}
    # magnitude of the defect of the real form (charged part of its exact complex form)
    rad = [abs(complex(float(xs[j]), -float(es[j]))) / 2 ** 0.5 for j in range(3)]

    def wt(k):
        return rad[0] ** (k[0] + k[1]) * rad[1] ** (k[2] + k[3]) * rad[2] ** (k[4] + k[5])
    by = defaultdict(lambda: [0.0, 0.0])
    for k in charged:
        by[sum(k)][0] = max(by[sum(k)][0], abs(float(Zc[k][0])))
    for k, v in pub.items():
        by[sum(k)][1] = max(by[sum(k)][1], abs(float(v)))
    report['real_form_defect'] = {
        'max_abs_charged_coefficient_by_degree': {d: '%.2e' % v[0] for d, v in sorted(by.items())},
        'max_abs_published_coefficient_by_degree': {d: '%.2e' % v[1] for d, v in sorted(by.items())},
        'charged_majorant_at_nominal_radii': '%.3e' % sum(abs(float(Zc[k][0])) * wt(k) for k in charged),
        'H_majorant_at_nominal_radii': '%.3e' % sum(abs(float(v)) * wt(k) for k, v in pub.items()),
        'nominal_radii': rad}
    real_ok = all(report[k]['pass'] for k in ('census', 'reversibility', 'complex_form_exact', 'amd_bracket',
                                              'nominal'))
    # ---- variant C: the published complex form as the model
    ch = [k for k in pub if (k[0] - k[1]) + (k[2] - k[3]) + (k[4] - k[5]) != 0]
    sw = [k for k in pub if pub.get((k[1], k[0], k[3], k[2], k[5], k[4])) != pub[k]]
    # {C, z^a zb^b} = i (sum_j (a_j - b_j)) z^a zb^b  (from {z_j, zb_j} = -i)
    brc = {k: v * ((k[0] - k[1]) + (k[2] - k[3]) + (k[4] - k[5])) for k, v in pub.items()}
    brc_nz = sum(1 for v in brc.values() if v != 0)
    # H(z*) from the complex form: z_j = (xi_j - i eta_j)/sqrt2; z^a zb^b = 2^{-d/2} (xi-i eta)^a (xi+i eta)^b
    gp = []
    for j in range(3):
        zpw, zbpw = [(Fraction(1), Fraction(0))], [(Fraction(1), Fraction(0))]
        for _ in range(18):
            a, b = zpw[-1]
            zpw.append((a * xs[j] + b * es[j], b * xs[j] - a * es[j]))      # * (xi - i eta)
            a, b = zbpw[-1]
            zbpw.append((a * xs[j] - b * es[j], b * xs[j] + a * es[j]))     # * (xi + i eta)
        gp.append((zpw, zbpw))
    Hc_re, Hc_im = Fraction(0), Fraction(0)
    for k, c in pub.items():
        re_, im_ = c / 2 ** (sum(k) // 2), Fraction(0)
        for j in range(3):
            for (u, v) in (gp[j][0][k[2 * j]], gp[j][1][k[2 * j + 1]]):
                re_, im_ = re_ * u - im_ * v, re_ * v + im_ * u
        Hc_re += re_
        Hc_im += im_
    report['complex_form_model'] = {
        'terms': len(pub), 'charged': len(ch), 'c_ab_ne_c_ba': len(sw), 'amd_bracket_nonzero': brc_nz,
        'H_exact_30': dec(Hc_re), 'H_imag_exact_zero': Hc_im == 0,
        'H_complex_minus_H_real_at_nominal': '%.3e' % float(Hc_re - Hval),
        'pass': not ch and not sw and brc_nz == 0 and Hc_im == 0}
    report['verdict_real_form'] = 'PASS' if real_ok else 'FAIL'
    report['verdict_complex_form'] = 'PASS' if report['complex_form_model']['pass'] else 'FAIL'
    ok = real_ok or report['complex_form_model']['pass']
    report['verdict'] = ('PASS' if real_ok else
                         'PASS for the complex form only' if ok else 'FAIL')
    report['seconds'] = round(time.time() - t0, 1)
    OUT.mkdir(exist_ok=True)
    (OUT / 'sr1.json').write_text(json.dumps(report, indent=1, default=str) + '\n')
    for k, v in report.items():
        print(k, ':', v)
    return 0 if ok else 1


if __name__ == '__main__':
    sys.exit(main())
