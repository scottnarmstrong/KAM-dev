#!/usr/bin/env python3
"""Exact modal Hamiltonian H_w = H_z o (z = V' w) of SJSU18-O2 by symmetric-power matrices (T2-CONF, N5a).

H_z = sum_{a, a'} c_{a a'} z^a zbar^{a'} (complex form, D75; |a| = |a'| = d by charge balance, d = 1..9).
With z = V' w, zbar = V' wbar (V' = M / N real, exact; scripts/sjsu/rigor/results/vprime.json):
  z^a = sum_{|b| = d} S_d[a, b] w^b,   S_d[a, .] built by peeling one factor z_j = sum_k V'_jk w_k,
  H_w,d = sum_{b, b'} (S_d^T C_d S_d)[b, b'] w^b wbar^{b'}.
Integer form: S_d = Sint_d / N^d (Sint_d from M), c = cint / 10^E, so C'_d = Sint_d^T Cint_d Sint_d / (N^{2d} 10^E).
Outputs results/hw.json: per degree d, the integer matrix data needed by the kernel check, and H_w as exact
rationals; cross-checks against flint's fmpq_mpoly composition when python-flint is available.
Usage: python3 gen_hw.py [--check-flint]
"""
from __future__ import annotations

import argparse
import json
from fractions import Fraction
from itertools import product
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]


def multis(d):
    return [(a, b, d - a - b) for a in range(d, -1, -1) for b in range(d - a, -1, -1)]


def sym_powers(M, dmax):
    """Sint[d][a] = dict b -> int: prod_j (sum_k M_jk w_k)^{a_j} = sum_b Sint[d][a][b] w^b (integer M)."""
    S = {0: {(0, 0, 0): {(0, 0, 0): 1}}}
    for d in range(1, dmax + 1):
        S[d] = {}
        for a in multis(d):
            j = next(i for i in range(3) if a[i] > 0)
            prev = S[d - 1][tuple(a[i] - (i == j) for i in range(3))]
            row = {}
            for b, v in prev.items():
                for k in range(3):
                    if M[j][k]:
                        bb = tuple(b[i] + (i == k) for i in range(3))
                        row[bb] = row.get(bb, 0) + v * M[j][k]
            S[d][a] = row
    return S


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--check-flint', action='store_true')
    args = ap.parse_args()
    data = json.loads((ROOT / 'applications/sjsu/data/sjsu18-o2.json').read_text())
    vp = json.loads((HERE / 'results/vprime.json').read_text())
    V = [[Fraction(x) for x in row] for row in vp['Vprime_exact']]
    N = V[0][0].denominator
    assert all(x.denominator in (1, N) or N % x.denominator == 0 for row in V for x in row)
    M = [[int(x * N) for x in row] for row in V]
    E = 0  # every coefficient is cint / 10^E with integer cint
    for t in data['complex_form']['terms']:
        while (Fraction(t[6]) * 10 ** E).denominator != 1:
            E += 1
    C = {}
    for t in data['complex_form']['terms']:
        a = (t[0], t[2], t[4])
        ab = (t[1], t[3], t[5])
        c = Fraction(t[6]) * 10 ** E
        assert c.denominator == 1
        C.setdefault(sum(a), {})[(a, ab)] = int(c)
    S = sym_powers(M, 9)
    Hw = {}
    out_deg = {}
    for d, Cd in sorted(C.items()):
        # C'_d[b, b'] = sum_{a, a'} Sint[a][b] Cint[a, a'] Sint[a'][b']
        tmp = {}
        for (a, ab), c in Cd.items():
            for bp, v in S[d][ab].items():
                key = (a, bp)
                tmp[key] = tmp.get(key, 0) + c * v
        Cp = {}
        for (a, bp), v in tmp.items():
            for b, u in S[d][a].items():
                key = (b, bp)
                Cp[key] = Cp.get(key, 0) + u * v
        den = N ** (2 * d) * 10 ** E
        nz = {k: v for k, v in Cp.items() if v}
        charged = [k for k in nz if sum(k[0]) != sum(k[1])]
        assert not charged
        bad = [k for k in nz if any(k[0][i] - k[1][i] for i in range(3)) and False]
        for (b, bp), v in nz.items():
            # store as (w exponents, wbar exponents) in planet order 0, 1, 2
            Hw[(b, bp)] = Fraction(v, den)
        out_deg[d] = {'terms': len(nz), 'max_bits': max(abs(v).bit_length() for v in nz.values()), 'den_bits': den.bit_length()}
    # charge balance in the modal form: sum_j (b_j - b'_j) = 0 for every term
    assert all(sum(b) == sum(bp) for (b, bp) in Hw)
    rep = {'doc': 'H_w = H_z o (z = V\' w) exactly; keys "b0,b1,b2|b0\',b1\',b2\'" (w and wbar exponents per mode).',
           'N': str(N), 'E': E, 'degrees': out_deg, 'terms': len(Hw),
           'Hw': {f"{','.join(map(str, b))}|{','.join(map(str, bp))}": f'{v.numerator}/{v.denominator}'
                  for (b, bp), v in sorted(Hw.items())}}
    if args.check_flint:
        from flint import fmpq, fmpq_mpoly_ctx
        cz = fmpq_mpoly_ctx.get(('z', 6), 'lex')
        cw = fmpq_mpoly_ctx.get(('w', 6), 'lex')
        Hz = cz.from_dict({tuple(t[:6]): fmpq(Fraction(t[6]).numerator, Fraction(t[6]).denominator)
                           for t in data['complex_form']['terms']})
        w = cw.gens()
        q = lambda x: fmpq(x.numerator, x.denominator)  # noqa: E731
        zero = cw.from_dict({})
        subs = []
        for j in range(3):
            subs.append(sum((q(V[j][k]) * w[2 * k] for k in range(3)), zero))
            subs.append(sum((q(V[j][k]) * w[2 * k + 1] for k in range(3)), zero))
        Hf = Hz.compose(*subs)
        ref = {}
        for m, c in zip(Hf.monoms(), Hf.coeffs()):
            m = [int(x) for x in m]
            ref[((m[0], m[2], m[4]), (m[1], m[3], m[5]))] = Fraction(int(c.numerator), int(c.denominator))
        rep['flint_crosscheck'] = (ref == Hw)
        assert ref == Hw, 'symmetric-power composition differs from flint compose'
    (HERE / 'results/hw.json').write_text(json.dumps(rep) + '\n')
    print({k: v for k, v in rep.items() if k != 'Hw'})


if __name__ == '__main__':
    main()
