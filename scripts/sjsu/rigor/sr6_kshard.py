#!/usr/bin/env python3
"""SR-6 KSHARD: generate standalone Lean files (core Nat only) for one real-size packed slot-pair product.

Operands (real data of run `sr-vp-L8`, V' coordinates):
  A = d/dphi_1 of the u_U-slot of F_U (support |k_i| <= 25; the bracket's first factor),
  B = sqrt(B0_U) (float witness of SR-4, support |k_i| <= 30; a power model of the H~ build),
each rounded to p fractional bits relative to its largest coefficient, Kronecker-packed with cell width w and
row stride S = 4 CP + 1 = 121 cells, signed coefficients split into two nonnegative digit arrays
(A = A+ - A-), so the product is 4 Nat.mul: C+ = A+ B+ + A- B-, C- = A+ B- + A- B+.
Literals are balanced trees of 288-bit chunks (lines <= 100 characters).  Variants:
  real   the chunks as they are;
  rand   every nonzero chunk's low 64 bits replaced by random bits (values change; C recomputed),
and three files per variant: data only (`decide` of a trivial fact over the data), product, product + mask
(the gutter bound: C+ >>> cut <= bound and (C+ &&& mask) <= bound).  No options are set.
Usage: python3 sr6_kshard.py --p 96 --out <dir>; then run each file with `lean` (see the GATES report).
"""
from __future__ import annotations

import argparse
import math
import random
import sys
from pathlib import Path

import numpy as np

sys.set_int_max_str_digits(0)

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
sys.path.insert(0, str(ROOT / 'scripts/sjsu/gate2'))
import ft  # noqa: E402

CP = 30
S = 4 * CP + 1
CH = 288


def hexn(k1, k2):
    return abs(k1) + abs(k2) + abs(k1 + k2)


def models():
    z = np.load(ROOT / 'scripts/sjsu/gate2/results/sr-vp-L8-F.npz')
    Sp = ft.Space(L=8, K=50)
    G = Sp.G
    F = z['F2']
    i = Sp.idx[(0, 0, 1)]
    A = {}
    for k2 in range(-25, 26):
        for k1 in range(-25, 26):
            if hexn(k1, k2) <= 50:
                a = 0.5 * (F[i, k1 % G, k2 % G].real + F[i, (-k1) % G, (-k2) % G].real)
                if k1:
                    A[(k1, k2)] = k1 * a  # d/dphi_1 of the cosine series: sine coefficients k1 a_k
    sh = z['s_hat']
    G2 = sh.shape[0]
    K1, K2 = np.meshgrid(np.rint(np.fft.fftfreq(G2, 1 / G2)), np.rint(np.fft.fftfreq(G2, 1 / G2)), indexing='ij')
    B0 = z['Istar'][2] + z['c0'][2] + (np.fft.ifft2(1j * (-K1 - K2) * sh) * G2 * G2).real
    c = np.fft.fft2(np.sqrt(B0)) / (G2 * G2)
    B = {}
    for k2 in range(-CP, CP + 1):
        for k1 in range(-CP, CP + 1):
            if hexn(k1, k2) <= 2 * CP:
                B[(k1, k2)] = 0.5 * (c[k1 % G2, k2 % G2].real + c[(-k1) % G2, (-k2) % G2].real)
    return A, B


def fixed(d, p):
    m = max(abs(v) for v in d.values())
    e = math.ceil(math.log2(m))
    return {k: int(round(v * 2.0 ** (p - e))) for k, v in d.items()}


def pack(d, w):
    pos, neg = 0, 0
    for (k1, k2), v in d.items():
        sh = w * ((k1 + CP) + S * (k2 + CP))
        if v > 0:
            pos |= v << sh
        elif v < 0:
            neg |= (-v) << sh
    return pos, neg


def chunks(n):
    out = []
    while n:
        out.append(n & ((1 << CH) - 1))
        n >>= CH
    return out or [0]


def tree(cs, lo, hi):
    """Lean term for sum_{i in [lo, hi)} cs[i] 2^{CH (i - lo)}: a balanced tree of explicit Nat.add /
    Nat.shiftLeft applications (no binop% notation, whose elaborator recurses over all leaves)."""
    if hi - lo == 1:
        return str(cs[lo])
    mid = (lo + hi) // 2
    return f'(Nat.add {tree(cs, lo, mid)} (Nat.shiftLeft {tree(cs, mid, hi)} {CH * (mid - lo)}))'


BLOCK = 256


def wrap(head, body, lines):
    out, cur = [], head
    for tok in body.replace('(', ' ( ').replace(')', ' ) ').split():
        if len(cur) + len(tok) + 1 > 100:
            out.append(cur)
            cur = '  ' + tok
        else:
            cur += ' ' + tok
    out.append(cur)
    lines.extend(out)
    lines.append('')


def lean_def(name, n, lines):
    """name := the value n, as sub-definitions of <= BLOCK chunks joined by a top-level tree."""
    cs = chunks(n)
    nb = (len(cs) + BLOCK - 1) // BLOCK
    subs = []
    for b in range(nb):
        part = cs[b * BLOCK:(b + 1) * BLOCK]
        sub = f'{name}_{b}'
        wrap(f'def {sub} : Nat :=', tree(part, 0, len(part)), lines)
        subs.append(sub)

    def jt(lo, hi):
        if hi - lo == 1:
            return subs[lo]
        mid = (lo + hi) // 2
        return f'(Nat.add {jt(lo, mid)} (Nat.shiftLeft {jt(mid, hi)} {CH * BLOCK * (mid - lo)}))'
    wrap(f'def {name} : Nat :=', jt(0, nb), lines)


def randomize(n, rng):
    cs = chunks(n)
    cs = [(c & ~((1 << 64) - 1)) | rng.getrandbits(64) if c else 0 for c in cs]
    return sum(c << (CH * i) for i, c in enumerate(cs))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--p', type=int, default=96)
    ap.add_argument('--out', required=True)
    args = ap.parse_args()
    out = Path(args.out)
    out.mkdir(parents=True, exist_ok=True)
    A, B = models()
    p = args.p
    nterms = min(len(A), len(B))
    w = 2 * p + math.ceil(math.log2(nterms)) + 2
    Af, Bf = fixed(A, p), fixed(B, p)
    Ap, An = pack(Af, w)
    Bp, Bn = pack(Bf, w)
    rng = random.Random(20261106)
    info = {'p': p, 'w': w, 'A_terms': len(A), 'B_terms': len(B)}
    for var in ('real', 'rand'):
        a_p, a_n, b_p, b_n = (Ap, An, Bp, Bn) if var == 'real' else tuple(randomize(x, rng) for x in (Ap, An, Bp, Bn))
        Cp = a_p * b_p + a_n * b_n
        Cn = a_p * b_n + a_n * b_p
        cut = w * (S * (3 * CP))  # rows k2 > CP of the product: outside the kept box (a gutter region)
        bound_hi = Cp >> cut
        mask = ((1 << (w * S * CP)) - 1) << (w * S * 2 * CP)  # a band of CP product rows
        bound_and = Cp & mask
        info[var] = {'operand_bits': [x.bit_length() for x in (a_p, a_n, b_p, b_n)], 'C_bits': [Cp.bit_length(), Cn.bit_length()],
                     'chunks': [len(chunks(x)) for x in (a_p, a_n, b_p, b_n, Cp, Cn)],
                     'low64_distinct_chunks': len({c & ((1 << 64) - 1) for x in (a_p, a_n, b_p, b_n, Cp, Cn) for c in chunks(x) if c})}
        data = ['/-! SR-6 KSHARD (generated by scripts/sjsu/rigor/sr6_kshard.py; throwaway, core only). -/', '']
        for nm, val in (('Ap', a_p), ('An', a_n), ('Bp', b_p), ('Bn', b_n), ('Cp', Cp), ('Cn', Cn)):
            lean_def(nm, val, data)
        extra = []
        lean_def('bandBound', bound_and, extra)
        lean_def('hiBound', bound_hi, extra)
        prod = ['theorem prodP : Ap * Bp + An * Bn = Cp := by decide +kernel', '',
                'theorem prodN : Ap * Bn + An * Bp = Cn := by decide +kernel', '']
        files = {
            'data': data + ['theorem sizes : Ap + An + Bp + Bn + Cp + Cn ≠ 0 := by decide +kernel', ''],
            'prod': data + prod,
            'mask': data + extra + prod + [
                f'theorem hi : Cp >>> {cut} ≤ hiBound := by decide +kernel', '',
                f'theorem band : Cp &&& ((2 ^ {w * S * CP} - 1) <<< {w * S * 2 * CP}) ≤ bandBound := by decide +kernel', ''],
        }
        for kind, lines in files.items():
            (out / f'Ksh_{var}_{kind}.lean').write_text('\n'.join(lines) + '\n')
    import json
    (out / 'info.json').write_text(json.dumps(info, indent=1) + '\n')
    print(json.dumps(info, indent=1))


if __name__ == '__main__':
    main()
