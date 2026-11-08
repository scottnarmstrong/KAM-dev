"""The literal observables F_j of T2-CONF (N7/N8): F-v1.json even parts, pruned and rounded.

f_j(u, phi) = sum_s u^s q_s sum_e m_e cos(k_e . phi): for each u-monomial s, the modes k with
|a_{s,k}| (2e-6)^|s| >= THR are kept (THR = 1e-21, kam-g2 ruling) in the box |k_i| <= CF = 25, and
rounded to P bits relative to the largest kept |a_{s,k}| (scale q_s = 2^-e_s).  The rounded, pruned
literal IS the observable.  Box coordinates (c, r) = (k1 + CF, k2 + CF).
"""
from __future__ import annotations

import json
from fractions import Fraction as Fr
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
THR = Fr(1, 10 ** 21)
R0 = Fr(2, 10 ** 6)
CF = 25
P = 80


def scale_round(co, p):
    mx = max(abs(v) for v in co.values())
    e = p - 1 - (mx.numerator.bit_length() - mx.denominator.bit_length())
    while mx * Fr(2) ** e >= 2 ** p:
        e -= 1
    while mx * Fr(2) ** (e + 1) < 2 ** p:
        e += 1
    out = {}
    for k, v in co.items():
        x = v * Fr(2) ** e
        m = int(x + Fr(1, 2)) if x >= 0 else -int(-x + Fr(1, 2))
        if m:
            out[k] = m
    return out, (Fr(1, 2 ** e) if e >= 0 else Fr(2 ** -e))


def load(small=False):
    """[(j, {s: (q_s, {(c, r): m})})] for j = 0, 1, 2"""
    cf = 8 if small else CF
    raw = json.loads((ROOT / '.drafts/g2/data/F-v1.json').read_text())
    out = []
    for j in range(3):
        Fj = {}
        for ms, d in sorted(raw[str(j)].items()):
            s = tuple(int(x) for x in ms.split(','))
            co = {}
            for ks, v in d.items():
                k = tuple(int(x) for x in ks.split(','))
                v = Fr(v)
                if abs(v) * R0 ** sum(s) < THR or max(abs(k[0]), abs(k[1])) > cf:
                    continue
                co[(k[0] + cf, k[1] + cf)] = v
            if co:
                mant, q = scale_round(co, P)
                if mant:
                    Fj[s] = (q, mant)
        out.append(Fj)
    return out, cf
