"""Sparse complex polynomials in (w1, w2, w3, wbar1, wbar2, wbar3), pure Python.

Monomial w^a wbar^b is packed into one int: key = sum_i e_i << (6 i), e = (a0, a1, a2, b0, b1, b2).
Exponents stay below 64 (total degree here is at most about 40).
Poisson structure of SJSU18-O2: {w_j, wbar_j} = -i, so
  {f, g} = -i sum_j (d_{w_j} f d_{wbar_j} g - d_{wbar_j} f d_{w_j} g).
"""
from __future__ import annotations

import math
import multiprocessing as mp
import os

SH = 6
MASK = 63
UNIT = [1 << (SH * i) for i in range(6)]
DROP = [UNIT[j] + UNIT[j + 3] for j in range(3)]


def key_of(e):
    k = 0
    for i, x in enumerate(e):
        k |= x << (SH * i)
    return k


def exps(k):
    return tuple((k >> (SH * i)) & MASK for i in range(6))


def degree(k):
    return sum(exps(k))


def charge(k):
    e = exps(k)
    return (e[0] - e[3], e[1] - e[4], e[2] - e[5])


def add(a, b, scale=1.0):
    out = dict(a)
    for k, c in b.items():
        out[k] = out.get(k, 0) + scale * c
    return out


def mul(a, b):
    out = {}
    for k, c in a.items():
        for l, d in b.items():
            m = k + l
            out[m] = out.get(m, 0) + c * d
    return out


def clean(p, tol=0.0):
    return {k: c for k, c in p.items() if abs(c) > tol}


def truncate(p, maxdeg):
    return {k: c for k, c in p.items() if degree(k) <= maxdeg}


def by_degree(p, d):
    return {k: c for k, c in p.items() if degree(k) == d}


def _prep(p):
    rows = []
    for k, c in p.items():
        e = exps(k)
        rows.append((k, c, e[0], e[1], e[2], e[3], e[4], e[5], sum(e)))
    return rows


def _bracket_rows(frows, grows, cap):
    out = {}
    get = out.get
    d0, d1, d2 = DROP
    for (kf, cf, a0, a1, a2, b0, b1, b2, df) in frows:
        for (kg, cg, c0, c1, c2, e0, e1, e2, dg) in grows:
            if df + dg - 2 > cap:
                continue
            base = kf + kg
            v = cf * cg
            f0 = a0 * e0 - b0 * c0
            if f0:
                m = base - d0
                out[m] = get(m, 0) + v * f0
            f1 = a1 * e1 - b1 * c1
            if f1:
                m = base - d1
                out[m] = get(m, 0) + v * f1
            f2 = a2 * e2 - b2 * c2
            if f2:
                m = base - d2
                out[m] = get(m, 0) + v * f2
    return out


_G = {}


def _worker(args):
    i, n, cap = args
    frows = _G['f'][i::n]
    return _bracket_rows(frows, _G['g'], cap)


NPROC = max(1, (os.cpu_count() or 2) - 2)


def bracket(f, g, cap=10**6, parallel=None):
    """{f, g} with {w_j, wbar_j} = -i; terms of degree > cap are skipped."""
    frows, grows = _prep(f), _prep(g)
    work = len(frows) * len(grows)
    if parallel is None:
        parallel = work > 2_000_000
    if not parallel:
        raw = _bracket_rows(frows, grows, cap)
    else:
        if len(frows) < len(grows):
            # split on the longer list for balance: {f,g} = -{g,f}
            raw = bracket(g, f, cap, parallel=True)
            return {k: -c for k, c in raw.items()}
        _G['f'], _G['g'] = frows, grows
        n = NPROC
        ctx = mp.get_context('fork')
        with ctx.Pool(n) as pool:
            parts = pool.map(_worker, [(i, n, cap) for i in range(n)])
        raw = {}
        for part in parts:
            for k, c in part.items():
                raw[k] = raw.get(k, 0) + c
        _G.clear()
    return {k: -1j * c for k, c in raw.items() if c != 0}


def lie(f, chi, cap, sign=1.0):
    """exp(sign L_chi) f = f + sign {f, chi} + 1/2 {{f,chi},chi} + ..., truncated at degree cap."""
    total = dict(f)
    term = dict(f)
    for n in range(1, 200):
        term = bracket(term, chi, cap)
        term = {k: c * sign / n for k, c in term.items() if degree(k) <= cap}
        if not term:
            return total
        total = add(total, term)
    raise RuntimeError('Lie series did not terminate')


def majorant(p, rho):
    """sum |c| prod rho_j^(a_j + b_j): a bound for sup |p| on the polydisk |w_j| <= rho_j."""
    terms = []
    for k, c in p.items():
        e = exps(k)
        terms.append(abs(c) * rho[0] ** (e[0] + e[3]) * rho[1] ** (e[1] + e[4])
                     * rho[2] ** (e[2] + e[5]))
    return math.fsum(terms)


def evaluate(p, w):
    v = list(w) + [x.conjugate() for x in w]
    s = 0
    for k, c in p.items():
        e = exps(k)
        t = c
        for i in range(6):
            if e[i]:
                t *= v[i] ** e[i]
        s += t
    return s
