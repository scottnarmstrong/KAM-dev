"""Truncated multivariate Taylor jets on grids (research scratch, float64).

A jet of degree <= D in `nvar` variables is an array of shape (M, *grid) whose first axis runs over monomials
ordered by total degree (so truncation to degree d is the prefix of length nmon[d]).  Products skip structurally
zero rows of either factor, so jets that depend on few variables stay cheap.
"""
from __future__ import annotations

import math
from math import comb

import os

import numpy as np

DTYPE = np.longdouble if os.environ.get('SJSU_DTYPE') == 'longdouble' else np.float64


def _mons(nvar, d):
    if nvar == 1:
        yield (d,)
        return
    for a in range(d, -1, -1):
        for rest in _mons(nvar - 1, d - a):
            yield (a,) + rest


class Basis:
    def __init__(self, nvar: int, D: int):
        self.nvar, self.D = nvar, D
        mons = []
        for d in range(D + 1):
            mons += list(_mons(nvar, d))
        self.mons = mons
        self.idx = {m: i for i, m in enumerate(mons)}
        self.deg = np.array([sum(m) for m in mons])
        self.nmon = [comb(nvar + d, d) for d in range(D + 1)]
        self.ks = []
        for i, mi in enumerate(mons):
            L = self.nmon[D - self.deg[i]]
            self.ks.append(np.array([self.idx[tuple(a + b for a, b in zip(mi, mons[j]))] for j in range(L)],
                                    dtype=np.int64))
        self.dsrc, self.ddst, self.dfac = [], [], []
        for v in range(nvar):
            src, dst, fac = [], [], []
            for g, m in enumerate(mons):
                if self.deg[g] < D:
                    mp = list(m); mp[v] += 1
                    src.append(self.idx[tuple(mp)]); dst.append(g); fac.append(mp[v])
            self.dsrc.append(np.array(src)); self.ddst.append(np.array(dst)); self.dfac.append(np.array(fac, float))
        self.unit = [self.idx[tuple(1 if w == v else 0 for w in range(nvar))] for v in range(nvar)]

    # ------------------------------------------------------------------ construction
    def const(self, c, d=None):
        c = np.asarray(c, dtype=DTYPE)
        out = np.zeros((self.nmon[self.D if d is None else d],) + c.shape, dtype=DTYPE)
        out[0] = c
        return out

    def affine(self, c, v, d=None):
        out = self.const(c, d)
        out[self.unit[v]] = 1.0
        return out

    # ------------------------------------------------------------------ algebra
    def trunc(self, a, d):
        return a[: self.nmon[d]]

    def deriv(self, a, v):
        """d/dx_v; result has degree one less (rows nmon[deg(a) - 1])."""
        M = a.shape[0]
        da = int(np.searchsorted(self.nmon, M))          # degree of a
        Mo = self.nmon[da - 1] if da >= 1 else 1
        out = np.zeros((Mo,) + a.shape[1:], dtype=a.dtype)
        if da == 0:
            return out
        sel = self.dsrc[v] < M
        src, dst, fac = self.dsrc[v][sel], self.ddst[v][sel], self.dfac[v][sel]
        sel2 = dst < Mo
        src, dst, fac = src[sel2], dst[sel2], fac[sel2]
        out[dst] = a[src] * fac.reshape((-1,) + (1,) * (a.ndim - 1))
        return out

    @staticmethod
    def support(a):
        return np.flatnonzero(np.any(a.reshape(a.shape[0], -1) != 0, axis=1))

    def mul(self, a, b, dout, chunk_bytes=1 << 28):
        Ma, Mb = a.shape[0], b.shape[0]
        Mo = self.nmon[dout]
        shp = np.broadcast_shapes(a.shape[1:], b.shape[1:])
        out = np.zeros((Mo,) + shp, dtype=np.result_type(a, b))
        nza = self.support(a)
        mb = np.zeros(Mb, bool); mb[self.support(b)] = True
        per = max(1, int(np.prod(shp))) * out.itemsize
        CH = max(1, chunk_bytes // per)
        for i in nza:
            di = self.deg[i]
            if di > dout:
                break
            L = min(self.nmon[dout - di], Mb)
            js = np.flatnonzero(mb[:L])
            if not len(js):
                continue
            ks = self.ks[i][js]
            ai = a[i]
            for c in range(0, len(js), CH):
                out[ks[c:c + CH]] += ai * b[js[c:c + CH]]
        return out

    def compose(self, a, coeffs, d):
        """sum_m coeffs[m] (a - a0)^m, coeffs[m] grid arrays (Taylor coefficients of g at a0)."""
        delta = self.trunc(a, d).copy()
        delta[0] = 0
        S = self.const(coeffs[d], 0)
        for m in range(d - 1, -1, -1):
            S = self.mul(delta, S, d)
            S[0] = S[0] + coeffs[m]
        return S

    def recip(self, a, d=None):
        d = self.D if d is None else d
        a0 = a[0]
        return self.compose(a, [(-1) ** m * a0 ** (-m - 1) for m in range(d + 1)], d)

    def powr(self, a, p, d=None):
        d = self.D if d is None else d
        a0 = a[0]
        co, c = [], 1.0
        for m in range(d + 1):
            co.append(c * a0 ** (p - m))
            c *= (p - m) / (m + 1)
        return self.compose(a, co, d)

    def sincos(self, a, d=None):
        d = self.D if d is None else d
        a0 = a[0]
        s = [np.sin(a0 + m * math.pi / 2) / math.factorial(m) for m in range(d + 1)]
        c = [np.cos(a0 + m * math.pi / 2) / math.factorial(m) for m in range(d + 1)]
        return self.compose(a, s, d), self.compose(a, c, d)
