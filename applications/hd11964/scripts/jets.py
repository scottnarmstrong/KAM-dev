#!/usr/bin/env python3
"""HD11964-PILOT: truncated multivariate Taylor jets with grid-valued coefficients.  Untrusted design tooling (Apache-2.0).

A jet in `nv` variables of degree `deg` is an array of shape (M(deg), *grid): the Taylor coefficients (NOT derivatives)
of a function of (u, lam) around u = 0, for every lam on a grid.  Monomials are sorted by total degree, so the
coefficients of degree <= d are the first M(d) rows.  Truncated power-series arithmetic is exact in every degree that is
kept; a jet carries its own `deg` (the number of valid degrees), and every operation returns the smallest valid degree of
its inputs (derivatives lose one).
"""
import itertools
import math

import numpy as np


class Space:
    """Monomial bookkeeping for nv variables up to degree D."""

    def __init__(self, nv, D):
        self.nv, self.D = nv, D
        mons = []
        for d in range(D + 1):
            for c in itertools.combinations_with_replacement(range(nv), d):
                e = [0] * nv
                for v in c:
                    e[v] += 1
                mons.append(tuple(e))
        self.mons = mons
        self.idx = {m: i for i, m in enumerate(mons)}
        self.deg = np.array([sum(m) for m in mons])
        self.Mof = [int(np.sum(self.deg <= d)) for d in range(D + 1)]
        self._pairs = {}
        # derivative maps: d/du_v of coefficient array
        self.dmap = []
        for v in range(nv):
            src, dst, fac = [], [], []
            for i, m in enumerate(mons):
                if m[v] > 0:
                    mm = list(m)
                    mm[v] -= 1
                    dst.append(self.idx[tuple(mm)])
                    src.append(i)
                    fac.append(m[v])
            self.dmap.append((np.array(src), np.array(dst), np.array(fac, float)))

    def M(self, d):
        return self.Mof[d]

    def pairs(self, d, bmask_key=None, bmask=None):
        """Pairs (i, j) -> k with deg_i + deg_j <= d, sorted by k; optional restriction of j to a monomial subset."""
        key = (d, bmask_key)
        if key not in self._pairs:
            I, J, K = [], [], []
            Md = self.M(d)
            for i in range(Md):
                for j in range(Md):
                    if self.deg[i] + self.deg[j] > d:
                        continue
                    if bmask is not None and not bmask[j]:
                        continue
                    s = tuple(a + b for a, b in zip(self.mons[i], self.mons[j]))
                    I.append(i)
                    J.append(j)
                    K.append(self.idx[s])
            I, J, K = np.array(I), np.array(J), np.array(K)
            o = np.argsort(K, kind="stable")
            I, J, K = I[o], J[o], K[o]
            starts = np.concatenate([[0], np.nonzero(np.diff(K))[0] + 1])
            self._pairs[key] = (I, J, K[starts], starts)
        return self._pairs[key]

    def var_index(self, v):
        e = [0] * self.nv
        e[v] = 1
        return self.idx[tuple(e)]


class Jet:
    __slots__ = ("S", "c", "deg")

    def __init__(self, S, c, deg=None):
        self.S = S
        self.deg = S.D if deg is None else deg
        self.c = c[: S.M(self.deg)]

    # --- constructors ---------------------------------------------------------------------------
    @staticmethod
    def const(S, val, grid_shape, deg=None):
        deg = S.D if deg is None else deg
        c = np.zeros((S.M(deg),) + tuple(grid_shape), dtype=np.result_type(val, np.float64))
        c[0] = val
        return Jet(S, c, deg)

    @staticmethod
    def var(S, v, val, grid_shape, deg=None):
        """val + u_v."""
        J = Jet.const(S, val, grid_shape, deg)
        J.c[S.var_index(v)] = 1.0
        return J

    def copy(self):
        return Jet(self.S, self.c.copy(), self.deg)

    def trunc(self, d):
        d = min(d, self.deg)
        return Jet(self.S, self.c[: self.S.M(d)], d)

    # --- arithmetic -----------------------------------------------------------------------------
    def _align(self, o):
        d = min(self.deg, o.deg)
        return self.c[: self.S.M(d)], o.c[: self.S.M(d)], d

    def __add__(self, o):
        if isinstance(o, Jet):
            a, b, d = self._align(o)
            return Jet(self.S, a + b, d)
        c = self.c.copy()
        c[0] = c[0] + o
        return Jet(self.S, c, self.deg)

    __radd__ = __add__

    def __neg__(self):
        return Jet(self.S, -self.c, self.deg)

    def __sub__(self, o):
        return self + (-o)

    def __rsub__(self, o):
        return (-self) + o

    def scale(self, s):
        """Multiply by a scalar or by a grid array (constant in u)."""
        return Jet(self.S, self.c * s, self.deg)

    def __mul__(self, o):
        if not isinstance(o, Jet):
            return self.scale(o)
        return mul(self, o)

    __rmul__ = __mul__

    def __truediv__(self, o):
        if isinstance(o, Jet):
            return mul(self, o.recip())
        return self.scale(1.0 / o)

    def __rtruediv__(self, o):
        return self.recip().scale(o)

    def nil(self):
        """The part without constant term."""
        c = self.c.copy()
        c[0] = 0
        return Jet(self.S, c, self.deg)

    def _series(self, coeffs):
        """sum_k coeffs[k] * (self - self0)^k, coeffs are grid arrays or scalars (k = 0..deg)."""
        d = self.nil()
        out = Jet.const(self.S, coeffs[0], self.c.shape[1:], self.deg)
        pw = None
        for k in range(1, self.deg + 1):
            pw = d if pw is None else mul(pw, d)
            out = out + pw.scale(coeffs[k])
        return out

    def recip(self):
        a0 = self.c[0]
        co = [(-1.0) ** k / a0 ** (k + 1) for k in range(self.deg + 1)]
        return self._series(co)

    def sqrt(self):
        a0 = self.c[0]
        co = []
        for k in range(self.deg + 1):
            # binom(1/2, k) a0^(1/2 - k)
            b = 1.0
            for j in range(k):
                b *= (0.5 - j) / (j + 1)
            co.append(b * a0 ** (0.5 - k))
        return self._series(co)

    def sincos(self):
        a0 = self.c[0]
        s0, c0 = np.sin(a0), np.cos(a0)
        cs, sn = [], []
        for k in range(self.deg + 1):
            f = 1.0 / math.factorial(k)
            # d^k/dx^k sin = sin(x + k pi/2)
            sn.append(f * (s0 if k % 4 == 0 else c0 if k % 4 == 1 else -s0 if k % 4 == 2 else -c0))
            cs.append(f * (c0 if k % 4 == 0 else -s0 if k % 4 == 1 else -c0 if k % 4 == 2 else s0))
        return self._series(sn), self._series(cs)

    def d(self, v):
        """Partial derivative in u_v (loses one degree)."""
        if self.deg == 0:
            return Jet(self.S, np.zeros_like(self.c), 0)
        src, dst, fac = self.S.dmap[v]
        nd = self.deg - 1
        Mn = self.S.M(nd)
        out = np.zeros((Mn,) + self.c.shape[1:], dtype=self.c.dtype)
        sel = src < self.S.M(self.deg)
        s, t, f = src[sel], dst[sel], fac[sel]
        keep = t < Mn
        out[t[keep]] = self.c[s[keep]] * f[keep].reshape((-1,) + (1,) * (self.c.ndim - 1))
        return Jet(self.S, out, nd)

    def at0(self):
        return self.c[0]

    def grad0(self):
        """First derivatives at u = 0, list over variables (grid arrays)."""
        return [self.c[self.S.var_index(v)] if self.deg >= 1 else np.zeros_like(self.c[0]) for v in range(self.S.nv)]


def mul(A, B, chunk=4096, bmask_key=None, bmask=None):
    S = A.S
    d = min(A.deg, B.deg)
    I, J, Ku, starts = S.pairs(d, bmask_key, bmask)
    a = A.c[: S.M(d)]
    b = B.c[: S.M(d)]
    gshape = a.shape[1:]
    G = int(np.prod(gshape)) if gshape else 1
    a2 = a.reshape(a.shape[0], G)
    b2 = b.reshape(b.shape[0], G)
    out = np.zeros((S.M(d), G), dtype=np.result_type(a, b))
    for g0 in range(0, G, chunk):
        g1 = min(G, g0 + chunk)
        prod = a2[I, g0:g1] * b2[J, g0:g1]
        out[Ku, g0:g1] = np.add.reduceat(prod, starts, axis=0)
    return Jet(S, out.reshape((S.M(d),) + gshape), d)


def embed(J, S2, varmap, grid_axes, grid_shape):
    """Embed a jet of a smaller space into S2 (variable v -> varmap[v]) and broadcast its grid onto `grid_shape`, the
    small grid sitting on axes `grid_axes` of the big grid."""
    S = J.S
    M2 = S2.M(J.deg)
    out = np.zeros((M2,) + tuple(grid_shape), dtype=J.c.dtype)
    shape = [1] * len(grid_shape)
    for ax, n in zip(grid_axes, J.c.shape[1:]):
        shape[ax] = n
    for i in range(S.M(J.deg)):
        m = S.mons[i]
        e = [0] * S2.nv
        for v, k in enumerate(m):
            e[varmap[v]] += k
        out[S2.idx[tuple(e)]] = np.broadcast_to(J.c[i].reshape(shape), grid_shape)
    return Jet(S2, out, J.deg)
