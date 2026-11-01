#!/usr/bin/env python3
"""HD11964 phase 2: the order-2 generators chi1, chi2 of the Lean F at high precision (untrusted, Apache-2.0).

The generators of `prod2.py` (the Lean identity `chartRate_approxIntegral₂`; see that file for the formulas), on
kamx-hd-layer's worst cell (`tf_cell.py`: centre, radii h, normalised variables u = (x - centre)/h in the order
(dLam_c, dLam_b, dxi_c, deta_c, dxi_b, deta_b)), computed in fixed point with Python integers at scale 2^FB:

  1. the charts of c and b on their angle grids, as Taylor jets (degree DJ in the planet's three variables), in
     mpmath at PREC bits, rounded to 2^-FB;
  2. P = mu f, f = |p_c + p_b|^2/2 - nu_c nu_b |q_c - q_b|^(-1/2 x 2), on the N1 x N2 grid as 6-variable jets of
     degree DJ (integer jet arithmetic; the constant terms of the series by exact integer division and isqrt);
  3. its Fourier coefficients by an EXACT sliced DFT: the integer data and the integer twiddles (cos, sin at
     2^-TB, mpmath) are cut into SB-bit slices whose products and sums are exact in float64 (BLAS), and the slice
     products are recombined in integers;
  4. chi1 = Pi_S P / (i k.omega(Lam)) mode by mode, 1/(k.omega(Lam_0 + h u)) as an exact Taylor series in
     (u_Lam_c, u_Lam_b) (mpmath);
  5. G2 = {P - 1/2 Pi_S P, chi1} on the grid (the four canonical pairs; slow derivatives exact on the jets, angle
     derivatives by exact inverse DFTs), its exact DFT, and chi2 = Pi_S G2 / (i k.omega(Lam));
  6. the tails r1 = (1 - Pi_S) P, r2 = (1 - Pi_S) G2 and the l1 bounds of D_i r1, D_i r2 (terms T1, T2).

Accuracy: every stored value is a 2^-FB fixed-point number; the DFT, products and series are exact up to one
rounding per operation (|error| <= a few units of 2^-FB) except the aliasing of the grid (below 2^-128 of the
function for the default grid at e_c = 0.6, estimated) and the Taylor truncation at degree DJ (exact for the
coefficients kept: the jets are truncated polynomials of the exact functions).

Output (gzipped JSON, see `--out`): the cell, the mode set S, the monomials, and for chi1 (degree DJ) and chi2
(degree DJ - 1) the coefficients c[m][(k_c, k_b)] of  chi(lam, u) = sum_m u^m sum_k c[m][k] e^{i(k_c lam_c +
k_b lam_b)}  for every k in S with k_b >= 0 (the rest by c[-k] = conj c[k]), as integer pairs (re, im) at scale
2^OUTB (OUTB >= 128). Also the float64 cross-check against `prod2.py`'s construction on the same grid.

Usage: python3 -I prod2_hp.py --out=FILE.json.gz [--N1=448] [--N2=72] [--Kc=80] [--Kb=20] [--DJ=4] [--FB=184]
       [--OUTB=160] [--check]          (--check: the float64 cross-check)
Reading: `load_box(path, "chi1", P=128)` expands a generator to the full box at 2^P, keyed as `tf_slice.py`'s nodes.
Run under the 8 GB cap.
"""
import gzip
import json
import math
import os
import sys
import time

import mpmath as mp
import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import hd11964_model as HM  # noqa: E402

H_CELL = [HM.Fr(11, 10 ** 4), HM.Fr(4, 10 ** 3), HM.Fr(3, 100), HM.Fr(15, 1000), HM.Fr(8, 100), HM.Fr(8, 100)]
CMAP, BMAP = (0, 2, 3), (1, 4, 5)


def opt(name, default):
    return next((x.split("=", 1)[1] for x in sys.argv if x.startswith("--%s=" % name)), default)


# ------------------------------------------------------------------------------------------------- monomials
def mons(nv, D):
    out = []
    for d in range(D + 1):
        def rec(prefix, left, k):
            if k == nv - 1:
                out.append(tuple(prefix + [left]))
                return
            for a in range(left, -1, -1):
                rec(prefix + [a], left - a, k + 1)
        rec([], d, 0)
    return out


class Space:
    def __init__(self, nv, D):
        self.nv, self.D = nv, D
        self.mons = mons(nv, D)
        self.idx = {m: i for i, m in enumerate(self.mons)}
        self.deg = [sum(m) for m in self.mons]
        self._pairs = {}

    def M(self, d):
        return sum(1 for g in self.deg if g <= d)

    def pairs(self, d):
        if d not in self._pairs:
            out = []
            Md = self.M(d)
            for i in range(Md):
                for j in range(Md):
                    if self.deg[i] + self.deg[j] <= d:
                        out.append((i, j, self.idx[tuple(x + y for x, y in zip(self.mons[i], self.mons[j]))]))
            self._pairs[d] = out
        return self._pairs[d]


# ------------------------------------------------------------------------------------- mpmath jets (charts)
class MJ:
    __slots__ = ("S", "c")

    def __init__(self, S, c):
        self.S, self.c = S, c

    @staticmethod
    def const(S, v):
        c = [mp.mpf(0)] * len(S.mons)
        c[0] = mp.mpf(v)
        return MJ(S, c)

    @staticmethod
    def var(S, j, v0, h):
        J = MJ.const(S, v0)
        e = [0] * S.nv
        e[j] = 1
        J.c[S.idx[tuple(e)]] = mp.mpf(h)
        return J

    def __add__(self, o):
        if isinstance(o, MJ):
            return MJ(self.S, [a + b for a, b in zip(self.c, o.c)])
        c = list(self.c)
        c[0] += o
        return MJ(self.S, c)

    __radd__ = __add__

    def __neg__(self):
        return MJ(self.S, [-a for a in self.c])

    def __sub__(self, o):
        return self + (-o)

    def __rsub__(self, o):
        return (-self) + o

    def __mul__(self, o):
        if not isinstance(o, MJ):
            return MJ(self.S, [a * o for a in self.c])
        c = [mp.mpf(0)] * len(self.c)
        for i, j, t in self.S.pairs(self.S.D):
            if self.c[i] and o.c[j]:
                c[t] += self.c[i] * o.c[j]
        return MJ(self.S, c)

    __rmul__ = __mul__

    def series(self, coefs):
        d = MJ(self.S, [mp.mpf(0)] + list(self.c[1:]))
        out, p = MJ.const(self.S, coefs[0]), MJ.const(self.S, 1)
        for k in range(1, self.S.D + 1):
            p = p * d
            out = out + p * coefs[k]
        return out

    def recip(self):
        a0 = self.c[0]
        return self.series([(-1) ** k / a0 ** (k + 1) for k in range(self.S.D + 1)])

    def __truediv__(self, o):
        return self * o.recip() if isinstance(o, MJ) else self * (1 / mp.mpf(o))

    def sqrt(self):
        a0 = self.c[0]
        return self.series([mp.binomial(mp.mpf(1) / 2, k) * a0 ** (mp.mpf(1) / 2 - k) for k in range(self.S.D + 1)])

    def sincos(self):
        a0 = self.c[0]
        s0, c0 = mp.sin(a0), mp.cos(a0)
        ds, dc = [s0, c0, -s0, -c0], [c0, -s0, -c0, s0]
        return (self.series([ds[k % 4] / mp.factorial(k) for k in range(self.S.D + 1)]),
                self.series([dc[k % 4] / mp.factorial(k) for k in range(self.S.D + 1)]))


def chart(S, nu, lam, L0, x0, e0, h):
    """q, p of one planet at the angle lam (LP's chart, as `normal_form.chart_planet`), jets in its 3 variables."""
    Lam, xi, eta = MJ.var(S, 0, L0, h[0]), MJ.var(S, 1, x0, h[1]), MJ.var(S, 2, e0, h[2])
    G = (xi * xi + eta * eta) * mp.mpf(0.5)
    K = 1 - G / Lam
    be = ((1 - G / (Lam * 2)) / Lam).sqrt()
    v0, v1 = be * xi, be * eta
    a, b = v0.c[0], v1.c[0]
    F = lam + a * mp.sin(lam) - b * mp.cos(lam)
    for _ in range(300):
        st = (F - a * mp.sin(F) + b * mp.cos(F) - lam) / (1 - a * mp.cos(F) - b * mp.sin(F))
        F -= st
        if abs(st) < mp.mpf(2) ** (-mp.mp.prec + 6):
            break
    F = MJ.const(S, F)
    for _ in range(S.D + 1):
        sn, cs = F.sincos()
        F = F - (F - v0 * sn + v1 * cs - lam) / (1 - v0 * cs - v1 * sn)
    sn, cs = F.sincos()
    J = 1 - v0 * cs - v1 * sn
    vu = (v0 * cs + v1 * sn) / (1 + K)
    s = Lam * Lam * (1 / (nu * nu))
    q0, q1 = s * (K * cs - v0 + vu * v0), s * (K * sn - v1 + vu * v1)
    c = (Lam * J).recip() * (nu * nu)
    return [q0, q1, c * (vu * v1 - sn), c * (cs - vu * v0)]


# --------------------------------------------------------------------------------- fixed-point grid jets
FB = int(opt("FB", "184"))
ONE = 1 << FB


def fx(x):
    """mpf -> fixed point int."""
    return int(mp.nint(x * mp.mpf(2) ** FB))


def oarr(shape, fill=0):
    a = np.empty(shape, dtype=object)
    a.fill(fill)
    return a


class FJ:
    """6-variable jet: list of object arrays (ints at 2^FB), broadcastable onto the grid."""
    __slots__ = ("S", "c", "deg")

    def __init__(self, S, c, deg):
        self.S, self.c, self.deg = S, c, deg

    def __add__(self, o):
        d = min(self.deg, o.deg)
        return FJ(self.S, [a + b for a, b in zip(self.c[: self.S.M(d)], o.c[: self.S.M(d)])], d)

    def __sub__(self, o):
        d = min(self.deg, o.deg)
        return FJ(self.S, [a - b for a, b in zip(self.c[: self.S.M(d)], o.c[: self.S.M(d)])], d)

    def __neg__(self):
        return FJ(self.S, [-a for a in self.c], self.deg)

    def mul(self, o, d=None):
        d = min(self.deg, o.deg) if d is None else min(d, self.deg, o.deg)
        acc = [None] * self.S.M(d)
        for i, j, t in self.S.pairs(d):
            p = self.c[i] * o.c[j]
            acc[t] = p if acc[t] is None else acc[t] + p
        return FJ(self.S, [(a + (ONE >> 1)) >> FB if a is not None else 0 for a in acc], d)

    def smul(self, z, sh=FB):
        """(z / 2^sh) * self, z an int."""
        half = 1 << (sh - 1) if sh > 0 else 0
        return FJ(self.S, [(a * z + half) >> sh for a in self.c], self.deg)

    def trunc(self, d):
        return FJ(self.S, self.c[: self.S.M(d)], min(d, self.deg))

    def du(self, v):
        """d/du_v (normalised variable): exponent times the shifted coefficient; loses one degree."""
        nd = self.deg - 1
        out = [0] * self.S.M(nd)
        for i, mon in enumerate(self.S.mons[: self.S.M(self.deg)]):
            if mon[v] and sum(mon) - 1 <= nd:
                e = list(mon)
                e[v] -= 1
                out[self.S.idx[tuple(e)]] = self.c[i] * mon[v]
        return FJ(self.S, out, nd)

    def series(self, coefs):
        """sum_k coefs[k] d^k, d = self - constant term; coefs[k] fixed-point (arrays or ints)."""
        d = FJ(self.S, [0] + list(self.c[1:]), self.deg)
        out = [0] * self.S.M(self.deg)
        out[0] = coefs[0]
        out = FJ(self.S, out, self.deg)
        p = None
        for k in range(1, self.deg + 1):
            p = d if p is None else p.mul(d)
            term = FJ(self.S, [(a * coefs[k] + (ONE >> 1)) >> FB for a in p.c], p.deg)
            out = out + term
        return out


def vec_isqrt(a):
    return np.vectorize(math.isqrt, otypes=[object])(a)


def embed(jets3, S6, vmap, axis, n1, n2):
    """3-variable chart jets (lists over the angle grid of MJ) -> FJ with arrays of shape (n1, 1) or (1, n2)."""
    S3 = jets3[0].S
    shape = (n1, 1) if axis == 0 else (1, n2)
    c = [0] * S6.M(S3.D)
    for i, mon in enumerate(S3.mons):
        e = [0] * 6
        for v, k in enumerate(mon):
            e[vmap[v]] += k
        arr = oarr(shape)
        flat = arr.reshape(-1)
        for g, J in enumerate(jets3):
            flat[g] = fx(J.c[i])
        c[S6.idx[tuple(e)]] = arr
    return FJ(S6, c, S3.D)


# -------------------------------------------------------------------------------------- the exact DFT
SB = int(opt("SB", "21"))


def slices(X, L):
    """X (object ints) ~ sum_s Xs * 2^(e - SB (s+1)); returns e and the float64 slices (|Xs| <= 2^(SB-1))."""
    mx = int(np.max(np.abs(X))) if X.size else 0
    e = max(mx.bit_length() + 1, SB)
    R = X.copy()
    out = []
    for s in range(L):
        sh = e - SB * (s + 1)
        if sh > 0:
            Xs = (R + (1 << (sh - 1))) >> sh
            R = R - (Xs << sh)
        else:
            Xs = R << (-sh)
            R = R * 0
        out.append(Xs.astype(np.float64))
        if sh <= 0:
            break
    return e, out


def topbits(X):
    mx = int(np.max(np.abs(X))) if X.size else 0
    return max(mx.bit_length() + 1, SB)


def matmul_exact(A, B, out_shift, guard=24):
    """(A @ B) >> out_shift for object-int matrices.  The slices of A and B are SB-bit integers in float64 whose
    products summed over the inner dimension are below 2^53 (exact in BLAS); every slice pair whose contribution can
    exceed 2^-guard units of the result is kept, so the result is exact up to a few units (plus the rounding)."""
    n = A.shape[1]
    lg = int(math.ceil(math.log2(max(n, 2))))
    assert 2 * (SB - 1) + lg < 53, "slice bits too large for the inner dimension"
    eA0, eB0 = topbits(A), topbits(B)
    L = max(2, int(math.ceil((eA0 + eB0 + lg - out_shift + guard + 2) / SB)))
    eA, As = slices(A, L)
    eB, Bs = slices(B, L)
    acc = None
    for dsum in range(len(As) + len(Bs) - 1):
        sh = eA + eB - SB * (dsum + 2) - out_shift
        if sh + 2 * SB + lg < -guard:
            break
        Dd = None
        for t in range(len(As)):
            s = dsum - t
            if 0 <= s < len(Bs):
                prod = As[t] @ Bs[s]
                Dd = prod if Dd is None else Dd + prod
        if Dd is None:
            continue
        Di = np.rint(Dd).astype(np.int64).astype(object)
        term = Di << sh if sh >= 0 else (Di + (1 << (-sh - 1))) >> (-sh)
        acc = term if acc is None else acc + term
    return acc


class DFT:
    """Exact 2-D DFT on the N1 x N2 grid (forward to the half plane k_b >= 0; inverse to real values)."""

    def __init__(self, N1, N2, TB=None):
        self.N1, self.N2 = N1, N2
        self.TB = FB if TB is None else TB
        sc = mp.mpf(2) ** self.TB
        self.c1 = [int(mp.nint(mp.cos(2 * mp.pi * r / N1) * sc)) for r in range(N1)]
        self.s1 = [int(mp.nint(mp.sin(2 * mp.pi * r / N1) * sc)) for r in range(N1)]
        self.c2 = [int(mp.nint(mp.cos(2 * mp.pi * r / N2) * sc)) for r in range(N2)]
        self.s2 = [int(mp.nint(mp.sin(2 * mp.pi * r / N2) * sc)) for r in range(N2)]
        self.K2h = N2 // 2 + 1

    def tw1(self, ks, ms):
        C = oarr((len(ks), len(ms)))
        S = oarr((len(ks), len(ms)))
        for a, k in enumerate(ks):
            for b, m in enumerate(ms):
                r = (k * m) % self.N1
                C[a, b], S[a, b] = self.c1[r], self.s1[r]
        return C, S

    def tw2(self, ks, ms, w=None):
        C = oarr((len(ks), len(ms)))
        S = oarr((len(ks), len(ms)))
        for a, k in enumerate(ks):
            for b, m in enumerate(ms):
                r = (k * m) % self.N2
                f = 1 if w is None else w[a]
                C[a, b], S[a, b] = self.c2[r] * f, self.s2[r] * f
        return C, S

    def forward(self, X, kcs):
        """X: object array (M, N1, N2) at 2^FB -> (re, im) arrays (M, len(kcs), K2h) at 2^FB."""
        M, N1, N2 = X.shape
        K2 = self.K2h
        C2, S2 = self.tw2(range(K2), range(N2))
        X2 = X.reshape(M * N1, N2)
        Y = matmul_exact(X2, np.concatenate([C2.T, S2.T], axis=1), self.TB)
        Yre = Y[:, :K2].reshape(M, N1, K2)
        Yim = (-Y[:, K2:]).reshape(M, N1, K2)
        del Y
        C1, S1 = self.tw1(list(kcs), range(N1))
        Yre2 = np.transpose(Yre, (1, 0, 2)).reshape(N1, M * K2)
        Yim2 = np.transpose(Yim, (1, 0, 2)).reshape(N1, M * K2)
        cols = M * K2
        Z = matmul_exact(np.concatenate([C1, S1], axis=0), np.concatenate([Yre2, Yim2], axis=1), self.TB)
        nk = len(kcs)
        Zre = Z[:nk, :cols] + Z[nk:, cols:]
        Zim = Z[:nk, cols:] - Z[nk:, :cols]
        den = N1 * N2
        Zre = (Zre + den // 2) // den
        Zim = (Zim + den // 2) // den
        sh = (len(kcs), M, self.K2h)
        return (np.transpose(Zre.reshape(sh), (1, 0, 2)), np.transpose(Zim.reshape(sh), (1, 0, 2)))

    def inverse(self, Cre, Cim, kcs, kb_max, w0):
        """Coefficients (M, len(kcs), kb_max + 1) (k_b >= 0 half plane, real function) -> grid (M, N1, N2).
        w0 = 1 when the k_b = 0 column holds both signs of k_c, 2 when it holds k_c > 0 only."""
        M = Cre.shape[0]
        N1, N2 = self.N1, self.N2
        CT1, ST1 = self.tw1(list(kcs), range(N1))          # (K, N1): cos(2 pi k m / N1)
        K2 = kb_max + 1
        cols = M * K2
        A_re = np.transpose(Cre, (1, 0, 2)).reshape(len(kcs), cols)
        A_im = np.transpose(Cim, (1, 0, 2)).reshape(len(kcs), cols)
        Y = matmul_exact(np.concatenate([CT1.T, ST1.T], axis=0), np.concatenate([A_re, A_im], axis=1), self.TB)
        Yre = Y[:N1, :cols] - Y[N1:, cols:]
        Yim = Y[:N1, cols:] + Y[N1:, :cols]
        del Y
        w = [w0] + [2] * kb_max
        C2, S2 = self.tw2(range(K2), range(N2), w)           # (K2, N2), weights folded in
        Yre = np.transpose(Yre.reshape(N1, M, K2), (1, 0, 2)).reshape(M * N1, K2)
        Yim = np.transpose(Yim.reshape(N1, M, K2), (1, 0, 2)).reshape(M * N1, K2)
        X = matmul_exact(np.concatenate([Yre, Yim], axis=1), np.concatenate([C2, -S2], axis=0), self.TB)
        return X.reshape(M, N1, N2)


# ------------------------------------------------------------------------------------------ the producer
def omega_inv_jets(S6, nu, Lc, Kc, Kb, kcs, kbs, DJ):
    """For every (k_c, k_b) in the box: the Taylor coefficients of 1/(k.omega(Lam_c + h_c u_c, Lam_b + h_b u_b))
    in (u_Lam_c, u_Lam_b), degree DJ, fixed point; returns dict (a, b) -> object array (len(kcs), len(kbs))."""
    hL = [HM.R(H_CELL[0]), HM.R(H_CELL[1])]
    out = {}
    pairs2 = [(a, b) for a in range(DJ + 1) for b in range(DJ + 1 - a)]
    for (a, b) in pairs2:
        out[(a, b)] = oarr((len(kcs), len(kbs)))
    # omega_j(L) = nu^3 / L^3 ; Taylor of omega_j in u_j: om_j[m] = nu^3 C(-3, m) L^(-3-m) h^m
    om = []
    for j in range(2):
        om.append([nu[j] ** 3 * mp.binomial(-3, m) * Lc[j] ** (-3 - m) * hL[j] ** m for m in range(DJ + 1)])
    for ia, kc in enumerate(kcs):
        for ib, kb in enumerate(kbs):
            if kc == 0 and kb == 0:
                continue
            # s(u) = kc om_c(u_c) + kb om_b(u_b): bivariate polynomial; its reciprocal by series in (u_c, u_b)
            s = {(m, 0): kc * om[0][m] for m in range(DJ + 1)}
            for m in range(1, DJ + 1):
                s[(0, m)] = kb * om[1][m]
            s[(0, 0)] = kc * om[0][0] + kb * om[1][0]
            s0 = s[(0, 0)]
            dlt = {k: v / s0 for k, v in s.items() if k != (0, 0)}
            # 1/s = (1/s0) sum_n (-dlt)^n
            res = {(0, 0): mp.mpf(1)}
            pw = {(0, 0): mp.mpf(1)}
            for n in range(1, DJ + 1):
                new = {}
                for (p1, q1), v1 in pw.items():
                    for (p2, q2), v2 in dlt.items():
                        if p1 + p2 + q1 + q2 <= DJ:
                            new[(p1 + p2, q1 + q2)] = new.get((p1 + p2, q1 + q2), 0) - v1 * v2
                pw = new
                for k, v in pw.items():
                    res[k] = res.get(k, 0) + v
            for k in pairs2:
                out[k][ia, ib] = fx(res.get(k, 0) / s0)
    return out


def solve_hom(S6, Rre, Rim, inv, kcs, kbs, DJ_out):
    """chi_k(u) = R_k(u) / (i s_k(u)) on the box (k in S): jets in the 6 variables times the 2-variable series
    of 1/s in (u_Lam_c, u_Lam_b); returns (re, im) object arrays (M, K1, K2)."""
    M = S6.M(DJ_out)
    out_re = [oarr((len(kcs), len(kbs))) for _ in range(M)]
    out_im = [oarr((len(kcs), len(kbs))) for _ in range(M)]
    for t in range(M):
        out_re[t][...] = 0
        out_im[t][...] = 0
    for i, mon in enumerate(S6.mons[: S6.M(DJ_out)]):
        for (a, b), arr in inv.items():
            e = list(mon)
            e[0] += a
            e[1] += b
            if sum(e) > DJ_out:
                continue
            t = S6.idx[tuple(e)]
            # (re + i im) / (i s) = (im - i re) / s
            out_re[t] = out_re[t] + ((Rim[i] * arr + (ONE >> 1)) >> FB)
            out_im[t] = out_im[t] - ((Rre[i] * arr + (ONE >> 1)) >> FB)
    return np.array(out_re), np.array(out_im)


def main():
    out_path = opt("out", "prod2_hp.json.gz")
    N1, N2 = int(opt("N1", "448")), int(opt("N2", "72"))
    Kc, Kb = int(opt("Kc", "80")), int(opt("Kb", "20"))
    DJ = int(opt("DJ", "4"))
    OUTB = int(opt("OUTB", "160"))
    ec = mp.mpf(opt("ec", "0.6"))
    mp.mp.prec = int(opt("PREC", "256"))
    m = HM.Model(dps=80)
    mp.mp.prec = int(opt("PREC", "256"))
    nu = [HM.R(x) for x in m.nu]
    mu = HM.R(m.mu)
    rho, d = [HM.Fr(1, 10 ** 4), HM.Fr(3, 10 ** 3)], HM.Fr(1, 10 ** 3)
    Lc = [m.Lam(i) - HM.R(rho[i] + d) for i in range(2)]
    Gc = Lc[0] * (1 - mp.sqrt(1 - ec ** 2))
    xi_c = mp.sqrt(2 * Gc)
    h = [HM.R(x) for x in H_CELL]
    t0 = time.time()
    S3 = Space(3, DJ)
    S6 = Space(6, DJ)
    jc = [chart(S3, nu[0], 2 * mp.pi * g / N1, Lc[0], xi_c, mp.mpf(0), (h[0], h[2], h[3])) for g in range(N1)]
    jb = [chart(S3, nu[1], 2 * mp.pi * g / N2, Lc[1], mp.mpf(0), mp.mpf(0), (h[1], h[4], h[5])) for g in range(N2)]
    t1 = time.time()
    print("charts %.1fs" % (t1 - t0), flush=True)
    Q = [[embed([J[k] for J in jc], S6, CMAP, 0, N1, N2) for k in range(4)],
         [embed([J[k] for J in jb], S6, BMAP, 1, N1, N2) for k in range(4)]]
    qc, pc = Q[0][:2], Q[0][2:]
    qb, pb = Q[1][:2], Q[1][2:]
    # f = |p_c + p_b|^2 / 2 - nu_c nu_b / |q_c - q_b|
    Px, Py = pc[0] + pb[0], pc[1] + pb[1]
    dx, dy = qc[0] - qb[0], qc[1] - qb[1]
    kin = Px.mul(Px) + Py.mul(Py)
    r2 = dx.mul(dx) + dy.mul(dy)
    a0 = r2.c[0]
    inv0 = (ONE * ONE + 0) // a0                                   # 1/r2 at 2^FB
    isq = (ONE * ONE) // vec_isqrt(a0 * ONE)                       # r2^(-1/2) at 2^FB
    coefs = [isq]
    for k in range(1, DJ + 1):
        # binom(-1/2, k) r2^(-1/2 - k)
        cprev = coefs[-1]
        bk = mp.binomial(-0.5, k) / mp.binomial(-0.5, k - 1)
        z = fx(bk)
        coefs.append((((cprev * inv0) >> FB) * z) >> FB)
    g = r2.series(coefs)
    nucnb = fx(nu[0] * nu[1])
    f = FJ(S6, [(a >> 1) for a in kin.c], kin.deg) - g.smul(nucnb)
    P = f.smul(fx(mu))
    # broadcast every coefficient to the full grid
    Pg = np.array([np.broadcast_to(np.asarray(a, dtype=object), (N1, N2)).copy() if isinstance(a, np.ndarray)
                   else np.full((N1, N2), a, dtype=object) for a in P.c])
    t2 = time.time()
    print("P on the grid %.1fs" % (t2 - t1), flush=True)
    dft = DFT(N1, N2)
    kfull = [k if k < N1 // 2 else k - N1 for k in range(N1)]
    Pre, Pim = dft.forward(Pg, kfull)
    t3 = time.time()
    print("DFT(P) %.1fs" % (t3 - t2), flush=True)
    # the mode set S (k_b >= 0 half plane): |k_c| <= Kc, 0 <= k_b <= Kb, k != 0
    kcS = list(range(-Kc, Kc + 1))
    kbS = list(range(0, Kb + 1))
    colc = [kfull.index(k) for k in kcS]
    PSre = Pre[:, colc, :][:, :, : Kb + 1].copy()
    PSim = Pim[:, colc, :][:, :, : Kb + 1].copy()
    # the k_b = 0 column: keep k_c > 0 only (k_c < 0 by conjugation), drop k = 0
    zc = kcS.index(0)
    for t in range(PSre.shape[0]):
        PSre[t, : zc + 1, 0] = 0
        PSim[t, : zc + 1, 0] = 0
    inv = omega_inv_jets(S6, nu, Lc, Kc, Kb, kcS, kbS, DJ)
    chi1re, chi1im = solve_hom(S6, PSre, PSim, inv, kcS, kbS, DJ)
    t4 = time.time()
    print("chi1 %.1fs" % (t4 - t3), flush=True)
    # A = P - 1/2 Pi_S P (grid values and angle derivatives), chi1 on the grid
    def inv_grid(Cre, Cim, deg):
        return dft.inverse(Cre, Cim, kcS, Kb, 2)

    def ramp(Cre, Cim, ks, axis):
        k = np.array(ks, dtype=object)
        kk = k.reshape(1, -1, 1) if axis == 0 else k.reshape(1, 1, -1)
        return -Cim * kk, Cre * kk

    # Pi_S P on the grid; the full-spectrum angle derivatives of A
    PSg = inv_grid(PSre, PSim, DJ)
    Ag = Pg - ((PSg + 1) >> 1)
    del Pg
    Are, Aim = Pre.copy(), Pim.copy()
    for t in range(Are.shape[0]):
        Are[t][np.ix_(colc, list(range(Kb + 1)))] -= (PSre[t] + 1) >> 1
        Aim[t][np.ix_(colc, list(range(Kb + 1)))] -= (PSim[t] + 1) >> 1
    # (the k_b = 0, k_c < 0 entries of Pi_S P were zeroed; the full-spectrum half plane keeps both signs of k_c at
    #  k_b = 0, so the conjugate entries are subtracted here as well)
    for t in range(Are.shape[0]):
        for a, kc in enumerate(kcS):
            if kc < 0:
                src = kcS.index(-kc)
                Are[t][colc[a], 0] -= (PSre[t][src, 0] + 1) >> 1
                Aim[t][colc[a], 0] += (PSim[t][src, 0] + 1) >> 1
    kb_all = list(range(dft.K2h))

    def inv_full(Cre, Cim):
        return dft.inverse(Cre, Cim, kfull, dft.K2h - 1, 1)

    del PSg
    Al = [inv_full(*ramp(Are, Aim, kfull, 0)), inv_full(*ramp(Are, Aim, kb_all, 1))]
    del Are, Aim
    chig = inv_grid(chi1re, chi1im, DJ)
    chil = [inv_grid(*ramp(chi1re, chi1im, kcS, 0), DJ), inv_grid(*ramp(chi1re, chi1im, kbS, 1), DJ)]
    t5 = time.time()
    print("inverse DFTs %.1fs" % (t5 - t4), flush=True)
    # G2 = {A, chi1}: sum_j A_lam_j chi_Lam_j - A_Lam_j chi_lam_j + A_xi_j chi_eta_j - A_eta_j chi_xi_j
    def fj(arr, deg):
        return FJ(S6, list(arr), deg)

    A, X = fj(Ag, DJ), fj(chig, DJ)
    AL = [fj(Al[0], DJ), fj(Al[1], DJ)]
    XL = [fj(chil[0], DJ), fj(chil[1], DJ)]
    hinv = [fx(1 / x) for x in h]
    G2 = None
    for j in range(2):
        t = AL[j].mul(X.du(j).smul(hinv[j]), DJ - 1) - A.du(j).smul(hinv[j]).mul(XL[j], DJ - 1)
        xv, ev = 2 + 2 * j, 3 + 2 * j
        t = t + A.du(xv).smul(hinv[xv]).mul(X.du(ev).smul(hinv[ev])) - A.du(ev).smul(hinv[ev]).mul(
            X.du(xv).smul(hinv[xv]))
        G2 = t if G2 is None else G2 + t
    del A, X, AL, XL, Al, chil, chig, Ag
    Gg = np.array([np.broadcast_to(np.asarray(a, dtype=object), (N1, N2)).copy() if isinstance(a, np.ndarray)
                   else np.full((N1, N2), a, dtype=object) for a in G2.c])
    del G2
    t6 = time.time()
    print("G2 %.1fs" % (t6 - t5), flush=True)
    Gre, Gim = dft.forward(Gg, kfull)
    GSre = Gre[:, colc, :][:, :, : Kb + 1].copy()
    GSim = Gim[:, colc, :][:, :, : Kb + 1].copy()
    for t in range(GSre.shape[0]):
        GSre[t, : zc + 1, 0] = 0
        GSim[t, : zc + 1, 0] = 0
    chi2re, chi2im = solve_hom(S6, GSre, GSim, inv, kcS, kbS, DJ - 1)
    t7 = time.time()
    print("DFT(G2), chi2 %.1fs" % (t7 - t6), flush=True)

    # ---- T1, T2: l1 bounds of D_i (1 - Pi_S) P and D_i (1 - Pi_S) G2 on the cell (degree <= 3, |u| <= 1)
    def tail_l1(Cre, Cim, deg_max):
        res = []
        Mx = min(S6.M(3), Cre.shape[0])
        for i, kk in ((0, kfull), (1, kb_all)):
            tot = 0.0
            for t in range(Mx):
                for a, kc in enumerate(kfull):
                    for b in kb_all:
                        if abs(kc) <= Kc and b <= Kb:
                            continue
                        if b > dft.K2h - 1:
                            continue
                        w = (1 if b == 0 else 2) * abs(kc if i == 0 else b)
                        if w == 0:
                            continue
                        re, im = Cre[t][a, b], Cim[t][a, b]
                        if re or im:
                            tot += w * math.hypot(float(re), float(im)) / 2.0 ** FB
            res.append(tot)
        return res

    T1 = tail_l1(Pre, Pim, DJ)
    T2 = tail_l1(Gre, Gim, DJ - 1)
    t8 = time.time()
    print("tails %.1fs" % (t8 - t7), "T1", ["%.4e" % x for x in T1], "T2", ["%.4e" % x for x in T2], flush=True)

    # ---- output
    sh = FB - OUTB

    def pack(Cre, Cim, deg):
        outm = {}
        for t, mon in enumerate(S6.mons[: S6.M(deg)]):
            ent = {}
            for a, kc in enumerate(kcS):
                for b, kb in enumerate(kbS):
                    if kb == 0 and kc <= 0:
                        continue
                    re = (int(Cre[t][a, b]) + (1 << (sh - 1))) >> sh
                    im = (int(Cim[t][a, b]) + (1 << (sh - 1))) >> sh
                    if re or im:
                        ent["%d,%d" % (kc, kb)] = [re, im]
            outm[",".join(map(str, mon))] = ent
        return outm

    res = dict(
        format="HD11964 order-2 generators, Taylor x Fourier, fixed point 2^-OUTB",
        cell=dict(Lam=[mp.nstr(x, 40) for x in Lc], xi=[mp.nstr(xi_c, 40), "0"], eta=["0", "0"], ec=str(ec),
                  h=[str(x) for x in H_CELL], vars=["dLam_c", "dLam_b", "dxi_c", "deta_c", "dxi_b", "deta_b"]),
        model=dict(nu=[str(x) for x in m.nu], mu=str(m.mu), P="mu f, f = |p_c + p_b|^2/2 - nu_c nu_b/|q_c - q_b|",
                   bracket="{a,b} = sum_j a_lam b_Lam - a_Lam b_lam + a_xi b_eta - a_eta b_xi (Lean pb)"),
        S=dict(Kc=Kc, Kb=Kb, note="0 < |k|, |k_c| <= Kc, |k_b| <= Kb; stored k_b > 0 or (k_b = 0, k_c > 0)"),
        convention="chi(lam, u) = sum_m u^m sum_k c[m][k] e^{i (k_c lam_c + k_b lam_b)}, c[-k] = conj c[k]",
        OUTB=OUTB, FB=FB, grid=[N1, N2], DJ=DJ,
        chi1=pack(chi1re, chi1im, DJ), chi2=pack(chi2re, chi2im, DJ - 1),
        T1_l1=T1, T2_l1=T2,
        seconds=dict(charts=t1 - t0, P=t2 - t1, dftP=t3 - t2, chi1=t4 - t3, inv=t5 - t4, G2=t6 - t5, chi2=t7 - t6,
                     tails=t8 - t7))
    del Pre, Pim, Gre, Gim, Gg, chi1re, chi1im, chi2re, chi2im
    if "--check" in sys.argv:
        check(res, N1, N2, Kc, Kb, [float(x) for x in Lc], float(xi_c), DJ)
    with gzip.open(out_path, "wt") as fh:
        json.dump(res, fh)
    print("wrote", out_path, flush=True)


def load_box(path, name, P=128):
    """For kamx-hd-layer: read a generator ("chi1" or "chi2") and expand it to the full box at scale 2^P, keyed as
    `tf_slice.py`'s two-angle nodes: {monomial tuple: {(k_c, k_b): (re, im)}} with c[-k] = conj c[k]."""
    with gzip.open(path, "rt") as fh:
        res = json.load(fh)
    sh = res["OUTB"] - P
    out = {}
    for mk, ent in res[name].items():
        mon = tuple(int(x) for x in mk.split(","))
        box = {}
        for kk, (re, im) in ent.items():
            kc, kb = map(int, kk.split(","))
            r = (re + (1 << (sh - 1))) >> sh if sh > 0 else re << (-sh)
            i = (im + (1 << (sh - 1))) >> sh if sh > 0 else im << (-sh)
            if r or i:
                box[(kc, kb)] = (r, i)
                box[(-kc, -kb)] = (r, -i)
        out[mon] = box
    return out


def check(res, N1, N2, Kc, Kb, Lc, xi_c, DJ):
    """float64 cross-check: prod2.py's construction (unnormalised jets) on the same grid; compare the S-box
    coefficients of chi1, chi2 after normalisation by h^m."""
    from prod2 import Prod2
    nu = [float(HM.R(x)) for x in HM.Model().nu]
    mu = float(HM.R(HM.Model().mu))
    pr = Prod2(nu, mu, N1=N1, N2=N2, N=DJ - 1, K1solve=Kc, K2solve=Kb)
    pr.setup(Lc, [xi_c, 0.0], [0.0, 0.0])
    P = pr.f.scale(mu)
    chi1, Rs1 = pr.solve(P)
    G2 = pr.bracket(P - Rs1.scale(0.5), chi1)
    chi2, _ = pr.solve(G2)
    hh = [float(x) for x in H_CELL]
    out = {}
    for name, J, deg in (("chi1", chi1, DJ), ("chi2", chi2, DJ - 1)):
        C = np.fft.rfft2(J.c, axes=(1, 2)) / (N1 * N2)
        worst, scale = 0.0, 0.0
        for t, mon in enumerate(pr.S6.mons[: pr.S6.M(deg)]):
            key = ",".join(map(str, mon))
            hm = np.prod([hh[j] ** e for j, e in enumerate(mon)])
            for kk, (re, im) in res[name].get(key, {}).items():
                kc, kb = map(int, kk.split(","))
                v = complex(re, im) / 2.0 ** res["OUTB"]
                w = C[t][kc % N1, kb] * hm
                worst = max(worst, abs(v - w))
                scale = max(scale, abs(v))
        out[name] = dict(max_abs_diff=worst, max_abs_coef=scale)
    print("float64 cross-check", out, flush=True)
    res["float64_check"] = out


if __name__ == "__main__":
    main()
