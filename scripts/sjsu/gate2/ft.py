"""Fourier-Taylor series in action deviations p = (p1, p2, p3) and rotation-invariant angles (numpy).

A function is f(p, q) = sum_{m, k} c[m, k] p^m e^{i k.q} with k = (k1, k2, -k1 - k2), so it depends
on q only through phi1 = q1 - q3, phi2 = q2 - q3. Coefficients are stored as an array
c[m, a, b] (m: index of the p-monomial, (a, b): FFT layout of (k1, k2) on a G x G grid).
Fourier support is truncated to the hexagon |k|_1 = |k1| + |k2| + |k1 + k2| <= K; products are
taken on the grid, which is alias-free on that hexagon when G > 3K/2.

Poisson structure of SJSU18-O2 in modal polar variables w_j = sqrt(I_j) e^{i q_j}, I_j = I*_j + p_j:
{w_j, wbar_j} = -i means {q_j, p_j} = -1, so
  {f, g} = -sum_j (d_{q_j} f d_{p_j} g - d_{p_j} f d_{q_j} g)
         = -(f_phi1 D1 g + f_phi2 D2 g - D1 f g_phi1 - D2 f g_phi2),  D1 = d_p1 - d_p3, D2 = d_p2 - d_p3.
"""
from __future__ import annotations

import math
import os
from concurrent.futures import ThreadPoolExecutor

import numpy as np

# numpy releases the GIL in einsum: FT_THREADS=6 gives ~2.4x on the bracket kernel (default 1)
THREADS = int(os.environ.get('FT_THREADS', '1'))


def monomials(L):
    out = []
    for d in range(L + 1):
        for a in range(d, -1, -1):
            for b in range(d - a, -1, -1):
                out.append((a, b, d - a - b))
    return out


def gbinom(alpha, l):
    """Generalized binomial coefficient binom(alpha, l), alpha real (vectorized over alpha)."""
    out = np.ones_like(np.asarray(alpha, dtype=float))
    for i in range(l):
        out = out * (alpha - i) / (i + 1)
    return out


class Space:
    def __init__(self, L, K, G=None):
        self.L, self.K = L, K
        if G is None:
            G = int(math.ceil(1.5 * K)) + 2
            G += G % 2
        self.G = G
        self.mons = monomials(L)
        self.M = len(self.mons)
        self.idx = {m: i for i, m in enumerate(self.mons)}
        self.deg = np.array([sum(m) for m in self.mons])
        k = np.rint(np.fft.fftfreq(G, 1.0 / G)).astype(int)
        self.K1, self.K2 = np.meshgrid(k, k, indexing='ij')
        self.K3 = -self.K1 - self.K2
        self.kabs = np.abs(self.K1) + np.abs(self.K2) + np.abs(self.K3)
        self.mask = (self.kabs <= K).astype(float)
        self.k0 = (self.kabs == 0)
        # product table grouped by left monomial: for i, (js, targets)
        self.groups = []
        for i, mi in enumerate(self.mons):
            js, ts = [], []
            for j, mj in enumerate(self.mons):
                if sum(mi) + sum(mj) <= L:
                    js.append(j)
                    ts.append(self.idx[(mi[0] + mj[0], mi[1] + mj[1], mi[2] + mj[2])])
            self.groups.append((i, np.array(js), np.array(ts)))
        # d/dp_j maps: (d f)[dst] = fac * f[src]
        self.dp = []
        for j in range(3):
            src, dst, fac = [], [], []
            for i, m in enumerate(self.mons):
                if m[j] > 0:
                    mm = list(m)
                    mm[j] -= 1
                    src.append(i)
                    dst.append(self.idx[tuple(mm)])
                    fac.append(m[j])
            self.dp.append((np.array(src), np.array(dst), np.array(fac, dtype=float)))

    # ---- construction / conversion
    def zeros(self):
        return np.zeros((self.M, self.G, self.G), dtype=complex)

    def var(self, j, shift=0.0):
        """The function p_j (+ shift)."""
        f = self.zeros()
        e = [0, 0, 0]
        e[j] = 1
        f[self.idx[tuple(e)], 0, 0] = 1.0
        f[0, 0, 0] += shift
        return f

    def embed(self, f, other):
        """Re-express f (array of Space `other`) in this space (truncating or zero-padding)."""
        g = self.zeros()
        Ko = other.K
        sel = other.kabs <= min(Ko, self.K)
        k1, k2 = other.K1[sel], other.K2[sel]
        for i, m in enumerate(other.mons):
            if sum(m) > self.L:
                continue
            g[self.idx[m], k1 % self.G, k2 % self.G] = f[i][sel]
        return g

    def trunc(self, f):
        return f * self.mask

    # ---- grid transforms (values on phi-grid <-> coefficients)
    def to_grid(self, f):
        return np.fft.ifft2(f, axes=(-2, -1)) * (self.G * self.G)

    def from_grid(self, v):
        return np.fft.fft2(v, axes=(-2, -1)) / (self.G * self.G)

    # ---- calculus
    def d_p(self, f, j):
        src, dst, fac = self.dp[j]
        g = self.zeros()
        g[dst] = f[src] * fac[:, None, None]
        return g

    def d_phi(self, f, a):
        K = self.K1 if a == 0 else self.K2
        return f * (1j * K)

    def mul(self, f, g):
        fv, gv = self.to_grid(f), self.to_grid(g)
        out = np.zeros_like(fv)
        for i, js, ts in self.groups:
            out[ts] += fv[i][None] * gv[js]
        return self.trunc(self.from_grid(out))

    def bracket(self, f, g):
        D1f = self.d_p(f, 0) - self.d_p(f, 2)
        D2f = self.d_p(f, 1) - self.d_p(f, 2)
        D1g = self.d_p(g, 0) - self.d_p(g, 2)
        D2g = self.d_p(g, 1) - self.d_p(g, 2)
        A = self.to_grid(np.stack([self.d_phi(f, 0), self.d_phi(f, 1), D1f, D2f]))
        B = self.to_grid(np.stack([D1g, D2g, -self.d_phi(g, 0), -self.d_phi(g, 1)]))
        nt = THREADS

        def work(part):
            out = np.zeros((self.M, self.G, self.G), dtype=complex)
            for i, js, ts in self.groups[part::nt]:
                out[ts] += np.einsum('sxy,sjxy->jxy', A[:, i], B[:, js])
            return out
        if nt > 1:
            with ThreadPoolExecutor(nt) as ex:
                out = sum(ex.map(work, range(nt)))
        else:
            out = work(0)
        return self.trunc(-self.from_grid(out))

    def lie(self, f, chi, sign=1.0, rho=None, rtol=1e-20, nmax=80):
        """exp(sign L_chi) f, L_chi f = {f, chi}; stops when a term's majorant falls below rtol."""
        total = f.copy()
        term = f
        ref = self.norm(f, rho) or 1.0
        for n in range(1, nmax):
            term = self.bracket(term, chi) * (sign / n)
            total += term
            if self.norm(term, rho) < rtol * ref:
                return total
        raise RuntimeError('Lie series did not converge')

    # ---- sizes
    def weights(self, rho):
        rho = np.asarray(rho, dtype=float)
        return np.array([rho[0] ** m[0] * rho[1] ** m[1] * rho[2] ** m[2] for m in self.mons])

    def norm(self, f, rho=None):
        """Majorant sum |c| rho^m (sup bound on the real torus times polydisk |p_j| <= rho_j)."""
        if rho is None:
            rho = [1e-5, 1e-5, 1e-5]
        w = self.weights(rho)
        return float(np.sum(np.abs(f).sum(axis=(1, 2)) * w))

    def norm_by_degree(self, f, rho):
        w = self.weights(rho)
        s = np.abs(f).sum(axis=(1, 2)) * w
        return np.array([s[self.deg == d].sum() for d in range(self.L + 1)])

    def angle_part(self, f, degs):
        g = f.copy()
        keep = np.isin(self.deg, list(degs))
        g[~keep] = 0
        g[:, self.k0] = 0
        return g

    def omega(self, f):
        return np.array([f[self.idx[e], 0, 0].real for e in [(1, 0, 0), (0, 1, 0), (0, 0, 1)]])

    def homological(self, f, omega, degs):
        """chi with {omega.p, chi} + (angle part of f in p-degrees degs) = 0: chi = i f / (k.omega)."""
        d = self.K1 * (omega[0] - omega[2]) + self.K2 * (omega[1] - omega[2])
        g = self.angle_part(f, degs) * self.mask
        dd = np.where(self.k0, 1.0, d)
        chi = 1j * g / dd[None]
        chi[:, self.k0] = 0
        return chi, float(np.min(np.abs(d[(~self.k0) & (self.mask > 0)])))

    # ---- evaluation
    def eval(self, f, p, phi):
        """f at one point (p in R^3, phi = (phi1, phi2))."""
        e = np.exp(1j * (self.K1 * phi[0] + self.K2 * phi[1]))
        vals = np.tensordot(f, e, axes=([1, 2], [0, 1]))
        pm = np.array([p[0] ** m[0] * p[1] ** m[1] * p[2] ** m[2] for m in self.mons])
        return complex(np.sum(vals * pm))


def from_modal_poly(S, terms, Istar):
    """Fourier-Taylor expansion about I* of sum c w^a wbar^b (terms: list of ((a0,a1,a2,b0,b1,b2), c)).

    w_j^a wbar_j^b = (I*_j + p_j)^{(a+b)/2} e^{i (a-b) q_j}; the binomial series is truncated at
    total p-degree S.L. Requires a rotation-invariant polynomial (sum of k_j = 0).
    """
    E = np.array([t[0] for t in terms])
    c = np.array([t[1] for t in terms], dtype=complex)
    n = E[:, :3] + E[:, 3:]
    k = E[:, :3] - E[:, 3:]
    assert np.all(k.sum(axis=1) == 0), 'not rotation invariant'
    alpha = n / 2.0
    f = S.zeros()
    a_idx = k[:, 0] % S.G
    b_idx = k[:, 1] % S.G
    inside = (np.abs(k).sum(axis=1) <= S.K)
    assert inside.all(), 'Fourier cutoff too small for the polynomial'
    Is = np.asarray(Istar, dtype=float)
    for mi, m in enumerate(S.mons):
        coef = c.copy()
        for j in range(3):
            coef = coef * gbinom(alpha[:, j], m[j]) * Is[j] ** (alpha[:, j] - m[j])
        np.add.at(f[mi], (a_idx, b_idx), coef)
    return f


def binom_tail_majorant(terms, Istar, rho, L, lmax=200):
    """Majorant of the omitted p-degree > L part of the expansion of sum c w^a wbar^b on |p_j| <= rho_j.

    For each term, the one-variable sequences s_j[l] = |binom(alpha_j, l)| I*^{alpha_j - l} rho_j^l are
    convolved by total degree and summed over total degree > L (lmax terms per variable).
    """
    total = 0.0
    Is = np.asarray(Istar, dtype=float)
    rho = np.asarray(rho, dtype=float)
    cache = {}
    for e, c in terms:
        key = tuple(int(x + y) for x, y in zip(e[:3], e[3:]))
        if key not in cache:
            seqs = []
            for j in range(3):
                al = key[j] / 2.0
                s = np.empty(lmax + 1)
                b = 1.0
                for l in range(lmax + 1):
                    s[l] = abs(b) * Is[j] ** (al - l) * rho[j] ** l
                    b = b * (al - l) / (l + 1)
                seqs.append(s)
            conv = np.convolve(np.convolve(seqs[0], seqs[1]), seqs[2])
            cache[key] = float(conv[L + 1:].sum())
        total += abs(c) * cache[key]
    return total
