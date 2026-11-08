"""Resonant Lie-series normal form of the full planar SJSU perturbation at one slow point (research scratch).

Unperturbed part h0 = H_Kep(Lambda) + DN.(Lambda - Lambda_pt), perturbation f' = f - DN.(Lambda - Lambda_pt)
(Kolmogorov-like split, as in E6 of the research plan), grade 1.  Steps r = 1..N of exp(L_chi_r), L_chi g = {g, chi},
with {h0, chi_r} + H_r = Z_r, i.e. chi_r,k = H_r,k / (i k.n(Lambda)), n = n_Kep(Lambda) + DN, solved exactly as a jet
in dLambda.  Z_r keeps k = 0, the 5:2 family m(2,-5,0) and (mode keep52nr) every three-body harmonic whose divisor
can come within NR_THRESH of zero at osculating Lambda.  Slow dependence: Taylor jets of degree D + 1 - s for grade
s (exact derivatives at the slow point; D = N); fast angles on a (NJ, NS, NU) grid, pair-structured at grade 1.

Poisson bracket {u, v} = sum_q (u_lam v_Lam - u_Lam v_lam) + (u_eta v_xi - u_xi v_eta)  (harmonics.py convention).
The rate of an order-r averaged observable w.Lambda' is sup over the fast torus of |w.d_lambda| of the
non-normalized grade-(r+1) term plus the kept parts (E6's definition).  Everything is float64 and sampled:
measured, not enclosed.
"""
from __future__ import annotations

import math
import time

import numpy as np

import model as M

NR_THRESH = 3.0e-3
# bound on max |Lambda - Lambda'| over the fast torus: 1.1 x the maximum over the 57 sample points of the
# first-order offset scaled to the N-body range (g2_modulation.py; maxima 1.77e-4, 2.26e-4, 3.42e-5)
OSC_HALF = np.array([1.95e-4, 2.5e-4, 3.8e-5])
OBS = {'LJ': (1, 0, 0), 'LS': (0, 1, 0), 'LU': (0, 0, 1), 'F1': (5, 2, 0)}


def kfreq(n):
    return np.round(np.fft.fftfreq(n, 1.0 / n)).astype(int) if n > 1 else np.zeros(1, int)


class Engine:
    def __init__(self, B, NG, slow, dn, divisor='kepler', keep='keep52', verbose=False):
        self.B, self.NG, self.slow = B, tuple(NG), slow
        self.divisor, self.keep, self.verbose = divisor, keep, verbose
        self.dn = np.asarray(dn, float)
        Lam = np.asarray(slow[0], float)
        if divisor == 'kepler':
            self.n0 = M.n_kep(Lam) + self.dn
            self.nk0 = M.n_kep(Lam)
        else:                                   # E6: n = N_NB + HESS (Lambda - Lambda*), at Lambda = Lambda* only
            self.n0 = M.N_NB.copy()
        self.Lam = Lam
        self._kc, self._mask, self._rd = {}, {}, {}
        self.t0 = time.time()
        self.keep_chis = False

    # ------------------------------------------------------------------ Fourier helpers
    def kvecs(self, shape):
        if shape not in self._kc:
            ks = []
            for ax in range(3):
                s = [1, 1, 1]; s[ax] = shape[ax]
                ks.append(kfreq(shape[ax]).reshape(s))
            self._kc[shape] = ks
        return self._kc[shape]

    def masks(self, shape):
        """(kept_all, kept_nr) boolean masks on a Fourier component of this shape."""
        if shape not in self._mask:
            kJ, kS, kU = self.kvecs(shape)
            zero = (kJ == 0) & (kS == 0) & (kU == 0)
            fam52 = (5 * kJ + 2 * kS == 0) & (kU == 0)
            kept = zero if self.keep == 'secular' else (zero | fam52)
            nr = np.zeros(np.broadcast_shapes(kJ.shape, kS.shape, kU.shape), bool)
            if self.keep == 'keep52nr':  # 'keep52': k = 0 and m(2,-5,0); 'secular': k = 0 only
                kn = kJ * self.n0[0] + kS * self.n0[1] + kU * self.n0[2]
                hess = 3 * M.n_kep(self.Lam) / self.Lam
                mod = (np.abs(kJ) * hess[0] * OSC_HALF[0] + np.abs(kS) * hess[1] * OSC_HALF[1]
                       + np.abs(kU) * hess[2] * OSC_HALF[2])
                nr = (np.abs(kn) - mod < NR_THRESH) & ~kept
            kept = np.broadcast_to(kept | nr, nr.shape)
            self._mask[shape] = (kept, nr)
        return self._mask[shape]

    def grid(self, c):
        sz = int(np.prod(c.shape[1:]))
        return np.fft.ifftn(c, axes=(1, 2, 3)).real * sz

    def fourier(self, g):
        sz = int(np.prod(g.shape[1:]))
        return np.fft.fftn(g, axes=(1, 2, 3)) / sz

    # ------------------------------------------------------------------ Fn = {shape: Fourier jet array}
    @staticmethod
    def add(F, G, s=1.0):
        out = {k: v.copy() for k, v in F.items()}
        for k, v in G.items():
            if k in out:
                n = min(out[k].shape[0], v.shape[0])
                out[k] = out[k][:n] + s * v[:n]
            else:
                out[k] = s * v
        return out

    def trunc(self, F, d):
        return {k: v[: self.B.nmon[d]] for k, v in F.items()}

    def split(self, F):
        kept, nonres, nr = {}, {}, {}
        for sh, v in F.items():
            ka, kn = self.masks(sh)
            ka = ka.reshape(sh); kn = np.broadcast_to(kn, sh)
            kept[sh] = np.where(ka, v, 0)
            nonres[sh] = np.where(ka, 0, v)
            nr[sh] = np.where(kn, v, 0)
        return kept, nonres, nr

    def recip_div(self, shape, d):
        """Jet in dLambda of 1/(k.n(Lambda)) on a Fourier component (0 where kept)."""
        key = (shape, d)
        if key not in self._rd:
            B = self.B
            kJ, kS, kU = self.kvecs(shape)
            ks = (kJ, kS, kU)
            kn0 = kJ * self.n0[0] + kS * self.n0[1] + kU * self.n0[2]
            kept, _ = self.masks(shape)
            kept = kept.reshape(shape)
            a0 = np.where(kept, 1.0, kn0 * np.ones(shape))
            Dk = B.const(a0, d)
            for j in range(3):
                for m in range(1, d + 1):
                    mon = [0] * 9; mon[j] = m
                    if self.divisor == 'kepler':
                        c = self.nk0[j] * math.comb(m + 2, 2) * (-1) ** m / self.Lam[j] ** m   # binom(-3, m)
                    else:
                        c = M.HESS_STAR[j] if m == 1 else 0.0
                    Dk[B.idx[tuple(mon)]] += np.where(kept, 0.0, ks[j] * c * np.ones(shape))
            R = B.recip(Dk, d)
            R[:, kept] = 0.0
            self._rd[key] = R
        return self._rd[key]

    def solve(self, nonres, d):
        out = {}
        for sh, v in nonres.items():
            out[sh] = -1j * self.B.mul(v, self.recip_div(sh, d), d)
        return out

    # ------------------------------------------------------------------ brackets
    def grids_of(self, F, d):
        """Grid jets of d_lambda_q F (degree d) and of the slow derivatives of F (degree d), per component."""
        B = self.B
        out = {}
        for sh, c in F.items():
            ks = self.kvecs(sh)
            g = {}
            for q in range(3):
                if sh[q] > 1:
                    g[('lam', q)] = self.grid(1j * ks[q][None] * c[: B.nmon[d]])
            for v in range(9):
                dv = B.deriv(c[: B.nmon[d + 1]], v)
                if B.support(dv).size:
                    g[('d', v)] = self.grid(dv)
            out[sh] = g
        return out

    def bracket(self, GU, GV, d):
        """{U, V} truncated at degree d from precomputed grids (grids_of(., d))."""
        B = self.B
        acc = {}

        def addto(a, b, s):
            if a is None or b is None:
                return
            p = B.mul(a, b, d)
            sh = p.shape[1:]
            if sh in acc:
                acc[sh] += s * p
            else:
                acc[sh] = s * p

        for gu in GU.values():
            for gv in GV.values():
                for q in range(3):
                    addto(gu.get(('lam', q)), gv.get(('d', q)), 1.0)
                    addto(gu.get(('d', q)), gv.get(('lam', q)), -1.0)
                    addto(gu.get(('d', 6 + q)), gv.get(('d', 3 + q)), 1.0)
                    addto(gu.get(('d', 3 + q)), gv.get(('d', 6 + q)), -1.0)
        return {sh: self.fourier(g) for sh, g in acc.items()}

    # ------------------------------------------------------------------ rates
    def rate(self, F, w):
        tot = 0.0
        for sh, c in F.items():
            ks = self.kvecs(sh)
            kw = (w[0] * ks[0] + w[1] * ks[1] + w[2] * ks[2]).reshape(sh)
            tot = tot + self.grid((1j * kw * c[0])[None])[0]
        return float(np.abs(tot).max()) if not np.isscalar(tot) else 0.0

    def log(self, msg):
        if self.verbose:
            print(f'  [{time.time() - self.t0:7.1f}s] {msg}', flush=True)

    # ------------------------------------------------------------------ the normal form
    def run(self, f, N, D=None, rate_obs=('LJ', 'LS', 'LU', 'F1'), graded=None):
        """f: Fn of grade 1 (Fourier jets of degree >= D), or graded = {s: Fn} (grade s of degree >= D + 1 - s).
        Returns per-order rates and the final graded H."""
        D = N if D is None else D
        if graded is None:
            graded = {1: f}
        H = {}
        for s in range(1, N + 2):
            H[s] = self.trunc(graded[s], D + 1 - s) if s in graded else {}
        ladder = []

        def record(r):
            kept_sum, nr_sum = {}, {}
            for s in range(1, r + 1):
                k_, _, n_ = self.split(H[s])
                kept_sum = self.add(kept_sum, k_)
                nr_sum = self.add(nr_sum, n_)
            _, rem, nrl = self.split(H[r + 1])
            row = {'order': r}
            for o in rate_obs:
                w = OBS[o]
                row[o] = {'total': self.rate(self.add(kept_sum, H[r + 1]), w),
                          'remainder': self.rate(rem, w),
                          'floor_nr': self.rate(self.add(nr_sum, nrl), w)}
            ladder.append(row)
            self.log('order %d: %s' % (r, {o: '%.3e' % row[o]['remainder'] for o in rate_obs}))

        record(0)
        self.chis = {}
        for r in range(1, N + 1):
            kept, nonres, _ = self.split(H[r])
            chi = self.solve(nonres, D + 1 - r)
            if self.keep_chis:
                self.chis[r] = chi
            new = {s: dict(H[s]) for s in H}
            new[r] = kept
            Gchi = self.grids_of(chi, D - r)      # derivatives of chi reach degree D - r at most
            # h0 terms: (1/j!) L^{j-1}(-nonres) at grade j r, j >= 2
            T, j = {sh: -v for sh, v in nonres.items()}, 1
            while (j + 1) * r <= N + 1:
                j += 1
                s = j * r
                T = self.bracket(self.grids_of(T, D + 1 - s), self._tr(Gchi, D + 1 - s), D + 1 - s)
                T = {sh: v / j for sh, v in T.items()}
                new[s] = self.add(new[s], T)
            # (1/j!) L^j H[b]
            for b in range(1, N + 1):
                if not H[b] or b + r > N + 1:
                    continue
                T, j = H[b], 0
                while b + (j + 1) * r <= N + 1:
                    j += 1
                    s = b + j * r
                    T = self.bracket(self.grids_of(T, D + 1 - s), self._tr(Gchi, D + 1 - s), D + 1 - s)
                    T = {sh: v / j for sh, v in T.items()}
                    new[s] = self.add(new[s], T)
            H = new
            record(r)
        return ladder, H

    def _tr(self, G, d):
        """Truncate precomputed grid dicts to degree d."""
        n = self.B.nmon[d]
        return {sh: {k: v[:n] for k, v in g.items()} for sh, g in G.items()}


def f_fourier(B, slow, NG, dn, pt_lam):
    """Grade-1 perturbation f' = f - dn.(Lambda - Lambda_pt) as an Fn, and the secular Lambda-gradient of f."""
    P = M.pair_jets(B, slow, NG)
    F = {}
    for (i, j), v in P.items():
        sz = int(np.prod(v.shape[1:]))
        F[v.shape[1:]] = np.fft.fftn(v, axes=(1, 2, 3)) / sz
    grad = np.array([sum(float(c[B.unit[q], 0, 0, 0].real) for c in F.values()) for q in range(3)])
    first = next(iter(F))
    for q in range(3):
        F[first][B.unit[q], 0, 0, 0] -= dn[q]
    return F, grad


def census(B, F, rho, taus, kweight=True):
    """Number of coefficients (k, alpha) of an Fn with |c| rho^alpha max(1, |k|_1) > tau, for each tau; and the
    number of harmonics k carrying at least one such coefficient."""
    w = np.array([np.prod([rho[v] ** e for v, e in enumerate(m)]) for m in B.mons])
    out = {}
    for tau in taus:
        nco, harm = 0, None
        for sh, c in F.items():
            kJ = kfreq(sh[0]).reshape(-1, 1, 1); kS = kfreq(sh[1]).reshape(1, -1, 1); kU = kfreq(sh[2]).reshape(1, 1, -1)
            kw = np.maximum(1, np.abs(kJ) + np.abs(kS) + np.abs(kU)) if kweight else np.ones((1, 1, 1))
            a = np.abs(c) * w[: c.shape[0]].reshape((-1, 1, 1, 1)) * kw[None]
            big = a > tau
            nco += int(big.sum())
            hk = big.any(axis=0)
            harm = (harm or 0) + int(hk.sum())
        out['%.0e' % tau] = {'coefficients': nco, 'harmonics': harm}
    return out
