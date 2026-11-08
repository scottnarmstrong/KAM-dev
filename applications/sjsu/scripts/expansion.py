"""First-order (in the masses) Fourier-Taylor expansion of the planar SJSU perturbation.

For each pair (i, j), i inner, the perturbation is
    f_ij = -G m_i m_j / |r_i - r_j|  +  (r~_i . r~_j)/m0
expanded in the complex Poincare variables z = (xi - i eta)/sqrt(2) of both planets and in the
mean longitudes, to total degree DEG in (z, zbar), trigonometric degree |k| <= KF, and to first
order in the translated actions L = Lambda - Lambda* (SLG13 (b1)-(b3)).

Direct part (alpha = a_i/a_j, t = log(rho_i/rho_j), psi = phi_i - phi_j):
    1/|r_i - r_j| = (1/(a_j rho_j)) sum_k (1/2) b^{(k)}_{1/2}(alpha e^t) e^{i k psi}
                  = (1/(2 a_j)) sum_k e^{ik(lambda_i - lambda_j)}
                      sum_n D^n b^{(k)}/(n! 2^n) sum_m C(n,m) [sigma_i^m e^{ik(phi_i-lambda_i)}]
                                                   [(-sigma_j)^{n-m} e^{-ik(phi_j-lambda_j)}/rho_j]
with D = alpha d/dalpha, sigma = 2 log rho.  Indirect part: r~_j = (Lambda_j/a_j) d/dlambda_j (rho_j e^{i phi_j}).

Output: a sparse 3-planet series (see sparse.py) with L-index 0 (value at Lambda*) and
L-index j+1 (coefficient of L_j, i.e. the Lambda_j-derivative at Lambda*).
"""
from __future__ import annotations

from math import comb, factorial

import mpmath
import numpy as np

from laplace import laplace_derivatives
from sparse import SP


def _tri_index(D):
    """Triangle entries (p, q), p + q <= D, grouped by degree."""
    by_deg = []
    for d in range(D + 1):
        by_deg.append([(p, d - p) for p in range(d + 1)])
    return by_deg


class PairExpander:
    def __init__(self, backend, U, D=18, KF=16):
        self.bk = backend
        self.U = U
        self.D = D
        self.KF = KF
        self.KL = U['KL']
        self.by_deg = _tri_index(D)
        # dense conversion of universal series per degree slice: dict[(m,k)] -> list over d of arrays
        self._A = {key: self._slices(s) for key, s in U['A'].items()}
        self._B = {key: self._slices(s) for key, s in U['B'].items()}
        self._V = self._slices(U['V'])
        self._Vb = self._slices({(q, p): v for (p, q), v in U['V'].items()})

    def _slices(self, series):
        out = []
        for d in range(self.D + 1):
            arr = self.bk.zeros(d + 1)
            for idx, (p, q) in enumerate(self.by_deg[d]):
                c = series.get((p, q))
                if c is not None:
                    arr[idx] = self.bk.real(c)
            out.append(arr)
        return out

    # ------------------------------------------------------------------ direct
    def direct(self, i, j, consts, harm_filter=None):
        """Return SP for -G m_i m_j/|r_i - r_j| with L-derivatives."""
        bk = self.bk
        D, KF, KL = self.D, self.KF, self.KL
        a = consts['a']
        alpha = a[i] / a[j]
        T = laplace_derivatives(alpha, KL, D + 1)
        pref = -consts['m'][i] * consts['m'][j] / a[j]          # -G m_i m_j / a_j, G = 1
        Lam = consts['Lambda']
        s_i = mpmath.sqrt(2 / Lam[i])
        s_j = mpmath.sqrt(2 / Lam[j])
        keys = []
        c0s, cis, cjs = [], [], []
        for k in range(-KL, KL + 1):
            kk = abs(k)
            # quick harmonic reachability: h_i = k + q_i - p_i, h_j = -k + q_j - p_j
            beta = [T[kk][n] / (factorial(n) * 2 ** n) for n in range(D + 1)]
            dbeta = [T[kk][n + 1] / (factorial(n) * 2 ** n) for n in range(D + 1)]
            # Bt_{m} = sum_{n>=m} beta_n C(n,m) (-1)^{n-m} B_{n-m,k}; per degree slice
            Bt = []
            dBt = []
            for m in range(D + 1):
                sl = [bk.zeros(d + 1) for d in range(D + 1)]
                dsl = [bk.zeros(d + 1) for d in range(D + 1)]
                for n in range(m, D + 1):
                    cf = comb(n, m) * (-1) ** (n - m)
                    b = bk.real(beta[n] * cf)
                    db = bk.real(dbeta[n] * cf)
                    Bs = self._B[(n - m, k)]
                    for d in range(n - m, D + 1 - m):
                        sl[d] = sl[d] + b * Bs[d]
                        dsl[d] = dsl[d] + db * Bs[d]
                Bt.append(sl)
                dBt.append(dsl)
            for di in range(D + 1):
                mmax = di  # A_{m,k} has degree >= m
                Ai = np.array([self._A[(m, k)][di] for m in range(mmax + 1)], dtype=bk.dtype)  # (m, ni)
                pi = np.array([p for p, q in self.by_deg[di]])
                qi = np.array([q for p, q in self.by_deg[di]])
                hi = k + qi - pi
                for dj in range(D + 1 - di):
                    pj = np.array([p for p, q in self.by_deg[dj]])
                    qj = np.array([q for p, q in self.by_deg[dj]])
                    hj = -k + qj - pj
                    H_i, H_j = np.meshgrid(hi, hj, indexing='ij')
                    mask = (np.abs(H_i) + np.abs(H_j)) <= KF
                    if harm_filter is not None:
                        mask &= harm_filter(H_i, H_j)
                    if not mask.any():
                        continue
                    Bj = np.array([Bt[m][dj] for m in range(mmax + 1)], dtype=bk.dtype)
                    dBj = np.array([dBt[m][dj] for m in range(mmax + 1)], dtype=bk.dtype)
                    Phi = Ai.T.dot(Bj) * bk.real(mpmath.mpf(1) / 2)
                    DPhi = Ai.T.dot(dBj) * bk.real(mpmath.mpf(1) / 2)
                    scale = pref * s_i ** di * s_j ** dj
                    sc = bk.real(scale)
                    v0 = sc * Phi
                    vi = bk.real(scale / Lam[i]) * (bk.real(2) * DPhi - bk.real(mpmath.mpf(di) / 2) * Phi)
                    vj = bk.real(scale / Lam[j]) * (bk.real(-2) * (DPhi + Phi) - bk.real(mpmath.mpf(dj) / 2) * Phi)
                    II, JJ = np.nonzero(mask)
                    for a_, b_ in zip(II, JJ):
                        keys.append((int(H_i[a_, b_]), int(H_j[a_, b_]), int(pi[a_]), int(qi[a_]), int(pj[b_]), int(qj[b_])))
                    c0s.append(v0[II, JJ])
                    cis.append(vi[II, JJ])
                    cjs.append(vj[II, JJ])
        return self._assemble(i, j, keys, c0s, cis, cjs)

    # ---------------------------------------------------------------- indirect
    def indirect(self, i, j, consts, harm_filter=None):
        """Return SP for (r~_i . r~_j)/m0 with L-derivatives."""
        bk = self.bk
        D, KF = self.D, self.KF
        Lam = consts['Lambda']
        beta, mu, m0 = consts['beta'], consts['mu'], consts['m0']
        # (1/(2 m0)) (Lambda_i/a_i)(Lambda_j/a_j) = (1/(2 m0)) beta_i^2 mu_i beta_j^2 mu_j/(Lambda_i Lambda_j)
        pref = beta[i] ** 2 * mu[i] * beta[j] ** 2 * mu[j] / (2 * m0 * Lam[i] * Lam[j])
        s_i = mpmath.sqrt(2 / Lam[i])
        s_j = mpmath.sqrt(2 / Lam[j])
        keys, c0s, cis, cjs = [], [], [], []
        for (Si, shi), (Sj, shj) in (((self._V, 1), (self._Vb, -1)), ((self._Vb, -1), (self._V, 1))):
            for di in range(D + 1):
                pi = np.array([p for p, q in self.by_deg[di]])
                qi = np.array([q for p, q in self.by_deg[di]])
                hi = shi + qi - pi
                for dj in range(D + 1 - di):
                    pj = np.array([p for p, q in self.by_deg[dj]])
                    qj = np.array([q for p, q in self.by_deg[dj]])
                    hj = shj + qj - pj
                    H_i, H_j = np.meshgrid(hi, hj, indexing='ij')
                    mask = (np.abs(H_i) + np.abs(H_j)) <= KF
                    if harm_filter is not None:
                        mask &= harm_filter(H_i, H_j)
                    if not mask.any():
                        continue
                    prod = np.multiply.outer(Si[di], Sj[dj])
                    scale = pref * s_i ** di * s_j ** dj
                    v0 = bk.real(scale) * prod
                    vi = bk.real(-scale * (1 + mpmath.mpf(di) / 2) / Lam[i]) * prod
                    vj = bk.real(-scale * (1 + mpmath.mpf(dj) / 2) / Lam[j]) * prod
                    II, JJ = np.nonzero(mask)
                    for a_, b_ in zip(II, JJ):
                        keys.append((int(H_i[a_, b_]), int(H_j[a_, b_]), int(pi[a_]), int(qi[a_]), int(pj[b_]), int(qj[b_])))
                    c0s.append(v0[II, JJ])
                    cis.append(vi[II, JJ])
                    cjs.append(vj[II, JJ])
        return self._assemble(i, j, keys, c0s, cis, cjs)

    # ------------------------------------------------------------------ helper
    def _assemble(self, i, j, keys, c0s, cis, cjs):
        bk = self.bk
        if not keys:
            return SP.empty(bk)
        kar = np.array(keys, dtype=np.int16)
        n = len(kar)
        c0 = np.concatenate(c0s)
        ci = np.concatenate(cis)
        cj = np.concatenate(cjs)
        K = np.zeros((n, 3), dtype=np.int16)
        E = np.zeros((n, 6), dtype=np.int16)
        K[:, i] = kar[:, 0]
        K[:, j] = kar[:, 1]
        E[:, 2 * i] = kar[:, 2]
        E[:, 2 * i + 1] = kar[:, 3]
        E[:, 2 * j] = kar[:, 4]
        E[:, 2 * j + 1] = kar[:, 5]
        parts = []
        for lidx, c in ((0, c0), (i + 1, ci), (j + 1, cj)):
            parts.append(SP(bk, K.copy(), E.copy(), np.full(n, lidx, dtype=np.int16), c))
        return SP.concat(bk, parts).consolidate()


def kepler_quadratic(consts):
    """K2(L) = sum_j (1/2) K2pp_j L_j^2 with K2pp_j = -3 n_j/Lambda_j (mpf list)."""
    return consts['K2pp']


def first_order_hamiltonian(bk, U, consts, D=18, KF=16, harm_filter=None, log=print):
    """Sum over pairs of direct + indirect parts, as one consolidated SP."""
    import time
    ex = PairExpander(bk, U, D=D, KF=KF)
    parts = []
    for (i, j) in ((0, 1), (0, 2), (1, 2)):
        t0 = time.time()
        d = ex.direct(i, j, consts, harm_filter=harm_filter)
        t1 = time.time()
        ind = ex.indirect(i, j, consts, harm_filter=harm_filter)
        t2 = time.time()
        log(f'  pair ({i+1},{j+1}): direct {len(d)} terms {t1-t0:.1f}s, indirect {len(ind)} terms {t2-t1:.1f}s')
        parts += [d, ind]
    return SP.concat(bk, parts).consolidate()
