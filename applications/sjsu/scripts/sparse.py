"""Sparse Fourier-Taylor series in the 3-planet Poincare variables, with Poisson brackets.

A term is  C * L^{(l)} * exp(i K.lambda) * prod_j z_j^{E[2j]} zbar_j^{E[2j+1]},
where l = 0 means no action factor and l = j+1 means one factor L_j (series are at most
linear in L, SLG13 (b1)).  Coefficients live in a numeric back end (sjsu_common.Backend).

Poisson bracket (coordinates lambda_j, eta_j; momenta L_j, xi_j; z = (xi - i eta)/sqrt 2):
    {f, g} = sum_j (f_{lambda_j} g_{L_j} - f_{L_j} g_{lambda_j})
             - i sum_j (f_{z_j} g_{zbar_j} - f_{zbar_j} g_{z_j}).
"""
from __future__ import annotations

import numpy as np

_KOFF = 64


def _encode(K, E, L):
    key = L.astype(np.int64)
    mult = 4
    for c in range(3):
        key = key + mult * (K[:, c].astype(np.int64) + _KOFF)
        mult *= 128
    for c in range(6):
        key = key + mult * E[:, c].astype(np.int64)
        mult *= 32
    return key


class SP:
    __slots__ = ('bk', 'K', 'E', 'L', 'C')

    def __init__(self, bk, K, E, L, C):
        self.bk = bk
        self.K = np.asarray(K, dtype=np.int16).reshape(-1, 3)
        self.E = np.asarray(E, dtype=np.int16).reshape(-1, 6)
        self.L = np.asarray(L, dtype=np.int16).reshape(-1)
        self.C = C

    # ------------------------------------------------------------ construction
    @staticmethod
    def empty(bk):
        return SP(bk, np.zeros((0, 3)), np.zeros((0, 6)), np.zeros(0), bk.zeros(0))

    @staticmethod
    def concat(bk, parts):
        parts = [p for p in parts if len(p)]
        if not parts:
            return SP.empty(bk)
        return SP(bk, np.concatenate([p.K for p in parts]), np.concatenate([p.E for p in parts]),
                  np.concatenate([p.L for p in parts]), np.concatenate([p.C for p in parts]))

    def __len__(self):
        return len(self.L)

    def copy(self):
        return SP(self.bk, self.K.copy(), self.E.copy(), self.L.copy(), self.C.copy())

    def select(self, mask):
        return SP(self.bk, self.K[mask], self.E[mask], self.L[mask], self.C[mask])

    def scaled(self, c):
        return SP(self.bk, self.K, self.E, self.L, self.C * c)

    def consolidate(self, drop_zero=True):
        if len(self) == 0:
            return self
        key = _encode(self.K, self.E, self.L)
        order = np.argsort(key, kind='stable')
        ks = key[order]
        uniq, idx = np.unique(ks, return_index=True)
        C = np.add.reduceat(self.C[order], idx)
        first = order[idx]
        out = SP(self.bk, self.K[first], self.E[first], self.L[first], C)
        if drop_zero:
            nz = np.array([c != 0 for c in C], dtype=bool) if self.bk.name == 'mp' else (C != 0)
            out = out.select(nz)
        return out

    def __add__(self, other):
        return SP.concat(self.bk, [self, other]).consolidate()

    def __sub__(self, other):
        return SP.concat(self.bk, [self, other.scaled(self.bk.real(-1))]).consolidate()

    # ---------------------------------------------------------------- queries
    def degree(self):
        return self.E.sum(axis=1)

    def knorm(self):
        return np.abs(self.K).sum(axis=1)

    def is_secular(self):
        return (self.K == 0).all(axis=1)

    def average(self):
        return self.select(self.is_secular())

    def harmonic_groups(self):
        """dict harmonic tuple -> index array."""
        if len(self) == 0:
            return {}
        code = ((self.K[:, 0].astype(np.int64) + _KOFF) * 128 + (self.K[:, 1] + _KOFF)) * 128 + (self.K[:, 2] + _KOFF)
        order = np.argsort(code, kind='stable')
        cs = code[order]
        uniq, idx = np.unique(cs, return_index=True)
        bounds = list(idx) + [len(cs)]
        out = {}
        for u in range(len(uniq)):
            ii = order[bounds[u]:bounds[u + 1]]
            out[tuple(int(x) for x in self.K[ii[0]])] = ii
        return out

    def to_dict(self):
        return {(int(l), tuple(int(x) for x in k), tuple(int(x) for x in e)): c
                for k, e, l, c in zip(self.K, self.E, self.L, self.C)}

    # ------------------------------------------------------------- operations
    def kdotn(self, nvec):
        """Backend array of K . n for numeric frequencies nvec (3 backend reals)."""
        bk = self.bk
        if bk.name == 'mp':
            return np.array([int(k[0]) * nvec[0] + int(k[1]) * nvec[1] + int(k[2]) * nvec[2] for k in self.K],
                            dtype=object)
        return (self.K[:, 0] * nvec[0] + self.K[:, 1] * nvec[1] + self.K[:, 2] * nvec[2])

    def homological(self, nvec):
        """X with n . d_lambda X + self = 0 (self must have no K = 0 term): X_k = i c_k / (k.n)."""
        assert not self.is_secular().any()
        kn = self.kdotn(nvec)
        I = self.bk.cplx(0, 1)
        return SP(self.bk, self.K, self.E, self.L, I * self.C / kn)

    def bracket_K2(self, K2pp):
        """{X, K2} for X with L = 0 only, K2 = sum_j (1/2) K2pp_j L_j^2.  Result: L-linear."""
        bk = self.bk
        assert (self.L == 0).all()
        parts = []
        I = bk.cplx(0, 1)
        for j in range(3):
            m = self.K[:, j] != 0
            if not m.any():
                continue
            kj = self.K[m, j]
            if bk.name == 'mp':
                fac = np.array([I * int(x) * K2pp[j] for x in kj], dtype=object)
            else:
                fac = I * kj * K2pp[j]
            parts.append(SP(bk, self.K[m], self.E[m], np.full(m.sum(), j + 1), self.C[m] * fac))
        return SP.concat(bk, parts).consolidate()


def bracket(A: SP, B: SP, targets=None, maxdeg=18, maxL=1, Lmask=None):
    """{A, B} truncated to total degree <= maxdeg, L-degree <= maxL.

    targets: None (all result harmonics) or an iterable of harmonic tuples to keep.
    Lmask: optional set of result L-indices to keep (e.g. {0} for L = 0).
    """
    bk = A.bk
    I = bk.cplx(0, 1)
    gA = A.harmonic_groups()
    gB = B.harmonic_groups()
    if targets is not None:
        targets = [tuple(t) for t in targets]
    degA = A.degree()
    degB = B.degree()
    out = []
    for kA, ia in gA.items():
        if targets is None:
            pairs = [(kB, ib) for kB, ib in gB.items()]
        else:
            pairs = []
            for t in targets:
                kB = (t[0] - kA[0], t[1] - kA[1], t[2] - kA[2])
                if kB in gB:
                    pairs.append((kB, gB[kB]))
        if not pairs:
            continue
        cA = A.C[ia]
        EA = A.E[ia].astype(np.int16)
        LA = A.L[ia]
        dA = degA[ia]
        for kB, ib in pairs:
            kres = (kA[0] + kB[0], kA[1] + kB[1], kA[2] + kB[2])
            # cheap degree prefilter
            dB = degB[ib]
            dmin_xe = dA[:, None] + dB[None, :] - 2
            if (dmin_xe > maxdeg).all():
                continue
            cB = B.C[ib]
            EB = B.E[ib].astype(np.int16)
            LB = B.L[ib]
            prod = np.multiply.outer(cA, cB)
            Esum = EA[:, None, :] + EB[None, :, :]
            dsum = dA[:, None] + dB[None, :]
            LAm = np.broadcast_to(LA[:, None], prod.shape)
            LBm = np.broadcast_to(LB[None, :], prod.shape)
            # ---- (L, lambda) part
            # term1: d_lambda_j A * d_L_j B: j = LB-1, factor i kA_j, result L = LA
            kA_arr = np.array(kA, dtype=np.int64)
            kB_arr = np.array(kB, dtype=np.int64)
            f1 = np.where(LB > 0, kA_arr[np.maximum(LB - 1, 0)], 0)  # per column
            m1 = (f1[None, :] != 0) & (dsum <= maxdeg) & np.ones(prod.shape, dtype=bool)
            if maxL < 1:
                m1 &= (LAm == 0)
            if Lmask is not None:
                m1 &= np.isin(LAm, list(Lmask))
            if m1.any():
                r, c = np.nonzero(m1)
                fac = f1[c]
                coef = prod[r, c] * _int_factor(bk, fac, I)
                out.append(SP(bk, np.tile(kres, (len(r), 1)), Esum[r, c], LA[r], coef))
            # term2: - d_L_j A * d_lambda_j B: j = LA-1, factor -i kB_j, result L = LB
            f2 = np.where(LA > 0, kB_arr[np.maximum(LA - 1, 0)], 0)  # per row
            m2 = (f2[:, None] != 0) & (dsum <= maxdeg)
            if maxL < 1:
                m2 &= (LBm == 0)
            if Lmask is not None:
                m2 &= np.isin(LBm, list(Lmask))
            if m2.any():
                r, c = np.nonzero(m2)
                fac = -f2[r]
                coef = prod[r, c] * _int_factor(bk, fac, I)
                out.append(SP(bk, np.tile(kres, (len(r), 1)), Esum[r, c], LB[c], coef))
            # ---- (z, zbar) part: -i (pA qB - qA pB) z^{EA+EB - e_p - e_q}
            Lres = LAm + LBm  # valid only when at most one is nonzero
            both = (LAm > 0) & (LBm > 0)
            base = (dsum - 2 <= maxdeg)
            if maxL < 1:
                base &= (Lres == 0)
            base &= ~both if maxL <= 1 else np.ones_like(base)
            if Lmask is not None:
                base &= np.isin(Lres, list(Lmask))
            if not base.any():
                continue
            for j in range(3):
                pA = EA[:, 2 * j].astype(np.int64)
                qA = EA[:, 2 * j + 1].astype(np.int64)
                pB = EB[:, 2 * j].astype(np.int64)
                qB = EB[:, 2 * j + 1].astype(np.int64)
                fac = pA[:, None] * qB[None, :] - qA[:, None] * pB[None, :]
                m3 = base & (fac != 0)
                if not m3.any():
                    continue
                r, c = np.nonzero(m3)
                Er = Esum[r, c].copy()
                Er[:, 2 * j] -= 1
                Er[:, 2 * j + 1] -= 1
                coef = prod[r, c] * _int_factor(bk, -fac[r, c], I)
                out.append(SP(bk, np.tile(kres, (len(r), 1)), Er, Lres[r, c], coef))
    return SP.concat(bk, out).consolidate()


def _int_factor(bk, ints, I):
    """Backend array I * ints (ints: integer numpy array)."""
    if bk.name == 'mp':
        return np.array([I * int(x) for x in ints], dtype=object)
    return I * ints.astype(bk.rdtype)
