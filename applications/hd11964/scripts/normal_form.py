#!/usr/bin/env python3
"""HD11964-PILOT: fast-angle Lie normal form with slow variables, and its residual against the ORIGINAL Hamiltonian.

Untrusted design tooling (Apache-2.0).  numpy only.

Coordinates: LP's chart w = (lam_j, xi_j; Lam_j, eta_j), j = 0 (HD 11964 c), 1 (HD 11964 b); canonical pairs (lam, Lam),
(xi, eta); {A, B} = sum_j A_lam B_Lam - A_Lam B_lam + A_xi B_eta - A_eta B_xi; dA/dt = {A, H}.
H o Psi = h(Lam) + mu f o Psi exactly (lpChart_hamiltonian), h = -sum nu^3/(2 Lam^2), omega_j = nu_j^3/Lam_j^3.

At a centre (Lam*, xi*, eta*) every function is a jet: Taylor in u = (dLam_0, dLam_1, dxi_0, deta_0, dxi_1, deta_1) to
degree D, values on an N1 x N2 grid of the fast angles.  The Lie series (one generator per order of mu, Kepler
frequencies omega(Lam* + dLam) in the divisors, every Fourier mode of the 2/3-filter box solved) gives generators
chi_1..chi_N and the approximate integrals

    F_i = exp(L_{-chi_1}) ... exp(L_{-chi_N}) Lam_i   truncated at order mu^N,     L_chi G = {G, chi}.

`residual` evaluates {F_i, H o Psi} at u = 0 on the whole fast-angle grid with the EXACT gradient of H o Psi (automatic
differentiation of the chart and of the Newtonian f, not the Fourier model), so it measures the true dF_i/dt, including
the unsolved Fourier tail, aliasing and Taylor truncation.  With D = N + 1 the value and gradient of F at u = 0 are exact
truncations.  Everything is sampled (label `estimated`).
"""
import math

import numpy as np

from jets import Jet, Space, embed, mul

TP = 2 * math.pi


# ---- the chart in jet arithmetic ---------------------------------------------------------------------------
def kepler_scalar(v0, v1, lam, iters=60):
    F = lam + v0 * np.sin(lam) - v1 * np.cos(lam)
    for _ in range(iters):
        g = F - v0 * np.sin(F) + v1 * np.cos(F) - lam
        dg = 1 - v0 * np.cos(F) - v1 * np.sin(F)
        st = g / dg
        F = F - st
        if np.max(np.abs(st)) < 8 * np.finfo(np.asarray(st).dtype).eps:
            break
    return F


def chart_planet(S, nu, lam_grid, Lam0, xi0, eta0, vL, vx, ve, vlam=None):
    """Jets of q, p (two components each) of one planet; variables vL, vx, ve (and vlam) of space S."""
    gs = lam_grid.shape
    Lam = Jet.var(S, vL, Lam0, gs)
    xi = Jet.var(S, vx, xi0, gs)
    eta = Jet.var(S, ve, eta0, gs)
    lam = Jet.var(S, vlam, lam_grid, gs) if vlam is not None else Jet.const(S, lam_grid, gs)
    G = (xi * xi + eta * eta).scale(0.5)
    K = 1.0 - G / Lam
    be = ((1.0 - G / Lam.scale(2.0)) / Lam).sqrt()
    v0, v1 = be * xi, be * eta
    F = Jet.const(S, kepler_scalar(v0.at0(), v1.at0(), lam_grid), gs)
    for _ in range(int(math.ceil(math.log2(S.D + 1))) + 1):
        sn, cs = F.sincos()
        g = F - v0 * sn + v1 * cs - lam
        dg = 1.0 - v0 * cs - v1 * sn
        F = F - g / dg
    sn, cs = F.sincos()
    u0, u1 = cs, sn
    Jk = 1.0 - v0 * u0 - v1 * u1
    vu = (v0 * u0 + v1 * u1) / (1.0 + K)
    s = (Lam * Lam).scale(1.0 / nu ** 2)
    q0 = s * (K * u0 - v0 + vu * v0)
    q1 = s * (K * u1 - v1 + vu * v1)
    c = (Lam * Jk).recip().scale(nu ** 2)
    p0 = c * (vu * v1 - u1)
    p1 = c * (u0 - vu * v0)
    return (q0, q1), (p0, p1)


def disturbing(nu, Q, P):
    """f = |p_0 + p_1|^2/2 - nu_0 nu_1/|q_0 - q_1| on jets."""
    Px, Py = P[0][0] + P[1][0], P[0][1] + P[1][1]
    dx, dy = Q[0][0] - Q[1][0], Q[0][1] - Q[1][1]
    r2 = dx * dx + dy * dy
    return (Px * Px + Py * Py).scale(0.5) - r2.sqrt().recip().scale(nu[0] * nu[1])


# ---- the normal form ---------------------------------------------------------------------------------------
class NormalForm:
    def __init__(self, nu, mu, N1=256, N2=64, N=3, Ksolve=None, K1solve=None, K2solve=None, long=False):
        """long=True: 80-bit long double throughout, with explicit DFT matrices (numpy's FFT is double only)."""
        self.long = long
        self.ft = np.longdouble if long else np.float64
        self.nu, self.mu = np.asarray(nu, self.ft), self.ft(mu)
        self.N1, self.N2, self.N = N1, N2, N
        self.D = N + 1
        self.S6 = Space(6, self.D)
        self.S3 = Space(3, self.D)
        tp = 2 * np.arccos(self.ft(-1))
        self.lam1 = tp * np.arange(N1, dtype=self.ft) / N1
        self.lam2 = tp * np.arange(N2, dtype=self.ft) / N2
        self.grid = (N1, N2)
        k1 = np.fft.fftfreq(N1, 1.0 / N1)
        k2 = np.fft.fftfreq(N2, 1.0 / N2) if long else np.fft.rfftfreq(N2, 1.0 / N2)
        self.k1, self.k2 = np.meshgrid(k1, k2, indexing="ij")
        self.filt = (np.abs(self.k1) <= N1 // 3) & (np.abs(self.k2) <= N2 // 3)
        sol = self.filt & ((self.k1 != 0) | (self.k2 != 0))
        if Ksolve is not None:
            sol &= (np.abs(self.k1) + np.abs(self.k2)) <= Ksolve
        if K1solve is not None:
            sol &= np.abs(self.k1) <= K1solve
        if K2solve is not None:
            sol &= np.abs(self.k2) <= K2solve
        self.solved = sol
        self.Lmask = np.array([m[2] == m[3] == m[4] == m[5] == 0 for m in self.S6.mons])
        if long:
            ct = np.clongdouble
            j1 = np.arange(N1, dtype=self.ft)
            j2 = np.arange(N2, dtype=self.ft)
            self.W1 = np.exp(ct(-1j) * np.outer(np.fft.fftfreq(N1, 1.0 / N1).astype(self.ft), j1) * (tp / N1))
            self.W2 = np.exp(ct(-1j) * np.outer(np.fft.fftfreq(N2, 1.0 / N2).astype(self.ft), j2) * (tp / N2))
            self.V1 = np.conj(self.W1).T / N1
            self.V2 = np.conj(self.W2).T / N2
        self.k1 = self.k1.astype(self.ft)
        self.k2 = self.k2.astype(self.ft)

    # spectral helpers on jets of shape (M, N1, N2)
    def fft(self, A):
        if self.long:
            return np.einsum('ka,mab,lb->mkl', self.W1, A.c, self.W2)
        return np.fft.rfft2(A.c, axes=(1, 2))

    def ifft(self, Ch, deg):
        if self.long:
            return Jet(self.S6, np.real(np.einsum('ak,mkl,bl->mab', self.V1, Ch, self.V2)), deg)
        return Jet(self.S6, np.fft.irfft2(Ch, s=self.grid, axes=(1, 2)), deg)

    def filter(self, A):
        return self.ifft(self.fft(A) * self.filt, A.deg)

    def dlam(self, A):
        Ch = self.fft(A)
        return self.ifft(Ch * (1j * self.k1), A.deg), self.ifft(Ch * (1j * self.k2), A.deg)

    def bracket(self, A, B):
        """{A, B} with the 2/3 filter applied to the result."""
        Al = self.dlam(A)
        Bl = self.dlam(B)
        out = None
        for j in range(2):
            t = mul(Al[j], B.d(j)) - mul(A.d(j), Bl[j])
            out = t if out is None else out + t
            xj, ej = 2 + 2 * j, 3 + 2 * j
            out = out + mul(A.d(xj), B.d(ej)) - mul(A.d(ej), B.d(xj))
        return self.filter(out)

    # centre-dependent data
    def setup(self, Lam0, xi0, eta0):
        self.Lam0 = np.asarray(Lam0, self.ft)
        self.xi0 = np.asarray(xi0, self.ft)
        self.eta0 = np.asarray(eta0, self.ft)
        D, S6 = self.D, self.S6
        # omega_j(Lam0 + dLam_j) Taylor coefficients (exact binomial series)
        self.om_coef = []
        for j in range(2):
            c = [self.nu[j] ** 3 / self.Lam0[j] ** 3]
            for m in range(1, D + 1):
                c.append(c[-1] * (-(3 + m - 1)) / (m * self.Lam0[j]))
            self.om_coef.append(c)
        # s(k, dLam) = k1 omega_0 + k2 omega_1 on the mode grid, as a jet in dLam; then 1/s
        mg = self.k1.shape
        sc = np.zeros((S6.M(D),) + mg, dtype=self.ft)
        for j, kk in ((0, self.k1), (1, self.k2)):
            for m in range(D + 1):
                e = [0] * 6
                e[j] = m
                sc[S6.idx[tuple(e)]] += kk * self.om_coef[j][m]
        safe = np.where(self.solved, sc[0], 1.0)
        sc[0] = safe
        self.inv = Jet(S6, sc, D).recip()
        # the 1-d planet charts and f
        Q, P = [], []
        for j, lg, ax in ((0, self.lam1, 0), (1, self.lam2, 1)):
            q, p = chart_planet(self.S3, self.nu[j], lg, self.Lam0[j], self.xi0[j], self.eta0[j], 0, 1, 2)
            vm = [j, 2 + 2 * j, 3 + 2 * j]
            Q.append(tuple(embed(x, S6, vm, (ax,), self.grid) for x in q))
            P.append(tuple(embed(x, S6, vm, (ax,), self.grid) for x in p))
        self.f = disturbing(self.nu, Q, P)
        self.exact_grad()

    def exact_grad(self):
        """Exact gradient of f o Psi at u = 0 on the grid, in all 8 chart directions (degree-1 AD)."""
        S8 = Space(8, 1)
        S4 = Space(4, 1)
        Q, P = [], []
        for j, lg, ax in ((0, self.lam1, 0), (1, self.lam2, 1)):
            q, p = chart_planet(S4, self.nu[j], lg, self.Lam0[j], self.xi0[j], self.eta0[j], 1, 2, 3, vlam=0)
            vm = [6 + j, j, 2 + 2 * j, 3 + 2 * j]
            Q.append(tuple(embed(x, S8, vm, (ax,), self.grid) for x in q))
            P.append(tuple(embed(x, S8, vm, (ax,), self.grid) for x in p))
        f8 = disturbing(self.nu, Q, P)
        g = f8.grad0()
        # order: dLam0, dLam1, xi0, eta0, xi1, eta1, lam0, lam1
        self.fg = dict(Lam=(g[0], g[1]), xi=(g[2], g[4]), eta=(g[3], g[5]), lam=(g[6], g[7]))
        self.f0 = f8.at0()

    def solve(self, R):
        """chi with omega(Lam).d_lam chi = solved part of R; returns chi and the solved part R_s."""
        Rh = self.fft(R)
        d = R.deg
        inv = self.inv.trunc(d)
        sel = self.solved[None]
        Rr = Jet(self.S6, Rh.real * sel, d)
        Ri = Jet(self.S6, Rh.imag * sel, d)
        # chi_k = R_k / (i s_k) = -i R_k / s_k
        cr = mul(Rr, inv, bmask_key="L", bmask=self.Lmask)
        ci = mul(Ri, inv, bmask_key="L", bmask=self.Lmask)
        Chih = ci.c - 1j * cr.c
        chi = self.ifft(Chih, d)
        Rs = self.ifft(Rh * sel, d)
        return chi, Rs

    def run(self):
        """Generators chi_1..chi_N and the approximate integrals F^(N') for N' = 0..N (as G = F - Lam per order)."""
        N, mu = self.N, self.mu
        H = {1: self.filter(self.f).scale(mu)}  # orders >= 1; h (order 0) is handled through its brackets
        chis = []
        for j in range(1, N + 1):
            R = H.get(j)
            chi, Rs = self.solve(R)
            chis.append(chi)
            new = dict(H)
            # exp(L_chi)(h + sum H[k]):  L_chi h = {h, chi} = -omega.d_lam chi = -Rs
            new[j] = new[j] - Rs
            # higher powers on h: L_chi^m h / m! = -L_chi^{m-1} Rs / m!
            t, m = Rs, 1
            while (m + 1) * j <= N:
                m += 1
                t = self.bracket(t, chi)
                new[m * j] = new.get(m * j, 0) + t.scale(-1.0 / math.factorial(m)) if m * j in new else \
                    t.scale(-1.0 / math.factorial(m))
            for k, Hk in H.items():
                t, m = Hk, 0
                while k + (m + 1) * j <= N:
                    m += 1
                    t = self.bracket(t, chi)
                    o = k + m * j
                    add = t.scale(1.0 / math.factorial(m))
                    new[o] = new[o] + add if o in new else add
            H = new
        self.chis = chis
        self.Hnf = H
        out = {}
        for Np in range(0, N + 1):
            Gs = []
            for i in range(2):
                A = {0: Jet.var(self.S6, i, self.Lam0[i], self.grid)}
                for j in range(Np, 0, -1):
                    chi = chis[j - 1]
                    new = dict(A)
                    for k, Ak in A.items():
                        t, m = Ak, 0
                        while k + (m + 1) * j <= Np:
                            m += 1
                            t = self.bracket(t, chi)
                            o = k + m * j
                            add = t.scale((-1.0) ** m / math.factorial(m))
                            new[o] = new[o] + add if o in new else add
                    A = new
                G = None
                for k, Ak in A.items():
                    if k >= 1:
                        G = Ak if G is None else G + Ak
                Gs.append(G)
            out[Np] = Gs
        self.G = out
        return out

    def residual(self, Np):
        """{F_i, H o Psi} at u = 0 on the grid, exact gradient of H; returns per planet (rate grid, G grid)."""
        mu = self.mu
        fg = self.fg
        om = [self.om_coef[0][0], self.om_coef[1][0]]
        res = []
        for i in range(2):
            G = self.G[Np][i]
            lead = -mu * fg["lam"][i]
            if G is None:
                res.append((lead, np.zeros(self.grid)))
                continue
            Gl = self.dlam(G.trunc(1))
            g0 = G.at0()
            gr = G.grad0()
            # {G, h + mu f}
            fast = om[0] * Gl[0].at0() + om[1] * Gl[1].at0()
            pert = 0.0
            for j in range(2):
                pert = pert + Gl[j].at0() * fg["Lam"][j] - gr[j] * fg["lam"][j]
                pert = pert + gr[2 + 2 * j] * fg["eta"][j] - gr[3 + 2 * j] * fg["xi"][j]
            res.append(((lead + fast) + mu * pert, g0))
        return res
