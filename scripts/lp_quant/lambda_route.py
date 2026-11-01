#!/usr/bin/env python3
"""LP-QUANT: the Lambda-only route.  Untrusted design tooling.

Claim being costed.  L is exactly conserved (LP Lemma 3), so C(t) - C(0) = sum_i (Lambda_i(t) - Lambda_i(0)) exactly.  Hence a
certified bound |Lambda(t) - Lambda(0)|_inf <= r up to time T, with r inside the budget of geometry.budgets, gives through LP0
(Lemma 5, C <= B(I) - m) no orbit crossing up to T, whatever eccentricities and inclinations do.  The certificate must
hold on the AMD ball sum Gamma <= C0 + n r: nothing is assumed about the slow variables.

 scan(...)      FFT of the pair and one-planet terms of f on sampled points of the ball; gives
                  eta0 = mu sup |d_lam f|                           (Gronwall: T0 = r/eta0)
                  amp1 = mu sup |d_i chi|                           (size of the first-order correction, the true oscillation)
                  G    = bound for {d_i chi, f}, product of sups    (first-order rate eta1 = mu^2 G + rate of unsolved modes)
                  theta= per-order gain (Chirikov/Lie number)
                  shells of |k|_inf |f_k| by |k|_1                   (the tail: which K must be resolved)
 fast_lie(...)  an actual Lie normal form in the fast angles of one pair, slow variables frozen, grid = Chebyshev in the
                actions x Fourier in the angles: eta_q at orders q = 0..Q.  Validates the extrapolation by theta.
 resonance_table(...) nearest resonances, distance to them in action, pendulum widths.
 nbody_check(...)     a short direct integration of (1): the AMD identity, the true oscillation of Lambda.
All sups are sampled: label `estimated`.
"""
import math
import os
import sys
import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import geometry as G
import chart as Ch
import divisors as Dv

TP = 2 * math.pi


def _freq(N):
    return np.fft.fftfreq(N, 1.0 / N)


def domega(ctx):
    """omega_i'(I_i) = -3 nu_i^3 / I_i^4 (radian frequencies; h is separable)."""
    return -3 * ctx.nu ** 3 / ctx.I0 ** 4


def pair_coeffs(ctx, i, j, I, zi, zj, N):
    """Fourier coefficients of f_ij = p_i.p_j - nu_i nu_j/|q_i-q_j| at given actions and slow points."""
    qi, pi = Ch.single_planet_arrays(ctx.nu[i], I[i], zi, N)
    qj, pj = Ch.single_planet_arrays(ctx.nu[j], I[j], zj, N)
    return np.fft.fft2(Ch.pair_grid(ctx.nu[i], ctx.nu[j], qi, pi, qj, pj)) / N ** 2


def self_coeffs(ctx, i, I, zi, N):
    qi, pi = Ch.single_planet_arrays(ctx.nu[i], I[i], zi, N)
    return np.fft.fft(Ch.self_grid(pi)) / N


def _sum_sup(c):
    """sup over the torus of |sum c_k e^{ik.lam}|, from a grid (2D or 1D coefficient array)."""
    if c.ndim == 2:
        return float(np.max(np.abs(np.fft.ifft2(c) * c.size)))
    return float(np.max(np.abs(np.fft.ifft(c) * c.size)))


def scan(ctx, r, Cball=None, N=256, J=40, seed=2, Ksolve=None, h=1e-5):
    """Rates on the tube |Lambda - I0| <= r, slow points on the AMD ball.  Modes whose divisor vanishes on the tube (or with
    |k|_1 > Ksolve) stay unsolved; they contribute mu |k_i f_k| to the first-order rate.  Returns a dict of numbers."""
    n, m = ctx.n, ctx.m
    Cball = ctx.C0 + n * r if Cball is None else Cball
    rng = np.random.default_rng(seed)
    zs = Ch._real_slow(rng, J, n, m, ctx.I0, Cball)
    nz = np.sqrt(np.maximum(np.sum(zs * zs, axis=1, keepdims=True), 1e-300))
    zs[: J // 2] = zs[: J // 2] / nz[: J // 2] * math.sqrt(2 * Cball)  # half on the sphere (max principle for f_k)
    w = ctx.omega
    wp = domega(ctx)
    f = _freq(N)
    k1, k2 = np.meshgrid(f, f, indexing="ij")
    Kcut = Ksolve or int(N / 3)
    res = dict(sup_dlam=0.0, sup_dlam_i=np.zeros(n), amp1=np.zeros(n), unsolved=0.0)
    # A[i][coordinate], B[coordinate]; coordinates per planet j: 0 lam, 1 Lambda, 2.. slow
    nc = 2 + 2 * m
    Asup = np.zeros((n, n, nc))
    Bsup = np.zeros((n, nc))
    shells = np.zeros(4 * N)
    sub = lambda c: None
    for t in range(J):
        z = zs[t]
        zp = [z[2 * m * i: 2 * m * (i + 1)] for i in range(n)]
        I = ctx.I0.copy()
        A = np.zeros((n, n, nc))
        Bc = np.zeros((n, nc))
        dl = np.zeros(n)
        am = np.zeros(n)
        uns = np.zeros(n)
        for a in range(n):
            # one-planet term: modes k e_a
            c = self_coeffs(ctx, a, I, zp[a], N)
            c0 = c.copy()
            c0[0] = 0
            div = f * w[a]
            ok = np.abs(f) > 0
            dk = np.abs(div) - np.abs(f * wp[a]) * r
            good = ok & (dk > 0) & (np.abs(f) <= Kcut)
            chi = np.where(good, c0 / (1j * np.where(good, div, 1.0)), 0)
            dl[a] += _sum_sup(1j * f * c0)
            am[a] += _sum_sup(1j * f * chi)
            uns[a] += float(np.sum(np.abs(f * c0)[~good]))
            Bc[a, 0] += _sum_sup(1j * f * c0)
            A[a, a, 0] += _sum_sup(-f * f * chi)
            # derivatives in the action and slow coordinates by central differences
            for cn in range(1, nc):
                Ip, Im, zpp, zmm = I.copy(), I.copy(), list(zp[a]), list(zp[a])
                if cn == 1:
                    Ip[a] += h
                    Im[a] -= h
                else:
                    zpp[cn - 2] += h
                    zmm[cn - 2] -= h
                dc = (self_coeffs(ctx, a, Ip, np.array(zpp), N) - self_coeffs(ctx, a, Im, np.array(zmm), N)) / (2 * h)
                dc0 = dc.copy()
                Bc[a, cn] += _sum_sup(dc0)
                dc0[0] = 0
                dchi = np.where(good, dc0 / (1j * np.where(good, div, 1.0)), 0)
                if cn == 1:  # d(c/(i d)) = dc/(i d) - c k omega'/(i d^2)
                    dchi = dchi - np.where(good, c0 * f * wp[a] / (1j * np.where(good, div, 1.0) ** 2), 0)
                A[a, a, cn] += _sum_sup(1j * f * dchi)
            for b in range(a + 1, n):
                c = pair_coeffs(ctx, a, b, I, zp[a], zp[b], N)
                c0 = c.copy()
                c0[0, 0] = 0
                div = k1 * w[a] + k2 * w[b]
                dk = np.abs(div) - (np.abs(k1 * wp[a]) + np.abs(k2 * wp[b])) * r
                norm1 = np.abs(k1) + np.abs(k2)
                good = (norm1 > 0) & (dk > 0) & (norm1 <= Kcut)
                sdiv = np.where(good, div, 1.0)
                chi = np.where(good, c0 / (1j * sdiv), 0)
                for p, kp in ((a, k1), (b, k2)):
                    dl[p] += _sum_sup(1j * kp * c0)
                    am[p] += _sum_sup(1j * kp * chi)
                    uns[p] += float(np.sum(np.abs(kp * c0)[~good]))
                    Bc[p, 0] += _sum_sup(1j * kp * c0)
                    # second angle derivatives of chi
                    A[a, p, 0] += _sum_sup(-k1 * kp * chi)
                    A[b, p, 0] += _sum_sup(-k2 * kp * chi)
                np.add.at(shells, norm1.astype(int).ravel(), (np.maximum(np.abs(k1), np.abs(k2)) * np.abs(c0)).ravel())
                for p, kp in ((a, k1), (b, k2)):
                    for cn in range(1, nc):
                        Ip, Im = I.copy(), I.copy()
                        z1p, z1m = [list(zp[a]), list(zp[b])], [list(zp[a]), list(zp[b])]
                        if cn == 1:
                            Ip[p] += h
                            Im[p] -= h
                        else:
                            sl = 0 if p == a else 1
                            z1p[sl][cn - 2] += h
                            z1m[sl][cn - 2] -= h
                        dc = (pair_coeffs(ctx, a, b, Ip, np.array(z1p[0]), np.array(z1p[1]), N)
                              - pair_coeffs(ctx, a, b, Im, np.array(z1m[0]), np.array(z1m[1]), N)) / (2 * h)
                        Bc[p, cn] += _sum_sup(dc)
                        dc[0, 0] = 0
                        dchi = np.where(good, dc / (1j * sdiv), 0)
                        if cn == 1:  # the double small divisor: d_Lambda_p 1/(k.omega) = -k_p omega_p'/(k.omega)^2
                            dchi = dchi - np.where(good, c0 * kp * wp[p] / (1j * sdiv ** 2), 0)
                        A[a, p, cn] += _sum_sup(1j * k1 * dchi)
                        A[b, p, cn] += _sum_sup(1j * k2 * dchi)
        res["sup_dlam"] = max(res["sup_dlam"], float(np.max(dl)))
        res["sup_dlam_i"] = np.maximum(res["sup_dlam_i"], dl)
        res["amp1"] = np.maximum(res["amp1"], am)
        res["unsolved"] = max(res["unsolved"], float(np.max(uns)))
        Asup = np.maximum(Asup, A)
        Bsup = np.maximum(Bsup, Bc)
    # {d_i chi, f} <= sum_j [A(lam_j) B(Lam_j) + A(Lam_j) B(lam_j) + slow conjugates]
    Gi = np.zeros(n)
    parts = np.zeros((n, 3))
    for i in range(n):
        for j in range(n):
            parts[i, 0] += Asup[i, j, 0] * Bsup[j, 1]
            parts[i, 1] += Asup[i, j, 1] * Bsup[j, 0]
            for c in range(m):
                parts[i, 2] += Asup[i, j, 2 + 2 * c] * Bsup[j, 3 + 2 * c] + Asup[i, j, 3 + 2 * c] * Bsup[j, 2 + 2 * c]
    Gi = parts.sum(axis=1)
    res.update(Gi=Gi, parts=parts, Asup=Asup, Bsup=Bsup, shells=shells / J, Cball=Cball, r=r)
    return res


def rates(ctx, sc, mu):
    """eta0, eta1, per-order number theta, oscillation amplitude at mass mu."""
    eta0 = mu * sc["sup_dlam"]
    eta1 = mu * mu * float(np.max(sc["Gi"])) + mu * sc["unsolved"]
    amp = mu * float(np.max(sc["amp1"]))
    return dict(eta0=eta0, eta1=eta1, amp=amp, theta=eta1 / eta0)


def resonance_table(ctx, sc_shell=None, K=40, mu=None):
    """Record divisors up to order K: k, |k.omega|, action distance d_k = |k.omega|/sum|k_i omega_i'|."""
    out = []
    wp = np.abs(domega(ctx))
    for nn, k, v in Dv.nearest_resonances(ctx.omega, K, top=6):
        ka = np.abs(np.array(k, float))
        out.append(dict(order=nn, k=k, div=v, dist=v / float(ka @ wp), period_yr=TP / v * ctx.sys.years_per_unit))
    return out


# ---------- Lie normal form in the fast angles of one pair ---------------------------------------------------------------
class TaylorAlg:
    """Truncated Taylor series in (d1, d2), degree <= deg, with coefficients arrays on the (N, N) angle grid."""

    def __init__(self, deg):
        self.deg = deg
        self.mon = [(a, b) for t in range(deg + 1) for a in range(t, -1, -1) for b in [t - a]]
        self.idx = {m: i for i, m in enumerate(self.mon)}
        self.M = len(self.mon)
        self.prod = [(i, j, self.idx[(a + c, b + d)]) for i, (a, b) in enumerate(self.mon)
                     for j, (c, d) in enumerate(self.mon) if a + b + c + d <= deg]

    def mul(self, A, B):
        out = np.zeros_like(A)
        for i, j, k in self.prod:
            out[k] += A[i] * B[j]
        return out

    def dact(self, A, c):
        out = np.zeros_like(A)
        for i, (a, b) in enumerate(self.mon):
            if c == 0 and a > 0:
                out[self.idx[(a - 1, b)]] += a * A[i]
            if c == 1 and b > 0:
                out[self.idx[(a, b - 1)]] += b * A[i]
        return out


def taylor_of_pair(ctx, i, j, zi, zj, N, deg, Rc=None):
    """Taylor coefficients in (d1, d2) of f on the angle grid, by Cauchy's formula on a pair of complex circles: accurate
    to rounding/Rc^deg, no finite-difference noise."""
    nu = ctx.nu
    Rc = Rc or 0.05 * min(ctx.I0[i], ctx.I0[j])
    nt = 2 * (deg + 2)
    th = TP * np.arange(nt) / nt
    circ = np.exp(1j * th)
    vals = np.zeros((nt, nt, N, N), dtype=complex)
    A1 = [Ch.single_planet_arrays(nu[i], ctx.I0[i] + Rc * c, zi, N) for c in circ]
    A2 = [Ch.single_planet_arrays(nu[j], ctx.I0[j] + Rc * c, zj, N) for c in circ]
    for a in range(nt):
        qi, pi = A1[a]
        spi = 0.5 * np.sum(pi * pi, axis=-1)
        for b in range(nt):
            qj, pj = A2[b]
            dq = qi[:, None, :] - qj[None, :, :]
            r = np.sqrt(np.sum(dq * dq, axis=-1))
            vals[a, b] = np.sum(pi[:, None, :] * pj[None, :, :], axis=-1) - nu[i] * nu[j] / r + spi[:, None] \
                + 0.5 * np.sum(pj * pj, axis=-1)[None, :]
    C = np.fft.fft2(vals, axes=(0, 1)) / nt ** 2
    return C, Rc


def fast_lie(ctx, i, j, zi, zj, Q=4, N=96, shift=None):
    """Lie normal form of the pair (i,j), slow variables frozen, all other planets removed:
         H(d, lam) = h(L0 + d) + mu f(L0 + d, lam),
    Taylor in d (degree Q+2), Fourier in lam, exact frequencies omega(L0 + d) in the divisors.  One generator per order of mu.
    Returns g_q = sup_lam |d_lam H_q(0, lam)|, q = 1..Q+1: after q-1 normalization steps the action rate at d = 0 is
    eta_{q-1}(mu) = mu^q g_q.  This is a series in mu at a point: it measures the true cost of the small divisors with
    the actual coefficients, no norms.  The slow coupling is absent, see `scan` parts for its relative size."""
    deg = Q + 2
    Tg = TaylorAlg(deg)
    nu = ctx.nu
    C, Rc = taylor_of_pair(ctx, i, j, zi, zj, N, deg)
    F = np.zeros((Tg.M, N, N))
    for t, (a, b) in enumerate(Tg.mon):
        F[t] = np.real(C[a, b]) / Rc ** (a + b)
    k = _freq(N)
    k1, k2 = np.meshgrid(k, k, indexing="ij")
    filt = (np.abs(k1) <= N / 3) & (np.abs(k2) <= N / 3)
    # h and omega Taylor series
    L1, L2 = float(ctx.I0[i]), float(ctx.I0[j])
    ser_w = np.zeros((Tg.M, N, N))  # k.omega(L0+d) is built mode-wise below

    def binom_series(nu3, L, power):
        """Taylor coefficients in d of nu3 / (L + d)^power, up to deg."""
        out = [nu3 / L ** power]
        for m in range(1, deg + 1):
            out.append(out[-1] * (-(power + m - 1)) / (m * L))
        return out

    w1 = binom_series(nu[i] ** 3, L1, 3)
    w2 = binom_series(nu[j] ** 3, L2, 3)
    if shift is not None:
        w1[0] += shift[0]
        w2[0] += shift[1]
    h1 = binom_series(-nu[i] ** 3 / 2, L1, 2)
    h2 = binom_series(-nu[j] ** 3 / 2, L2, 2)
    H0 = np.zeros(Tg.M)
    for t, (a, b) in enumerate(Tg.mon):
        if b == 0:
            H0[t] += h1[a]
        if a == 0:
            H0[t] += h2[b]
    S = np.zeros((Tg.M,) + k1.shape)  # k.omega(L0 + d)
    for t, (a, b) in enumerate(Tg.mon):
        if b == 0:
            S[t] += k1 * w1[a]
        if a == 0:
            S[t] += k2 * w2[b]
    d0 = np.where(np.abs(S[0]) > 0, S[0], 1.0)
    Inv = np.zeros_like(S)
    Inv[0] = 1 / d0
    order = [Tg.idx[m] for m in Tg.mon]
    for t, (a, b) in enumerate(Tg.mon):
        if t == 0:
            continue
        acc = np.zeros_like(d0)
        for u, (c, e) in enumerate(Tg.mon):
            if u == 0 or c > a or e > b:
                continue
            acc = acc + S[u] * Inv[Tg.idx[(a - c, b - e)]]
        Inv[t] = -acc / d0

    def dang(A, c):
        kk = k1 if c == 0 else k2
        return np.real(np.fft.ifft2(1j * kk * filt * np.fft.fft2(A, axes=(1, 2)), axes=(1, 2)))

    def pb(A, B):
        s = 0.0
        for c in (0, 1):
            s = s + Tg.mul(dang(A, c), Tg.dact(B, c)) - Tg.mul(Tg.dact(A, c), dang(B, c))
        return s

    def solve(Fn):
        """omega.d_lam chi = Fn - <Fn>."""
        Fh = np.fft.fft2(Fn, axes=(1, 2)) * filt
        avg = np.real(Fh[:, 0, 0]) / N ** 2
        Fh[:, 0, 0] = 0
        Ch_ = np.zeros_like(Fh)
        for u, v, w in Tg.prod:
            Ch_[w] += Fh[u] * Inv[v]
        return np.real(np.fft.ifft2(Ch_ / 1j, axes=(1, 2))), avg

    H = [np.zeros_like(F) for _ in range(Q + 2)]
    H[1] = F.copy()
    out = {1: float(np.max(np.maximum(np.abs(dang(H[1], 0)[0]), np.abs(dang(H[1], 1)[0]))))}
    avg_full = np.zeros_like(F)
    for q in range(1, Q + 1):
        chi, avg = solve(H[q])
        osc = H[q].copy()
        osc[:, :, :] -= avg[:, None, None]
        new = [h.copy() for h in H]
        new[q] = new[q] - osc  # the exact homological cancellation {h, chi} = -(H_q - <H_q>)
        for m0 in range(1, Q + 2):
            term = H[m0]
            fac, jj = 1.0, 0
            while m0 + (jj + 1) * q <= Q + 1:
                jj += 1
                term = pb(term, chi)
                fac /= jj
                new[m0 + jj * q] = new[m0 + jj * q] + fac * term
        term = -osc
        fac, jj = 1.0, 1
        while (jj + 1) * q <= Q + 1:
            jj += 1
            term = pb(term, chi)
            fac /= jj
            new[jj * q] = new[jj * q] + fac * term
        H = new
        out[q + 1] = float(np.max(np.maximum(np.abs(dang(H[q + 1], 0)[0]), np.abs(dang(H[q + 1], 1)[0]))))
    return out


def fast_newton(ctx, i, j, zi, zj, mu, steps=6, N=96, deg=12):
    """Numerical (fixed mu) Newton-type normal form of the pair model: H = h + R, h = h_Kepler + mu <f> (fast average), R oscillating.
    Each step solves omega(d).d_lam chi = R_S with the CURRENT frequencies on a set S of modes, composes with exp(L_chi), and moves
    the new average into h.

    Staging.  A mode k is solved only if its resonance lies outside the displacement of the current generator:
        |k.omega| >= 3 A sum_i |k_i| |omega_i'|,   A = max_i Sum_{k in S} |k_i R_k| / |k.omega|.
    Without this rule the first step fails when the displacement of the big low-order harmonics exceeds the distance to a near
    resonance (it does at the calibrated SJS: A ~ 2e-3, distance to 5:2 ~ 8e-4): the Taylor series of 1/(k.omega(d)) is then
    used beyond its radius.  With it the big harmonics go first and the near-resonant ones afterwards.

    Returns rho_t = sup_lam |d_lam R_t(0, lam)|, t = 0..steps, the frequency at d = 0 after each step, and |S| per step.
    Taylor degree `deg` is ample for about 5 steps.  Label `estimated`, pointwise in (action, slow), no slow coupling."""
    Tg = TaylorAlg(deg)
    nu = ctx.nu
    C, Rc = taylor_of_pair(ctx, i, j, zi, zj, N, deg, Rc=0.08 * min(ctx.I0[i], ctx.I0[j]))
    F = np.zeros((Tg.M, N, N))
    for t, (a, b) in enumerate(Tg.mon):
        F[t] = np.real(C[a, b]) / Rc ** (a + b)
    k = _freq(N)
    k1, k2 = np.meshgrid(k, k, indexing="ij")
    filt = (np.abs(k1) <= N / 3) & (np.abs(k2) <= N / 3)
    L1, L2 = float(ctx.I0[i]), float(ctx.I0[j])

    def binom_series(c, L, power):
        out = [c / L ** power]
        for m in range(1, deg + 1):
            out.append(out[-1] * (-(power + m - 1)) / (m * L))
        return out

    h1 = binom_series(-nu[i] ** 3 / 2, L1, 2)
    h2 = binom_series(-nu[j] ** 3 / 2, L2, 2)
    h = np.zeros(Tg.M)
    for t, (a, b) in enumerate(Tg.mon):
        if b == 0:
            h[t] += h1[a]
        if a == 0:
            h[t] += h2[b]

    def split(A):
        Ah = np.fft.fft2(A, axes=(1, 2)) * filt
        avg = np.real(Ah[:, 0, 0]) / N ** 2
        Ah[:, 0, 0] = 0
        return avg, np.real(np.fft.ifft2(Ah, axes=(1, 2)))

    def dang(A, c):
        kk = k1 if c == 0 else k2
        return np.real(np.fft.ifft2(1j * kk * filt * np.fft.fft2(A, axes=(1, 2)), axes=(1, 2)))

    def pb(A, B):
        s = 0.0
        for c in (0, 1):
            s = s + Tg.mul(dang(A, c), Tg.dact(B, c)) - Tg.mul(Tg.dact(A, c), dang(B, c))
        return s

    def dh(hc, c):
        out = np.zeros(Tg.M)
        for t, (a, b) in enumerate(Tg.mon):
            if c == 0 and a > 0:
                out[Tg.idx[(a - 1, b)]] += a * hc[t]
            if c == 1 and b > 0:
                out[Tg.idx[(a, b - 1)]] += b * hc[t]
        return out

    def rate(R):
        return float(max(np.max(np.abs(dang(R, 0)[0])), np.max(np.abs(dang(R, 1)[0]))))

    avg, R = split(mu * F)
    h = h + avg
    rhos = [rate(R)]
    freqs = [(dh(h, 0)[0], dh(h, 1)[0])]
    nsolved = []
    wp1 = 3 * nu[i] ** 3 / L1 ** 4
    wp2 = 3 * nu[j] ** 3 / L2 ** 4
    for t in range(steps):
        w1, w2 = dh(h, 0), dh(h, 1)
        S = k1[None] * w1[:, None, None] + k2[None] * w2[:, None, None]
        d0 = np.where(np.abs(S[0]) > 0, S[0], 1.0)
        Rh = np.fft.fft2(R, axes=(1, 2)) * filt
        Rh[:, 0, 0] = 0
        ab = np.abs(Rh[0]) / N ** 2
        ell = np.abs(k1) * wp1 + np.abs(k2) * wp2
        sel = filt & (ab > 0)
        for _ in range(4):
            A = max(float(np.sum((np.abs(k1) * ab / np.abs(d0))[sel])), float(np.sum((np.abs(k2) * ab / np.abs(d0))[sel])))
            sel = filt & (ab > 0) & (np.abs(d0) >= 3 * A * ell)
        nsolved.append(int(np.sum(sel)))
        Rh = Rh * sel
        Inv = np.zeros_like(S)
        Inv[0] = 1 / d0
        for u, (a, b) in enumerate(Tg.mon):
            if u == 0:
                continue
            acc = np.zeros_like(d0)
            for v, (c, e) in enumerate(Tg.mon):
                if v == 0 or c > a or e > b:
                    continue
                acc = acc + S[v] * Inv[Tg.idx[(a - c, b - e)]]
            Inv[u] = -acc / d0
        Chih = np.zeros_like(Rh)
        for u, v, w in Tg.prod:
            Chih[w] += Rh[u] * Inv[v]
        chi = np.real(np.fft.ifft2(Chih / 1j, axes=(1, 2)))
        Rs = np.real(np.fft.ifft2(Rh, axes=(1, 2)))  # the solved part: {h, chi} = -Rs
        # exp(L_chi)(h + R) = h + (R - Rs) + sum_{j>=1} [ad^j (R)/j! - ad^j (Rs)/(j+1)!]
        new = R - Rs
        tR, tS = R, Rs
        fR, fS = 1.0, 1.0
        for jj in range(1, 4 if t < 2 else 3):
            tR, tS = pb(tR, chi), pb(tS, chi)
            fR /= jj
            fS /= jj + 1
            new = new + fR * tR - fS * tS
        avg, R = split(new)
        h = h + avg
        rhos.append(rate(R))
        freqs.append((dh(h, 0)[0], dh(h, 1)[0]))
    return dict(rho=rhos, freq=freqs, nsolved=nsolved)


def tail_profile(ctx, Cball, N=768, J=10, seed=9):
    """Shells: S[K] = sup_J Sum_{|k|_1 = K} |k|_inf |f_k| over all pairs, K <= N/3 (sampled on the ball sphere)."""
    n, m = ctx.n, ctx.m
    rng = np.random.default_rng(seed)
    zs = Ch._real_slow(rng, J, n, m, ctx.I0, Cball)
    zs = zs / np.sqrt(np.maximum(np.sum(zs * zs, axis=1, keepdims=True), 1e-300)) * math.sqrt(2 * Cball)
    f = _freq(N)
    k1, k2 = np.meshgrid(f, f, indexing="ij")
    norm1 = (np.abs(k1) + np.abs(k2)).astype(int).ravel()
    w = np.maximum(np.abs(k1), np.abs(k2)).ravel()
    out = np.zeros(int(N / 3) + 1)
    for t in range(J):
        z = zs[t]
        zp = [z[2 * m * i: 2 * m * (i + 1)] for i in range(n)]
        sh = np.zeros(2 * N + 1)
        for a in range(n):
            for b in range(a + 1, n):
                c = pair_coeffs(ctx, a, b, ctx.I0, zp[a], zp[b], N)
                sh += np.bincount(norm1, weights=np.abs(c).ravel() * w, minlength=2 * N + 1)
        out = np.maximum(out, sh[: len(out)])
    return out.tolist()


def K_tail(tail, mu, eta):
    """Smallest K with mu Sum_{K' > K} S[K'] <= eta, extrapolating the last shells geometrically; the rounding floor of the
    FFT (about 1e-15 |f|) is removed by fitting on shells above that floor."""
    S = np.array(tail)
    good = np.nonzero(S > 1e-12 * S.max())[0]
    last = int(good[-1])
    lo = max(1, last - 40)
    slope = np.polyfit(np.arange(lo, last + 1), np.log(np.maximum(S[lo: last + 1], 1e-300)), 1)
    S2 = np.concatenate([S[: last + 1], np.exp(slope[1] + slope[0] * np.arange(last + 1, 4000))])
    cum = np.cumsum(S2[::-1])[::-1]
    idx = np.nonzero(mu * cum <= eta)[0]
    return int(idx[0]) if len(idx) else None


def res_free_tube(ctx, K, omega=None):
    """Smallest action distance to a resonance among pair modes with |k|_1 <= K: min |k.omega| / sum |k_i omega_i'|.
    `omega` overrides ctx.omega (used for the O(mu)-shifted frequencies, which are the ones the normal-form action sees)."""
    if K is None:
        return dict(dist=None, k=None)
    wp = np.abs(domega(ctx))
    om = ctx.omega if omega is None else omega
    best, arg = math.inf, None
    for a in range(ctx.n):
        for b in range(a + 1, ctx.n):
            ks = np.arange(-K, K + 1)
            k1, k2 = np.meshgrid(ks, ks, indexing="ij")
            sel = (np.abs(k1) + np.abs(k2) <= K) & ((k1 != 0) | (k2 != 0))
            d = np.abs(k1 * om[a] + k2 * om[b])
            den = np.abs(k1) * wp[a] + np.abs(k2) * wp[b]
            v = np.where(sel, d / np.where(den > 0, den, 1.0), np.inf)
            i = int(np.argmin(v))
            if v.ravel()[i] < best:
                ij = np.unravel_index(i, v.shape)
                best, arg = float(v[ij]), (a, b, int(k1[ij]), int(k2[ij]))
    return dict(dist=best, k=arg)


def closure(ctx, tail, mu, T, rgrid=None, omega=None):
    """Self-consistent fast-averaging tube for horizon T: the largest r such that all pair modes that matter at rate r/T (those
    with |k|_1 <= K_tail) have no resonance inside the tube, r <= dist(K_tail)/2.  Modes beyond K_tail are simply
    bounded in the rate.  Returns r, K, rate.  Near 5:2 this is what fixes the tube, not the AMD budget."""
    rgrid = np.logspace(-2, -9, 141) if rgrid is None else rgrid
    for r in rgrid:
        eta = r / T
        K = K_tail(tail, mu, eta)
        if K is None or K > 1500:
            continue
        rn = res_free_tube(ctx, K, omega)
        if rn["dist"] is not None and r <= 0.5 * rn["dist"]:
            return dict(r=float(r), K=K, eta=float(eta), limiting_k=rn["k"], dist=rn["dist"])
    return None


def secular_rate(ctx, mu, N=128, h=2e-3):
    """Estimated largest secular frequency at the AMD ball's centre: mu sup |d^2 <f>/dx^2| per slow coordinate."""
    n, m = ctx.n, ctx.m
    I = ctx.I0

    def mean(p, shift):
        tot = 0.0
        for b in range(n):
            if b == p:
                continue
            zs = [np.zeros(2 * m) for _ in range(n)]
            zs[p][0] = shift
            i, j = min(p, b), max(p, b)
            c = pair_coeffs(ctx, i, j, I, zs[i], zs[j], N)
            tot += c[0, 0].real
        return tot

    g = max(abs(mean(p, h) - 2 * mean(p, 0.0) + mean(p, -h)) / h ** 2 for p in range(n))
    return float(mu * g)


# ---------- Direct integration --------------------------------------------------------------------------------------
def nbody_check(s, years=20000.0, dt=0.4, seed=4):
    """RK4 of (1) from Kepler elements with random phases: verifies the AMD identity (13) and measures the actual excursion of
    Lambda.  dt in time units.  Returns extrema of the actions and the residual of the identity."""
    n = s.n
    nu, mu = s.nu, s.mu
    rng = np.random.default_rng(seed)
    I = s.I0.copy()
    Gam = I * (1 - np.sqrt(1 - s.e ** 2))
    th = rng.uniform(0, TP, n)
    x, y = np.sqrt(2 * Gam) * np.cos(th), np.sqrt(2 * Gam) * np.sin(th)
    lam = rng.uniform(0, TP, n)
    q, p, _, _ = Ch.chart_planar(nu, I + 0j, lam + 0j, x + 0j, y + 0j)
    q, p = q.real, p.real

    def field(q, p):
        Ps = p.sum(axis=0)
        dq = p / nu[:, None] + mu * Ps
        r3 = np.sum(q * q, axis=1) ** 1.5
        dp = -(nu / r3)[:, None] * q
        for i in range(n):
            for j in range(i + 1, n):
                d = q[i] - q[j]
                r3p = (d @ d) ** 1.5
                fo = mu * nu[i] * nu[j] * d / r3p
                dp[i] -= fo
                dp[j] += fo
        return dq, dp

    def elements(q, p):
        v = p / nu[:, None]
        E = 0.5 * np.sum(v * v, axis=1) - 1 / np.sqrt(np.sum(q * q, axis=1))
        a = -1 / (2 * E)
        lam_ = nu * np.sqrt(a)
        Lz = np.sum(q[:, 0] * p[:, 1] - q[:, 1] * p[:, 0])
        return lam_, np.sum(lam_) - abs(Lz), Lz

    L0, C0, Lz0 = elements(q, p)
    steps = int(years / s.years_per_unit / dt)
    mn, mx = L0.copy(), L0.copy()
    err = 0.0
    errL = 0.0
    every = 20
    for t in range(steps):
        k1q, k1p = field(q, p)
        k2q, k2p = field(q + dt / 2 * k1q, p + dt / 2 * k1p)
        k3q, k3p = field(q + dt / 2 * k2q, p + dt / 2 * k2p)
        k4q, k4p = field(q + dt * k3q, p + dt * k3p)
        q = q + dt / 6 * (k1q + 2 * k2q + 2 * k3q + k4q)
        p = p + dt / 6 * (k1p + 2 * k2p + 2 * k3p + k4p)
        if t % every == 0:
            L, C, Lz = elements(q, p)
            mn, mx = np.minimum(mn, L), np.maximum(mx, L)
            err = max(err, abs((C - C0) - np.sum(L - L0)))
            errL = max(errL, abs(Lz - Lz0))
    return dict(years=years, steps=steps, drift=(mx - mn).tolist(), amd_identity_residual=err, L_error=errL, C0=C0)


def hill_margin(ctx):
    """n = 2: walk along the energy curve h(I) = h(I0) from I0, inward and outward, and record where the margin B(I) - C closes,
    C = C0 + sum (I - I0), using only the exact integrals.  Returns the range of a_2 allowed before the AMD barrier can fail."""
    I0, nu = ctx.I0, ctx.nu
    h0 = -np.sum(nu ** 3 / (2 * I0 ** 2))
    if ctx.n != 2:
        return None

    def I1_of(I2):
        rhs = -h0 - nu[1] ** 3 / (2 * I2 ** 2)
        return float(nu[0] ** 1.5 / math.sqrt(2 * rhs)) if rhs > 0 else None

    out = {}
    for sign, name in ((-1, "inward"), (1, "outward")):
        I2 = float(I0[1])
        step = 1e-4 * I2
        last = None
        while True:
            I2n = I2 + sign * step
            step *= 1.01
            I1 = I1_of(I2n)
            if I2n <= 0 or I1 is None or (I1 / nu[0]) ** 2 >= (I2n / nu[1]) ** 2:
                out[name] = dict(stop="chamber boundary", a2=last)
                break
            Iv = np.array([I1, I2n])
            C = ctx.C0 + float(np.sum(Iv - I0))
            if C < 0:
                out[name] = dict(stop="AMD = 0 reached: excluded by the exact integrals alone", a2=(I2n / nu[1]) ** 2, a1=(I1 / nu[0]) ** 2)
                break
            if C >= G.B(Iv, nu):
                out[name] = dict(stop="margin closes", a2=(I2n / nu[1]) ** 2, a1=(I1 / nu[0]) ** 2, dI2=I2n - I0[1], dI1=I1 - I0[0])
                break
            I2 = I2n
            last = (I2n / nu[1]) ** 2
    return out


if __name__ == "__main__":
    from systems import catalogue
    import chain as Cn
    s = catalogue()["SJ"]
    c = Cn.Ctx(s, Kmax=2000)
    print(hill_margin(c))
    for r in (1e-3,):
        sc = scan(c, r)
        print({k: v for k, v in rates(c, sc, s.mu).items()}, "sup dlam", sc["sup_dlam"], sc["Gi"], sc["parts"])
        print(sc["shells"][:30])
    print(resonance_table(c))
    z = Ch._real_slow(np.random.default_rng(1), 1, 2, 1, c.I0, c.C0)[0]
    g = fast_lie(c, 0, 1, z[:2], z[2:], Q=5)
    print(g, {q: s.mu ** q * v for q, v in g.items()})
    r = fast_newton(c, 0, 1, z[:2], z[2:], s.mu)
    print(r["rho"], r["nsolved"], 2 * r["freq"][-1][0] - 5 * r["freq"][-1][1])
