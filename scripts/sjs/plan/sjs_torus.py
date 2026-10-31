#!/usr/bin/env python3
"""SJS-PLAN: a coarse numerical invariant torus of FH25's reduced planar Sun-Jupiter-Saturn Hamiltonian.

Untrusted design tooling, double precision, numpy only.  Reproduces FH25 Section 3 on a small grid:
  H(l, ghat, L, Ghat) = H0(L) + mu H1 o D  (FH25 (2.1), (2.2)), m = (0.9546, 0.2856), mu0 = 1e-3,
  fast frequencies (4.1), secular frequency (4.2), total angular momentum Ghat2 = 3.0583985...
  1. translated-torus continuation from mu = 0 (system (3.2), supertorsion (3.3)) at fixed Ghat0;
  2. invariant-torus refinement at fixed frequency (FH25 Section 3.2).
Coordinates z = (l1, l2, ghat, L1, L2, Ghat), 2 pi periodic angles, X_H = (dH/dI, -dH/dtheta), K(theta) = (theta + u, v).
E = L_omega K + X_H(K) + lambda X_Ghat, L_omega f = -Df omega, as in FH25.
Gradient and Hessian of H are exact (second-order jets of the Delaunay map per planet, closed forms for H1 in Cartesian
coordinates), evaluated slab by slab to bound memory.
Usage: python3 -I scripts/sjs/plan/sjs_torus.py --grid 64 64 64 --save OUT.npz [--load IN.npz] [--steps 20]
"""
import argparse, json, math, sys, time
import numpy as np

M = (0.9546, 0.2856)
MU0 = 1e-3
OMEGA = np.array([8.39549288702546301204e-2, 3.38240117059304358259e-2, -1.85007988077595e-5])
GTOT = 3.05839852910896096675
GHAT0 = 2.17657425006565519231          # FH25, the value giving lambda = 3e-14 at mu0
TWO_PI = 2 * math.pi
CUT = 1.0 / 3                           # the 2/3 rule: a looser cut (0.45 N) is unstable near mu = 6.5e-4 by aliasing


class J2:
    """Second-order jet in nv variables over numpy arrays: value, gradient g[i], symmetric Hessian h[i][j] (i <= j)."""
    __slots__ = ("v", "g", "h", "n")

    def __init__(self, v, g, h):
        self.v, self.g, self.h = v, g, h
        self.n = len(g)

    @staticmethod
    def var(v, i, n):
        z = np.zeros_like(v)
        return J2(v, [np.ones_like(v) if j == i else z for j in range(n)], [[z for _ in range(n)] for _ in range(n)])

    @staticmethod
    def const(v, n, like):
        z = np.zeros_like(like)
        return J2(v + z, [z] * n, [[z] * n for _ in range(n)])

    def __add__(self, o):
        if not isinstance(o, J2):
            return J2(self.v + o, self.g, self.h)
        return J2(self.v + o.v, [a + b for a, b in zip(self.g, o.g)],
                  [[a + b for a, b in zip(r, s)] for r, s in zip(self.h, o.h)])
    __radd__ = __add__

    def __neg__(self):
        return J2(-self.v, [-a for a in self.g], [[-a for a in r] for r in self.h])

    def __sub__(self, o):
        return self + (-o if isinstance(o, J2) else -o)

    def __rsub__(self, o):
        return (-self) + o

    def __mul__(self, o):
        if not isinstance(o, J2):
            return J2(self.v * o, [a * o for a in self.g], [[a * o for a in r] for r in self.h])
        n = self.n
        g = [self.v * o.g[i] + o.v * self.g[i] for i in range(n)]
        h = [[None] * n for _ in range(n)]
        for i in range(n):
            for j in range(i, n):
                h[i][j] = h[j][i] = (self.v * o.h[i][j] + o.v * self.h[i][j]
                                     + self.g[i] * o.g[j] + self.g[j] * o.g[i])
        return J2(self.v * o.v, g, h)
    __rmul__ = __mul__

    def fn(self, f0, f1, f2):
        """composition with a scalar function with value f0, derivatives f1, f2 at self.v."""
        n = self.n
        g = [f1 * a for a in self.g]
        h = [[None] * n for _ in range(n)]
        for i in range(n):
            for j in range(i, n):
                h[i][j] = h[j][i] = f1 * self.h[i][j] + f2 * self.g[i] * self.g[j]
        return J2(f0, g, h)

    def inv(self):
        v = self.v
        return self.fn(1 / v, -1 / v ** 2, 2 / v ** 3)

    def sqrt(self):
        s = np.sqrt(self.v)
        return self.fn(s, 0.5 / s, -0.25 / (s * self.v))

    def sin(self):
        s, c = np.sin(self.v), np.cos(self.v)
        return self.fn(s, c, -s)

    def cos(self):
        s, c = np.sin(self.v), np.cos(self.v)
        return self.fn(c, -s, -c)


def kepler_val(l, e):
    E = l + e * np.sin(l)
    for _ in range(12):
        d = (E - e * np.sin(E) - l) / (1 - e * np.cos(E))
        E = E - d
        if np.max(np.abs(d)) < 1e-15:
            break
    return E


def delaunay_jet(l, g, L, G, m):
    """(x1, x2, y1, y2) as jets in (l, g, L, G), FH25 Section 2."""
    n = 4
    jl, jg, jL, jG = (J2.var(a, i, n) for i, a in enumerate((l, g, L, G)))
    iL = jL.inv()
    ratio = jG * iL
    e = (1 - ratio * ratio).sqrt()
    a = jL * jL * (1 / m ** 2)
    b = iL * m ** 2
    E0 = kepler_val(l, e.v)
    E = J2.const(E0, n, l)
    for _ in range(2):                    # Newton on jets: order 0 -> 1 -> 3
        sE, cE = E.sin(), E.cos()
        E = E - (E - e * sE - jl) * (1 - e * cE).inv()
    sE, cE = E.sin(), E.cos()
    q1 = a * (cE - e)
    q2 = a * ratio * sE
    w = b * (1 - e * cE).inv()
    p1 = w * (-sE)
    p2 = w * ratio * cE
    cg, sg = jg.cos(), jg.sin()
    return (cg * q1 - sg * q2, sg * q1 + cg * q2, cg * p1 - sg * p2, sg * p1 + cg * p2)


def grad_hess_slab(z, mu, want_hess=True):
    """gradient (6, ...) and Hessian (6, 6, ...) of H at z = (l1, l2, gh, L1, L2, Gh), arrays of one slab."""
    l1, l2, gh, L1, L2, Gh = z
    G2 = GTOT - Gh
    Z1 = delaunay_jet(l1, gh, L1, Gh, M[0])
    Z2 = delaunay_jet(l2, np.zeros_like(l2), L2, G2, M[1])
    x1, x2, y1, y2 = [Z1[0].v, Z1[1].v], [Z2[0].v, Z2[1].v], [Z1[2].v, Z1[3].v], [Z2[2].v, Z2[3].v]
    d0, d1 = x1[0] - x2[0], x1[1] - x2[1]
    r2 = d0 * d0 + d1 * d1
    r = np.sqrt(r2)
    mm = M[0] * M[1]
    c3 = mm / (r2 * r)
    # gradient of H1 w.r.t. the 8 Cartesian slots (x1, y1 | x2, y2)
    sy0, sy1 = y1[0] + y2[0], y1[1] + y2[1]
    P1 = [c3 * d0, c3 * d1, sy0, sy1]
    P2 = [-c3 * d0, -c3 * d1, sy0, sy1]
    # u1 = (l1, g1, L1, G1) -> idx (0, 2, 3, 5), u2 = (l2, g2, L2, G2) -> idx (1, -, 4, 5 with sign -1)
    idx1, idx2 = (0, 2, 3, 5), (1, None, 4, 5)
    sgn2 = (1.0, 0.0, 1.0, -1.0)
    shape = l1.shape
    grad = np.zeros((6,) + shape)
    for a in range(4):
        grad[idx1[a]] += mu * sum(P1[c] * Z1[c].g[a] for c in range(4))
        if idx2[a] is not None:
            grad[idx2[a]] += mu * sgn2[a] * sum(P2[c] * Z2[c].g[a] for c in range(4))
    grad[3] += M[0] ** 3 / L1 ** 3
    grad[4] += M[1] ** 3 / L2 ** 3
    if not want_hess:
        return grad, None
    c5 = 3 * mm / (r2 * r2 * r)
    D = [[c3 - c5 * d0 * d0, -c5 * d0 * d1], [-c5 * d0 * d1, c3 - c5 * d1 * d1]]
    # 4x4 blocks of the Cartesian Hessian: P11, P12, P22, slots (x, y)
    z0 = np.zeros(shape)
    one = np.ones(shape)
    P11 = [[D[0][0], D[0][1], z0, z0], [D[1][0], D[1][1], z0, z0], [z0, z0, one, z0], [z0, z0, z0, one]]
    P22 = P11
    P12 = [[-D[0][0], -D[0][1], z0, z0], [-D[1][0], -D[1][1], z0, z0], [z0, z0, one, z0], [z0, z0, z0, one]]
    hess = np.zeros((6, 6) + shape)
    for a in range(4):
        ia = idx1[a]
        va = [sum(P11[c][d] * Z1[d].g[a] for d in range(4)) for c in range(4)]
        for b in range(a, 4):
            ib = idx1[b]
            w = sum(va[c] * Z1[c].g[b] + P1[c] * Z1[c].h[a][b] for c in range(4))
            hess[ia, ib] += mu * w
            if ia != ib:
                hess[ib, ia] += mu * w
    for a in range(4):
        ia = idx2[a]
        if ia is None:
            continue
        va = [sum(P22[c][d] * Z2[d].g[a] for d in range(4)) for c in range(4)]
        for b in range(a, 4):
            ib = idx2[b]
            if ib is None:
                continue
            w = sgn2[a] * sgn2[b] * sum(va[c] * Z2[c].g[b] + P2[c] * Z2[c].h[a][b] for c in range(4))
            hess[ia, ib] += mu * w
            if ia != ib:
                hess[ib, ia] += mu * w
    for a in range(4):
        ia = idx1[a]
        va = [sum(P12[c][d] * Z1[c].g[a] for c in range(4)) for d in range(4)]
        for b in range(4):
            ib = idx2[b]
            if ib is None:
                continue
            w = mu * sgn2[b] * sum(va[d] * Z2[d].g[b] for d in range(4))
            hess[ia, ib] += w
            hess[ib, ia] += w
    hess[3, 3] += -3 * M[0] ** 3 / L1 ** 4
    hess[4, 4] += -3 * M[1] ** 3 / L2 ** 4
    return grad, hess


def grad_hess(z, mu, want_hess=True, slab=8):
    shape = z.shape[1:]
    grad = np.zeros((6,) + shape)
    hess = np.zeros((6, 6) + shape) if want_hess else None
    for i in range(0, shape[0], slab):
        g, h = grad_hess_slab(z[:, i:i + slab], mu, want_hess)
        grad[:, i:i + slab] = g
        if want_hess:
            hess[:, :, i:i + slab] = h
    return grad, hess


class Grid:
    def __init__(self, shape, F=None):
        """F: unimodular integer matrix, theta_new = F theta (angles of the chart = F^-1 theta_new + periodic)."""
        self.shape = tuple(shape)
        self.F = np.eye(3, dtype=int) if F is None else np.array(F, dtype=int)
        self.Fi = np.rint(np.linalg.inv(self.F)).astype(int)
        self.omega = self.F @ OMEGA
        ax = [TWO_PI * np.arange(n) / n for n in shape]
        self.th = np.meshgrid(*ax, indexing="ij")
        self.k = [np.fft.fftfreq(n, 1.0 / n) for n in shape[:-1]] + [np.fft.rfftfreq(shape[-1], 1.0 / shape[-1])]
        kk = np.meshgrid(*self.k, indexing="ij", sparse=True)
        self.kk = kk
        lw = sum(k * w for k, w in zip(kk, self.omega))
        self.kw = lw + 0 * (kk[0] + kk[1] + kk[2])
        with np.errstate(divide="ignore"):
            self.Rw = np.where(self.kw == 0, 0, 1j / np.where(self.kw == 0, 1, self.kw))
        self.cut = np.ones(self.kw.shape, dtype=bool)
        for k, n in zip(kk, shape):
            self.cut = self.cut & (np.abs(k) <= n * CUT)

    def f(self, a):
        return np.fft.rfftn(a, axes=(-3, -2, -1))

    def fi(self, a):
        return np.fft.irfftn(a, s=self.shape, axes=(-3, -2, -1))

    def R(self, s):
        """R_omega: L_omega f = s - <s>, <f> = 0."""
        return self.fi(self.f(s) * self.Rw)

    def D(self, a):
        """derivative of periodic a (..., N1, N2, N3) -> (..., 3, N1, N2, N3)"""
        A = self.f(a)
        return np.stack([self.fi(1j * k * A) for k in self.kk], axis=-4)

    def filt(self, a):
        return self.fi(self.f(a) * self.cut)

    def theta_chart(self):
        """identity part of the chart angles: F^-1 theta_new."""
        return np.stack([sum(self.Fi[i, j] * self.th[j] for j in range(3)) for i in range(3)])

    def tangent_id(self):
        return np.vstack([self.Fi.astype(float), np.zeros((3, 3))])  # (6, 3)


def geom(gr, u, mu, lam, want_hess=True):
    """u: (6, ...) periodic part of K (angle corrections, full actions).  Returns everything of one Newton step."""
    z = u.copy()
    z[:3] += gr.theta_chart()
    grad, hess = grad_hess(z, mu, want_hess)
    XH = np.concatenate([grad[3:], -grad[:3]])
    DK = gr.D(u)                                         # (6, 3, ...)
    DK += gr.tangent_id().reshape(6, 3, 1, 1, 1)
    om = gr.omega.reshape(1, 3, 1, 1, 1)
    Dw = np.sum(DK * om, axis=1)
    E = -Dw + XH
    E[2] += lam                                          # X_Ghat = d/d ghat
    return dict(z=z, XH=XH, DK=DK, E=E, hess=hess, grad=grad)


def mv(A, x):
    return np.einsum("ij...,j...->i...", A, x)


def mm(A, B):
    return np.einsum("ik...,kj...->ij...", A, B)


OM = np.block([[np.zeros((3, 3)), -np.eye(3)], [np.eye(3), np.zeros((3, 3))]])
OMa = OM.reshape(6, 6, 1, 1, 1)


def frames(gr, g):
    DK = g["DK"]
    Dm = np.moveaxis(DK, (0, 1), (-2, -1))              # (..., 6, 3)
    G = np.swapaxes(Dm, -1, -2) @ Dm
    B = np.linalg.inv(G)
    Nm = (OM @ Dm) @ B                                   # N = J DK B, J = Omega
    return Dm, Nm, B


def torsion(g, Dm, Nm):
    """T = N^T Omega (DX + J DX J) N, DX = Omega^{-1} D2H (FH25)."""
    H = np.moveaxis(g["hess"], (0, 1), (-2, -1))
    DX = -OM @ H                                         # Omega^-1 = -Omega
    W = DX + OM @ DX @ OM
    T = np.swapaxes(Nm, -1, -2) @ OM @ W @ Nm
    return T


def newton(gr, u, lam, mu, mode, Ghat_target=None):
    """one (quasi-)Newton step; mode 'translated' (K, lambda) or 'invariant' (K only, lam = 0)."""
    g = geom(gr, u, mu, lam)
    E = g["E"]
    Dm, Nm, B = frames(gr, g)
    T = torsion(g, Dm, Nm)
    Em = np.moveaxis(E, 0, -1)[..., None]               # (..., 6, 1)
    OE = OM @ Em
    etaL = -(np.swapaxes(Nm, -1, -2) @ OE)[..., 0]
    etaN = (np.swapaxes(Dm, -1, -2) @ OE)[..., 0]
    Tt = np.moveaxis(T, (-2, -1), (0, 1))                # (3, 3, ...)
    etaL, etaN = np.moveaxis(etaL, -1, 0), np.moveaxis(etaN, -1, 0)
    RetaN = gr.R(etaN)
    etat = etaL - mv(Tt, RetaN)
    avg = lambda a: a.mean(axis=(-3, -2, -1))
    Tavg = avg(Tt)
    RT = gr.R(Tt - Tavg.reshape(3, 3, 1, 1, 1))
    if mode == "translated":
        XG = np.zeros(6); XG[2] = 1.0
        Xv = XG.reshape(6, 1, 1, 1, 1)
        OX = (OM @ XG).reshape(6, 1)
        bL = np.moveaxis((np.swapaxes(Nm, -1, -2) @ OX)[..., 0], -1, 0)
        bN = np.moveaxis(-(np.swapaxes(Dm, -1, -2) @ OX)[..., 0], -1, 0)
        RbN = gr.R(bN)
        bt = bL - mv(Tt, RbN)
        Rbt = gr.R(bt)
        Retat = gr.R(etat)
        Pi = 5                                           # Ghat component
        DKt = np.moveaxis(Dm, (-2, -1), (0, 1))
        Nt = np.moveaxis(Nm, (-2, -1), (0, 1))
        A = np.zeros((4, 4))
        A[:3, :3] = Tavg
        A[:3, 3] = avg(bt)
        A[3, :3] = avg(Nt[Pi] - np.einsum("j...,ji...->i...", DKt[Pi], RT))
        A[3, 3] = -avg(np.einsum("j...,j...->...", DKt[Pi], Rbt) + np.einsum("j...,j...->...", Nt[Pi], RbN))
        etaG = -avg(u[Pi]) + Ghat_target
        rhs = np.zeros(4)
        rhs[:3] = avg(etat)
        rhs[3] = etaG - avg(np.einsum("j...,j...->...", DKt[Pi], Retat))
        sol = np.linalg.solve(A, rhs)
        xi0, dlam = sol[:3], sol[3]
        xiN = xi0.reshape(3, 1, 1, 1) + RetaN - RbN * dlam
        xiL = Retat - mv(RT, xi0.reshape(3, 1, 1, 1)) - Rbt * dlam
    else:
        xi0 = np.linalg.solve(Tavg, avg(etat))
        xiN = xi0.reshape(3, 1, 1, 1) + RetaN
        xiL = gr.R(etat) - mv(RT, xi0.reshape(3, 1, 1, 1))
        dlam = 0.0
    xim = np.concatenate([xiL, xiN])
    Pm = np.concatenate([Dm, Nm], axis=-1)               # (..., 6, 6)
    du = (Pm @ np.moveaxis(xim, 0, -1)[..., None])[..., 0]
    du = np.moveaxis(du, -1, 0)
    unew = gr.filt(u + du)
    info = dict(err=float(np.max(np.abs(E))), dlam=float(dlam), du=float(np.max(np.abs(du))),
                Tavg=Tavg, Tinv=float(np.max(np.sum(np.abs(np.linalg.inv(Tavg)), axis=1))))
    return unew, lam + dlam, info


def initial(gr, Ghat0=GHAT0):
    L0 = [M[i] / OMEGA[i] ** (1 / 3.0) for i in range(2)]
    u = np.zeros((6,) + gr.shape)
    u[3] += L0[0]; u[4] += L0[1]; u[5] += Ghat0
    return u


def upsample(u, old, new):
    """Fourier interpolation of periodic u between grids."""
    U = np.fft.rfftn(u, axes=(-3, -2, -1))
    out = np.zeros((6,) + tuple(new[:2]) + (new[2] // 2 + 1,), dtype=complex)
    n0, n1, n2 = [min(a, b) for a, b in zip(old, new)]
    h0, h1 = n0 // 2, n1 // 2
    h2 = min(old[2] // 2, new[2] // 2)
    for s0, d0 in ((slice(0, h0), slice(0, h0)), (slice(-h0 + 1, None), slice(-h0 + 1, None))):
        for s1, d1 in ((slice(0, h1), slice(0, h1)), (slice(-h1 + 1, None), slice(-h1 + 1, None))):
            out[:, d0, d1, :h2] = U[:, s0, s1, :h2]
    return np.fft.irfftn(out, s=new, axes=(-3, -2, -1)) * (np.prod(new) / np.prod(old))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--grid", type=int, nargs=3, default=[64, 64, 64])
    ap.add_argument("--load")
    ap.add_argument("--save")
    ap.add_argument("--steps", type=int, default=20)
    ap.add_argument("--newton", type=int, default=3)
    ap.add_argument("--refine", type=int, default=6)
    a = ap.parse_args()
    gr = Grid(a.grid)
    t0 = time.time()
    if a.load:
        d = np.load(a.load)
        u = upsample(d["u"], d["u"].shape[1:], tuple(a.grid))
        lam = float(d["lam"])
    else:
        u = initial(gr)
        lam = float(OMEGA[2])
        us, lams, mus = [], [], []
        for j in range(1, a.steps + 1):
            mu = MU0 * j / a.steps
            if len(us) == 2:                               # secant predictor in mu
                u = 2 * us[1] - us[0]
                lam = 2 * lams[1] - lams[0]
            for it in range(a.newton):
                u, lam, info = newton(gr, u, lam, mu, "translated", GHAT0)
            print("mu %.3e err %.2e dlam %.2e du %.2e lam %.4e |T^-1| %.1f t %.0f" % (
                mu, info["err"], info["dlam"], info["du"], lam, info["Tinv"], time.time() - t0), flush=True)
            us = (us + [u.copy()])[-2:]
            lams = (lams + [lam])[-2:]
    for it in range(a.refine):
        u, lam2, info = newton(gr, u, 0.0, MU0, "invariant")
        print("refine %d err %.3e du %.2e |T^-1| %.3f <Ghat> %.12f t %.0f" % (
            it, info["err"], info["du"], info["Tinv"], u[5].mean(), time.time() - t0), flush=True)
    if a.save:
        np.savez(a.save, u=u, lam=lam, Tavg=info["Tavg"], grid=np.array(a.grid))


if __name__ == "__main__":
    main()
