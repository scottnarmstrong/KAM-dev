#!/usr/bin/env python3
"""Generic double-precision solver and norm sampler for primary 2-tori (track APPS-SCOUT).

Untrusted tooling: every number here is a numerical estimate, never a certificate.

Conventions follow the repository: angles of period 1, H(theta, I) on T^2 x R^2, X_H = J grad H,
torus K(theta) = (theta + u(theta), y(theta)), invariance X_H(K) = d_omega K with omega = s omega*.

Contents
  Jet       truncated multivariate Taylor arithmetic over numpy arrays (derivatives of any H up to order 3)
  Torus     Fourier grid, spectral derivatives, cohomological solve, evaluation on the complex strip
  newton    the isoenergetic quasi-Newton step of HL19 / FH25 sec. 3 (bordered 3x3 system)
  spectrum  coefficient envelopes, decay fits and support counts
  norms     sampled majorants M, sigma_K, sigma_B, sigma_T on the distinguished boundary of the strip
"""
import itertools
import math
import numpy as np

# ---------------------------------------------------------------------------------------------
# truncated Taylor jets
# ---------------------------------------------------------------------------------------------

class JetSpace:
    def __init__(self, nvars, degree):
        self.nvars, self.degree = nvars, degree
        self.index = []
        for d in range(degree + 1):
            for c in itertools.combinations_with_replacement(range(nvars), d):
                a = [0] * nvars
                for i in c:
                    a[i] += 1
                self.index.append(tuple(a))
        self.pos = {a: i for i, a in enumerate(self.index)}
        self.table = []
        for i, a in enumerate(self.index):
            for j, b in enumerate(self.index):
                c = tuple(x + y for x, y in zip(a, b))
                if sum(c) <= degree:
                    self.table.append((i, j, self.pos[c]))
        self.fact = [float(np.prod([math.factorial(x) for x in a])) for a in self.index]

    def seed(self, z):
        return [Jet(self, self._const(z[i]), i) for i in range(self.nvars)]

    def _const(self, x):
        c = [0.0] * len(self.index)
        c[0] = x
        return c


class Jet:
    __array_priority__ = 100

    def __init__(self, sp, c, var=None):
        self.sp, self.c = sp, list(c)
        if var is not None:
            e = [0] * sp.nvars
            e[var] = 1
            self.c[sp.pos[tuple(e)]] = 1.0

    def _lift(self, o):
        return o if isinstance(o, Jet) else Jet(self.sp, self.sp._const(o))

    def __add__(self, o):
        o = self._lift(o)
        return Jet(self.sp, [a + b for a, b in zip(self.c, o.c)])
    __radd__ = __add__

    def __neg__(self):
        return Jet(self.sp, [-a for a in self.c])

    def __sub__(self, o):
        return self + (-self._lift(o))

    def __rsub__(self, o):
        return self._lift(o) + (-self)

    def __mul__(self, o):
        if not isinstance(o, Jet):
            return Jet(self.sp, [a * o for a in self.c])
        r = [0.0] * len(self.c)
        for i, j, k in self.sp.table:
            r[k] = r[k] + self.c[i] * o.c[j]
        return Jet(self.sp, r)
    __rmul__ = __mul__

    def compose(self, derivs):
        """f(self) given [f(a0), f'(a0), f''(a0), ...], a0 the constant term."""
        d = self.sp.degree
        dl = Jet(self.sp, [0.0] + self.c[1:])
        res = self.sp._const(derivs[0])
        res = Jet(self.sp, res)
        pw = Jet(self.sp, self.sp._const(1.0))
        f = 1.0
        for m in range(1, d + 1):
            pw = pw * dl
            f *= m
            res = res + pw * (derivs[m] / f)
        return res

    def inv(self):
        a = self.c[0]
        d = [1 / a]
        for m in range(1, self.sp.degree + 1):
            d.append(d[-1] * (-m) / a)
        return self.compose(d)

    def __truediv__(self, o):
        return self * (self._lift(o).inv())

    def __rtruediv__(self, o):
        return self._lift(o) * self.inv()

    def __pow__(self, m):
        r = Jet(self.sp, self.sp._const(1.0))
        for _ in range(m):
            r = r * self
        return r

    def rpow(self, p):
        a = self.c[0]
        d = [a ** p]
        q = p
        for m in range(1, self.sp.degree + 1):
            d.append(d[-1] * q / a)
            q -= 1
        return self.compose(d)

    def sqrt(self):
        return self.rpow(0.5)

    def sin(self):
        s, c = np.sin(self.c[0]), np.cos(self.c[0])
        return self.compose([s, c, -s, -c, s][: self.sp.degree + 1])

    def cos(self):
        s, c = np.sin(self.c[0]), np.cos(self.c[0])
        return self.compose([c, -s, -c, s, c][: self.sp.degree + 1])

    def exp(self):
        e = np.exp(self.c[0])
        return self.compose([e] * (self.sp.degree + 1))

    def log(self):
        a = self.c[0]
        d = [np.log(a), 1 / a]
        for m in range(2, self.sp.degree + 1):
            d.append(d[-1] * (-(m - 1)) / a)
        return self.compose(d)


def derivs(H, z, degree=2, const=False):
    """grad and hessian (and third derivatives if degree = 3) of H at z = (q1,q2,p1,p2) arrays."""
    nv = len(z)
    sp = JetSpace(nv, degree)
    v = H(sp.seed(z))
    shape = np.shape(z[0])
    dtype = np.result_type(*[np.asarray(a) for a in z])
    def coef(a):
        i = sp.pos[tuple(a)]
        x = v.c[i] * sp.fact[i]
        return np.broadcast_to(np.asarray(x, dtype=np.result_type(dtype, float)), shape)
    e = np.eye(nv, dtype=int)
    g = np.array([coef(e[i]) for i in range(nv)])
    out = [g]
    if degree >= 2:
        out.append(np.array([[coef(e[i] + e[j]) for j in range(nv)] for i in range(nv)]))
    if degree >= 3:
        t = np.array([[[coef(e[i] + e[j] + e[k]) for k in range(nv)] for j in range(nv)] for i in range(nv)])
        out.append(t)
    if const:
        out.insert(0, np.broadcast_to(np.asarray(v.c[0]), shape))
    return out


# ---------------------------------------------------------------------------------------------
# Fourier torus
# ---------------------------------------------------------------------------------------------

Ja = np.array([[0, 0, 1, 0], [0, 0, 0, 1], [-1, 0, 0, 0], [0, -1, 0, 0]], dtype=float)
Om = -Ja


class Grid:
    def __init__(self, N1, N2, frac=2 / 3):
        self.N1, self.N2 = N1, N2
        self.k1 = np.fft.fftfreq(N1, 1 / N1)[:, None] * np.ones((1, N2))
        self.k2 = np.fft.fftfreq(N2, 1 / N2)[None, :] * np.ones((N1, 1))
        self.mask = (np.abs(self.k1) <= frac * N1 / 2) & (np.abs(self.k2) <= frac * N2 / 2)
        t1 = np.arange(N1) / N1
        t2 = np.arange(N2) / N2
        self.t1, self.t2 = np.meshgrid(t1, t2, indexing="ij")

    def f(self, a):
        return np.fft.fft2(a) / (self.N1 * self.N2)

    def i(self, a):
        return np.fft.ifft2(a * (self.N1 * self.N2))

    def filt(self, a):
        return self.i(self.f(a) * self.mask).real

    def d(self, a, j):
        k = self.k1 if j == 0 else self.k2
        return self.i(self.f(a) * (2j * np.pi * k))

    def dom(self, a, om):
        return self.i(self.f(a) * (2j * np.pi * (self.k1 * om[0] + self.k2 * om[1]))).real

    def rsolve(self, a, om):
        """zero-average solution of d_om u = a - <a> (filtered)."""
        lam = 2j * np.pi * (self.k1 * om[0] + self.k2 * om[1])
        lam[0, 0] = 1
        h = self.f(a) * self.mask / lam
        h[0, 0] = 0
        return self.i(h).real

    def strip(self, a, rho, sg):
        """evaluate at theta + i rho (sg1, sg2), a real on the grid."""
        w = np.exp(-2 * np.pi * rho * (sg[0] * self.k1 + sg[1] * self.k2)) * self.mask
        return self.i(self.f(a) * w)


class Torus:
    """u[i], y[i] on a grid; K(theta) = (theta + u, y)."""
    def __init__(self, grid, y0, u=None, y=None):
        self.g = grid
        self.u = np.zeros((2, grid.N1, grid.N2)) if u is None else u
        self.y = np.array([np.full((grid.N1, grid.N2), float(y0[0])),
                           np.full((grid.N1, grid.N2), float(y0[1]))]) if y is None else y

    def copy(self):
        return Torus(self.g, None, self.u.copy(), self.y.copy())

    def resample(self, grid):
        """spectral resampling to a finer or coarser grid."""
        out = []
        g = self.g
        for a in np.concatenate([self.u, self.y]):
            h = g.f(a)
            r = np.zeros((grid.N1, grid.N2), dtype=complex)
            K1, K2 = min(g.N1, grid.N1) // 2 - 1, min(g.N2, grid.N2) // 2 - 1
            for i in range(-K1, K1 + 1):
                for j in range(-K2, K2 + 1):
                    r[i % grid.N1, j % grid.N2] = h[i % g.N1, j % g.N2]
            out.append(grid.i(r).real)
        return Torus(grid, None, np.array(out[:2]), np.array(out[2:]))

    def z(self):
        g = self.g
        return [g.t1 + self.u[0], g.t2 + self.u[1], self.y[0], self.y[1]]

    def frame(self):
        g = self.g
        L = np.zeros((4, 2, g.N1, g.N2))
        for j in range(2):
            L[0, j] = (1.0 if j == 0 else 0.0) + g.d(self.u[0], j).real
            L[1, j] = (1.0 if j == 1 else 0.0) + g.d(self.u[1], j).real
            L[2, j] = g.d(self.y[0], j).real
            L[3, j] = g.d(self.y[1], j).real
        return L


def mm(*ms):
    r = ms[0]
    for m in ms[1:]:
        r = np.einsum("ik...,kj...->ij...", r, m)
    return r


def tr(m):
    return np.einsum("ij...->ji...", m)


def inv2(G):
    det = G[0, 0] * G[1, 1] - G[0, 1] * G[1, 0]
    return np.array([[G[1, 1], -G[0, 1]], [-G[1, 0], G[0, 0]]]) / det


def newton(H, tor, om, s, E0=None, iso=True):
    """One quasi-Newton step at frequency s*om. Returns (new torus, new s, sup error, avg H)."""
    g = tor.g
    z = tor.z()
    Hv, gr, he = derivs(H, z, 2, const=True)
    gr, he = gr.real, he.real
    Hv = np.real(Hv)
    w = (s * om[0], s * om[1])
    X = np.einsum("ij,j...->i...", Ja, gr)
    DX = np.einsum("ij,jk...->ik...", Ja, he)
    L = tor.frame()
    G = mm(tr(L), L)
    B = inv2(G)
    N = np.einsum("ij,jk...->ik...", Ja, mm(L, B))
    dK = np.array([w[0] + g.dom(tor.u[0], w), w[1] + g.dom(tor.u[1], w), g.dom(tor.y[0], w), g.dom(tor.y[1], w)])
    E = X - dK
    err = float(np.abs(E).max())
    OmE = np.einsum("ij,j...->i...", Om, E)
    aL = -np.einsum("ji...,j...->i...", N, OmE)
    aN = np.einsum("ji...,j...->i...", L, OmE)
    dN = np.array([[g.dom(N[i, j], w) for j in range(2)] for i in range(4)])
    A = mm(DX, N) - dN
    T = -mm(tr(N), np.einsum("ij,jk...->ik...", Om, A))
    Ta = T.mean(axis=(2, 3))
    xiN0 = np.array([g.rsolve(aN[i], w) for i in range(2)])
    Tx = np.einsum("ij...,j...->i...", T, xiN0)
    rhs1 = -(Tx.mean(axis=(1, 2)) + aL.mean(axis=(1, 2)))
    c = np.einsum("ji...,j...->i...", N, gr)
    if iso:
        Eav = Hv.mean()
        target = Eav if E0 is None else E0
        rhs2 = target - Eav - np.einsum("i...,i...->...", c, xiN0).mean()
        ca = c.mean(axis=(1, 2))
        M = np.zeros((3, 3))
        M[:2, :2] = Ta
        M[:2, 2] = -np.array(om)
        M[2, :2] = ca
        sol = np.linalg.solve(M, np.append(rhs1, rhs2))
        xb, ds = sol[:2], sol[2]
    else:
        xb, ds = np.linalg.solve(Ta, rhs1), 0.0
    xiN = xiN0 + xb[:, None, None]
    src = np.einsum("ij...,j...->i...", T, xiN) + aL - np.array(om)[:, None, None] * ds
    xiL = np.array([g.rsolve(src[i], w) for i in range(2)])
    dKc = np.einsum("ij...,j...->i...", L, xiL) + np.einsum("ij...,j...->i...", N, xiN)
    new = tor.copy()
    new.u[0] = g.filt(tor.u[0] + dKc[0])
    new.u[1] = g.filt(tor.u[1] + dKc[1])
    new.y[0] = g.filt(tor.y[0] + dKc[2])
    new.y[1] = g.filt(tor.y[1] + dKc[3])
    return new, s + ds, err, float(Hv.mean())


def solve(H, tor, om, s=1.0, E0=None, iso=True, tol=1e-12, maxit=25, verbose=False, damp_stop=1e3):
    best = None
    for it in range(maxit):
        new, s2, err, av = newton(H, tor, om, s, E0, iso)
        if verbose:
            print("   it", it, "err %.3e s %.12f" % (err, s))
        if not np.isfinite(err) or err > damp_stop:
            return (best or (tor, s, np.inf))
        if best is None or err < best[2]:
            best = (tor, s, err)
        if err < tol:
            break
        if it > 4 and err > 0.9 * best[2] and err > 10 * tol and it > 8:
            break
        tor, s = new, s2
    return best


def newton_free(H, tor, om, ybar):
    """Quasi-Newton step at prescribed mean actions ybar with the frequency vector free (no small-divisor assumption beyond the filter)."""
    g = tor.g
    gr, he = derivs(H, tor.z(), 2)
    gr, he = gr.real, he.real
    w = (om[0], om[1])
    X = np.einsum("ij,j...->i...", Ja, gr)
    DX = np.einsum("ij,jk...->ik...", Ja, he)
    L = tor.frame()
    B = inv2(mm(tr(L), L))
    N = np.einsum("ij,jk...->ik...", Ja, mm(L, B))
    dK = np.array([w[0] + g.dom(tor.u[0], w), w[1] + g.dom(tor.u[1], w), g.dom(tor.y[0], w), g.dom(tor.y[1], w)])
    E = X - dK
    err = float(np.abs(E).max())
    OmE = np.einsum("ij,j...->i...", Om, E)
    aL = -np.einsum("ji...,j...->i...", N, OmE)
    aN = np.einsum("ji...,j...->i...", L, OmE)
    dN = np.array([[g.dom(N[i, j], w) for j in range(2)] for i in range(4)])
    T = -mm(tr(N), np.einsum("ij,jk...->ik...", Om, mm(DX, N) - dN))
    xiN = np.array([g.rsolve(aN[i], w) for i in range(2)])
    src = np.einsum("ij...,j...->i...", T, xiN) + aL
    dw = src.mean(axis=(1, 2))
    xiL = np.array([g.rsolve(src[i] - dw[i], w) for i in range(2)])
    dKc = np.einsum("ij...,j...->i...", L, xiL) + np.einsum("ij...,j...->i...", N, xiN)
    new = tor.copy()
    new.u[0] = g.filt(tor.u[0] + dKc[0])
    new.u[1] = g.filt(tor.u[1] + dKc[1])
    new.y[0] = g.filt(tor.y[0] + dKc[2])
    new.y[1] = g.filt(tor.y[1] + dKc[3])
    new.y[0] += ybar[0] - new.y[0].mean()
    new.y[1] += ybar[1] - new.y[1].mean()
    return new, (om[0] + dw[0], om[1] + dw[1]), err


def find_freq(H, tor, om, ybar, tol=1e-12, maxit=30):
    """iterate newton_free; returns (torus, frequency, error)."""
    best = (tor, om, float("inf"))
    for it in range(maxit):
        new, om2, err = newton_free(H, tor, om, ybar)
        if not np.isfinite(err):
            return best
        if err < best[2]:
            best = (tor, om, err)
        if err < tol:
            break
        if it > 8 and err > 0.5 * best[2]:
            break
        tor, om = new, om2
    return best


# ---------------------------------------------------------------------------------------------
# spectrum: decay and support
# ---------------------------------------------------------------------------------------------

def envelope(tor):
    g = tor.g
    m = np.zeros((g.N1, g.N2))
    for a in np.concatenate([tor.u, tor.y]):
        m = np.maximum(m, np.abs(g.f(a - a.mean())))
    return m


def fit_decay(tor, floor=1e-12, hi=1e-3):
    """decay in digits per mode along each angle: log10|c| ~ A - a1|k1| - a2|k2|, fit on envelopes."""
    g = tor.g
    m = envelope(tor) * g.mask
    out = []
    for ax in (0, 1):
        e = m.max(axis=1 - ax)
        N = g.N1 if ax == 0 else g.N2
        ks, vs = [], []
        best = {}
        for i in range(N):
            k = abs(int(np.fft.fftfreq(N, 1 / N)[i]))
            best[k] = max(best.get(k, 0), e[i])
        # upper envelope: running maximum from the right, on [floor, hi]
        K = sorted(best)
        run = 0
        env = {}
        for k in reversed(K):
            run = max(run, best[k])
            env[k] = run
        for k in K:
            if k > 0 and floor < env[k] < hi:
                ks.append(k)
                vs.append(np.log10(env[k]))
        if len(ks) >= 2:
            a, b = np.polyfit(ks, vs, 1)
            out.append((-a, b, ks[-1]))
        else:
            out.append((float("nan"), float("nan"), 0))
    return out


def support_counts(tor, Ls=(6, 8, 10, 12)):
    m = envelope(tor) * tor.g.mask
    return {L: int((m > 10.0 ** (-L)).sum()) for L in Ls}


def support_model(tor, floor_L=(8, 12)):
    """Fit S(L) = alpha L^2 on the measured counts (the SO fit N_E = 1.1 L^2 has this form)."""
    c = support_counts(tor, tuple(range(floor_L[0], floor_L[1] + 1)))
    x = np.array([L ** 2 for L in c], dtype=float)
    y = np.array([c[L] for L in c], dtype=float)
    alpha = float((x * y).sum() / (x * x).sum())
    return alpha, c


# ---------------------------------------------------------------------------------------------
# sampled norm majorants on the strip
# ---------------------------------------------------------------------------------------------

SIGNS = [(1, 1), (1, -1), (-1, 1), (-1, -1)]


def rowsum(A):
    """sup over the arrays of the max row sum; A[i,j,...]."""
    return float(np.abs(A).sum(axis=1).max())


def strip_data(H, tor, rho, mu=0.0):
    """Everything needed by `package`, on the four corners of the distinguished boundary."""
    g = tor.g
    data = []
    for sg in SIGNS:
        q = [g.t1 + 1j * rho * sg[0] + g.strip(tor.u[0], rho, sg), g.t2 + 1j * rho * sg[1] + g.strip(tor.u[1], rho, sg)]
        p = [g.strip(tor.y[0], rho, sg), g.strip(tor.y[1], rho, sg)]
        z = q + p
        L = np.zeros((4, 2, g.N1, g.N2), dtype=complex)
        arrs = [tor.u[0], tor.u[1], tor.y[0], tor.y[1]]
        for i in range(4):
            for j in range(2):
                k = g.k1 if j == 0 else g.k2
                L[i, j] = g.i(g.f(arrs[i]) * (2j * np.pi * k) * np.exp(-2 * np.pi * rho * (sg[0] * g.k1 + sg[1] * g.k2)) * g.mask)
        L[0, 0] += 1
        L[1, 1] += 1
        ders = []
        offs = [(0, 0, 0, 0)] if mu == 0 else [(1, 1, 1, 1), (-1, -1, -1, -1)]
        for o in offs:
            zo = [z[i] + 1j * mu * o[i] for i in range(4)]
            ders.append(derivs(H, zo, 3))
        data.append(dict(L=L, ders=ders))
    return data


def bordered_avg(H, tor, om_s, s=1.0):
    """<T> and the mean of N^T grad H (the border), unscaled, on the real torus."""
    g = tor.g
    z = tor.z()
    gr, he = derivs(H, z, 2)
    gr, he = gr.real, he.real
    DX = np.einsum("ij,jk...->ik...", Ja, he)
    L = tor.frame()
    B = inv2(mm(tr(L), L))
    N = np.einsum("ij,jk...->ik...", Ja, mm(L, B))
    w = (s * om_s[0], s * om_s[1])
    dN = np.array([[g.dom(N[i, j], w) for j in range(2)] for i in range(4)])
    A = mm(DX, N) - dN
    T = -mm(tr(N), np.einsum("ij,jk...->ik...", Om, A))
    return T, L, B, N, gr, he


def package(sd, H, tor, om, s, lam=(1.0, 1.0), c=1.0, mu=1 / 160, slack=1.05):
    """Sampled majorants after the action scaling y -> y/lam_i, H -> c H / det-free scaling.

    The scaling I = lam I' with H' = c H(theta, lam I')/lam is symplectic only for equal lam_1 = lam_2
    (conformal factor), which is all we use here: lam = (l, l).  Returns dict with M, sK, sB, sT (slack and mu
    included, as package R1) and the separate raw pieces (M0,M1,M2 for the v2 estimate)."""
    l = lam[0]
    # scale factors for derivatives: d_q^a d_p^b H' = (c/l) l^b d_q^a d_p^b H
    fac = np.array([1.0, 1.0, l, l])
    M_DH = M_XH = M_DX = M_D2X = M_D2H = 0.0
    sK = sB = 0.0
    for d in sd:
        L = d["L"].copy()
        L[2:] = L[2:] / l
        G = mm(tr(L), L)
        Bm = inv2(G)
        sK = max(sK, rowsum(L))
        sB = max(sB, rowsum(Bm))
        for (gr, he, th) in d["ders"]:
            g1 = (c / l) * np.einsum("i,i...->i...", fac, gr)
            h1 = (c / l) * np.einsum("i,j,ij...->ij...", fac, fac, he)
            t1 = (c / l) * np.einsum("i,j,k,ijk...->ijk...", fac, fac, fac, th)
            M_DH = max(M_DH, float(np.abs(g1).sum(axis=0).max()))
            M_XH = max(M_XH, float(np.abs(g1).max()))
            DX = np.einsum("ij,jk...->ik...", Ja, h1)
            M_DX = max(M_DX, rowsum(DX))
            M_D2H = max(M_D2H, rowsum(h1))
            D2X = np.einsum("ij,jkl...->ikl...", Ja, t1)
            M_D2X = max(M_D2X, float(np.abs(D2X).sum(axis=(1, 2)).max()))
    # bordered torsion, at the scaled problem
    T, L0, B0, N0, gr0, he0 = bordered_avg(H, tor, om, s)
    Ls = L0.copy()
    Ls[2:] = Ls[2:] / l
    Bs = inv2(mm(tr(Ls), Ls))
    Ns = np.einsum("ij,jk...->ik...", Ja, mm(Ls, Bs))
    w = (c * s * om[0], c * s * om[1])
    g = tor.g
    he1 = (c / l) * np.einsum("i,j,ij...->ij...", fac, fac, he0)
    gr1 = (c / l) * np.einsum("i,i...->i...", fac, gr0)
    DXs = np.einsum("ij,jk...->ik...", Ja, he1)
    dN = np.array([[g.dom(Ns[i, j], w) for j in range(2)] for i in range(4)])
    Ts = -mm(tr(Ns), np.einsum("ij,jk...->ik...", Om, mm(DXs, Ns) - dN))
    Ta = Ts.mean(axis=(2, 3))
    ca = np.einsum("ji...,j...->i...", Ns, gr1).mean(axis=(1, 2))
    Bd = np.zeros((3, 3))
    Bd[:2, :2] = Ta
    Bd[:2, 2] = -np.array(om) * c
    Bd[2, :2] = ca
    try:
        Bi = np.linalg.inv(Bd)
        sT = float(np.abs(Bi).sum(axis=1).max())
    except np.linalg.LinAlgError:
        sT = float("inf")
    # fixed-frequency twist, when it exists
    try:
        sT_fix = float(np.abs(np.linalg.inv(Ta)).sum(axis=1).max())
    except np.linalg.LinAlgError:
        sT_fix = float("inf")
    raw = dict(DH=M_DH, XH=M_XH, DX=M_DX, D2X=M_D2X, D2H=M_D2H, sK=sK, sB=sB, sT=sT, sT_fix=sT_fix,
               Tmax=float(np.abs(Ts).sum(axis=1).max()), Tavg=Ta.tolist())
    M = max(M_DH, M_XH, M_DX, M_D2X, M_D2H)
    return dict(M=slack * M, sK=slack * sK + mu, sB=slack * sB + mu, sT=slack * sT + mu,
                M0=slack * max(M_DH, M_XH), M1=slack * max(M_DX, M_D2H), M2=slack * M_D2X, raw=raw)


def dio_gamma(om, kmax=2000, tau=1):
    """numerical infimum of |k.om| |k|_1^tau over 0 < |k|_1 <= kmax, for om = (a, b)."""
    a, b = om
    best = (float("inf"), None)
    for k1 in range(0, kmax + 1):
        if b != 0:
            k2c = -k1 * a / b
            for k2 in (math.floor(k2c), math.ceil(k2c)):
                if k1 == 0 and k2 == 0:
                    continue
                v = abs(k1 * a + k2 * b) * (abs(k1) + abs(k2)) ** tau
                if v < best[0]:
                    best = (v, (k1, k2))
    k = (0, 1)
    v = abs(b)
    if v < best[0]:
        best = (v, k)
    return best
