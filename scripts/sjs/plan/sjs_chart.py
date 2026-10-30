#!/usr/bin/env python3
"""SJS-PLAN: norms of the coarse SJS torus in a certificate's chart, for the Delaunay chart and the regular chart.

Untrusted design tooling, double precision.  Two charts of the reduced planar SJS Hamiltonian (FH25 (2.2)):
  'del': z = (l1, l2, ghat, L1, L2, Ghat), FH25's.
  'reg': z = (a1, a2, a3, Lambda1, Lambda2, I6), polar coordinates in the secular normal modes (sjs_spectrum.py), gauge psi5 = 0.
Certificate chart (as lg00_oracle.py): theta = phi/2pi, I = I0 + ell a, h~ = c h / (2 pi ell), K~ = (theta + u/2pi, v/ell),
omega~ = c omega / 2 pi, followed by the unimodular reparametrization making K primary.
This module: truncated Taylor algebra (TPS) on numpy arrays (real or complex), derivative tensors of H up to order 3 on sample
points, the sampled majorants M0, M1, M2 on the tube around K (sampled, not an enclosure) and on the polydisc box the landed
ball arithmetic uses, frames on the distinguished boundary of T_rho, torsion on a real grid.
"""
import itertools, json, math, os, sys
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import sjs_torus as ST
import sjs_spectrum as SPEC
sys.path.pop(0)

TP = 2 * math.pi
M1, M2 = ST.M


class Alg:
    def __init__(self, nv, deg):
        self.nv, self.deg = nv, deg
        monos = [e for e in itertools.product(range(deg + 1), repeat=nv) if sum(e) <= deg]
        monos.sort(key=lambda e: (sum(e), e))
        self.monos = monos
        self.idx = {e: i for i, e in enumerate(monos)}
        I, J, K = [], [], []
        for i, a in enumerate(monos):
            for j, b in enumerate(monos):
                if sum(a) + sum(b) <= deg:
                    I.append(i); J.append(j); K.append(self.idx[tuple(x + y for x, y in zip(a, b))])
        self.I, self.J, self.K = np.array(I), np.array(J), np.array(K)
        self.nm = len(monos)


class T:
    __slots__ = ("A", "c")

    def __init__(self, A, c):
        self.A, self.c = A, c

    @staticmethod
    def const(A, v):
        c = np.zeros((A.nm,) + np.shape(v), dtype=complex)
        c[0] = v
        return T(A, c)

    @staticmethod
    def var(A, v, i):
        t = T.const(A, v)
        e = [0] * A.nv; e[i] = 1
        t.c[A.idx[tuple(e)]] = 1.0
        return t

    def __add__(self, o):
        if isinstance(o, T):
            return T(self.A, self.c + o.c)
        c = self.c.copy(); c[0] = c[0] + o
        return T(self.A, c)
    __radd__ = __add__

    def __neg__(self):
        return T(self.A, -self.c)

    def __sub__(self, o):
        return self + (-o)

    def __rsub__(self, o):
        return (-self) + o

    def __mul__(self, o):
        if not isinstance(o, T):
            return T(self.A, self.c * o)
        A = self.A
        res = np.zeros_like(self.c)
        np.add.at(res, A.K, self.c[A.I] * o.c[A.J])
        return T(A, res)
    __rmul__ = __mul__

    def fn(self, f):
        """f = list of Taylor coefficients f^(m)(a0)/m!, m = 0..deg"""
        t = T(self.A, self.c.copy()); t.c[0] = 0
        r = T.const(self.A, f[0])
        p = None
        for m in range(1, self.A.deg + 1):
            p = t if p is None else p * t
            r = r + p * f[m]
        return r

    def inv(self):
        a = self.c[0]
        return self.fn([(-1) ** m / a ** (m + 1) for m in range(self.A.deg + 1)])

    def sqrt(self):
        a = self.c[0]; s = np.sqrt(a)
        co = [s, 0.5 / s, -0.125 / (s * a), 0.0625 / (s * a * a)]
        return self.fn(co[: self.A.deg + 1])

    def sincos(self):
        a = self.c[0]; s, c = np.sin(a), np.cos(a)
        fs = [s, c, -s / 2, -c / 6]; fc = [c, -s, -c / 2, s / 6]
        return self.fn(fs[: self.A.deg + 1]), self.fn(fc[: self.A.deg + 1])

    def atan0(self):
        """atan(t) for t with value 0"""
        return self.fn([np.zeros_like(self.c[0]), 1.0, 0, -1.0 / 3][: self.A.deg + 1])


def kepler_num(l, e):
    E = l + e * np.sin(l)
    for _ in range(14):
        E = E - (E - e * np.sin(E) - l) / (1 - e * np.cos(E))
    return E


def delaunay(l, g, L, G, m):
    A = l.A
    iL = L.inv()
    ratio = G * iL
    e = (1.0 - ratio * ratio).sqrt()
    a = L * L * (1.0 / m ** 2)
    b = iL * (m ** 2)
    E = T.const(A, kepler_num(l.c[0], e.c[0]))
    for _ in range(3):
        sE, cE = E.sincos()
        E = E - (E - e * sE - l) * (1.0 - e * cE).inv()
    sE, cE = E.sincos()
    q1 = a * (cE - e); q2 = a * ratio * sE
    w = b * (1.0 - e * cE).inv()
    p1 = w * (-1.0 * sE); p2 = w * ratio * cE
    sg, cg = g.sincos()
    return cg * q1 - sg * q2, sg * q1 + cg * q2, cg * p1 - sg * p2, sg * p1 + cg * p2


def H_del(z, mu=ST.MU0):
    l1, l2, gh, L1, L2, Gh = z
    A = l1.A
    G2 = ST.GTOT - Gh
    x1, x2, y1, y2 = delaunay(l1, gh, L1, Gh, M1)
    X1, X2, Y1, Y2 = delaunay(l2, T.const(A, np.zeros_like(l2.c[0])), L2, G2, M2)
    d0, d1 = x1 - X1, x2 - X2
    r2 = d0 * d0 + d1 * d1
    ir = r2.sqrt().inv()
    sy0, sy1 = y1 + Y1, y2 + Y2
    H1 = (sy0 * sy0 + sy1 * sy1) * 0.5 - ir * (M1 * M2)
    iL1, iL2 = L1.inv(), L2.inv()
    return iL1 * iL1 * (-0.5 * M1 ** 3) + iL2 * iL2 * (-0.5 * M2 ** 3) + H1 * mu


def H_reg(z, phi, mu=ST.MU0):
    """the regular chart: w5 = sqrt(2 I5), w6 = sqrt(2 I6) e^{i a3} (gauge psi5 = 0), z = Q w, then Delaunay."""
    a1, a2, a3, La1, La2, I6 = z
    A = a1.A
    I5 = La1 + La2 - ST.GTOT - I6
    r5 = (2.0 * I5).sqrt(); r6 = (2.0 * I6).sqrt()
    s3, c3 = a3.sincos()
    w5r, w5i = r5, T.const(A, np.zeros_like(r5.c[0]))
    w6r, w6i = r6 * c3, r6 * s3
    c, s = math.cos(phi), math.sin(phi)
    z1r, z1i = c * w5r - s * w6r, c * w5i - s * w6i
    z2r, z2i = s * w5r + c * w6r, s * w5i + c * w6i

    def polar(xr, xi):
        P = (xr * xr + xi * xi) * 0.5
        th0 = np.angle(xr.c[0] + 1j * xi.c[0]) if not np.iscomplexobj(xr.c[0]) else (-1j * np.log(
            (xr.c[0] + 1j * xi.c[0]) / np.sqrt(xr.c[0] ** 2 + xi.c[0] ** 2)))
        c0, s0 = np.cos(th0), np.sin(th0)
        xr2 = xr * c0 + xi * s0
        xi2 = xi * c0 - xr * s0
        return P, (xi2 * xr2.inv()).atan0() + th0
    P1, p1 = polar(z1r, z1i)
    P2, p2 = polar(z2r, z2i)
    g1, g2 = -1.0 * p1, -1.0 * p2
    l1, l2 = a1 - g1, a2 - g2
    return H_del_full(l1, l2, g1, g2, La1, La2, La1 - P1, La2 - P2, mu)


def H_syn(z, phi, mu=ST.MU0):
    """the synodic regular chart: angles (b1, b2, b3) = (a1 - a2, a2, a2 + a3), actions (Lambda1, I5, I6), Lambda2 eliminated.
    Canonical and unimodular over 'reg'.  I5 and I6 vary by 25 % and 13 % on the torus, so a polydisc in these actions stays
    away from the singular set I5 I6 = 0; in (Lambda1, Lambda2, I6) the fast oscillation of the Lambdas reaches I5 = 0."""
    b1, b2, b3, La1, I5, I6 = z
    return H_reg((b1 + b2, b2, b3 - b2, La1, ST.GTOT + I5 + I6 - La1, I6), phi, mu)


def H_del_full(l1, l2, g1, g2, L1, L2, G1, G2, mu):
    x1, x2, y1, y2 = delaunay(l1, g1, L1, G1, M1)
    X1, X2, Y1, Y2 = delaunay(l2, g2, L2, G2, M2)
    d0, d1 = x1 - X1, x2 - X2
    r2 = d0 * d0 + d1 * d1
    ir = r2.sqrt().inv()
    sy0, sy1 = y1 + Y1, y2 + Y2
    H1 = (sy0 * sy0 + sy1 * sy1) * 0.5 - ir * (M1 * M2)
    iL1, iL2 = L1.inv(), L2.inv()
    return iL1 * iL1 * (-0.5 * M1 ** 3) + iL2 * iL2 * (-0.5 * M2 ** 3) + H1 * mu


def tensors(chart, z, phi=None, deg=3):
    """z: (6, ns) complex points; returns dict of derivative tensors D1 (6, ns), D2 (6,6,ns), D3 (6,6,6,ns)."""
    A = Alg(6, deg)
    v = [T.var(A, z[i], i) for i in range(6)]
    H = H_del(v) if chart == "del" else (H_reg(v, phi) if chart == "reg" else H_syn(v, phi))
    ns = z.shape[1]
    D1 = np.zeros((6, ns), dtype=complex)
    D2 = np.zeros((6, 6, ns), dtype=complex)
    D3 = np.zeros((6, 6, 6, ns), dtype=complex) if deg >= 3 else None
    for e, i in A.idx.items():
        o = sum(e)
        if o == 0:
            continue
        fac = np.prod([math.factorial(x) for x in e])
        ind = [j for j, x in enumerate(e) for _ in range(x)]
        if o == 1:
            D1[ind[0]] = H.c[i]
        elif o == 2:
            for p in set(itertools.permutations(ind)):
                D2[p] = H.c[i] * fac
        elif o == 3:
            for p in set(itertools.permutations(ind)):
                D3[p] = H.c[i] * fac
    return dict(D1=D1, D2=D2, D3=D3)


def majorants(Tn, c, ell):
    """sampled sups in the scaled chart: |X|, |DX|, |D^2 X| (max-norm, row sums), |T_h|."""
    s = np.array([TP] * 3 + [ell] * 3)
    pre = c / (TP * ell)
    D1 = np.abs(Tn["D1"]) * s[:, None] * pre
    D2 = np.abs(Tn["D2"]) * (s[:, None] * s[None, :])[:, :, None] * pre
    M0 = float(D1.max())
    M1_ = float(D2.sum(axis=1).max())
    out = dict(M0=M0, M1=M1_, Mh1=float(D1.max()), Mh2=float(D2.sum(axis=1).max()))
    if Tn["D3"] is not None:
        D3 = np.abs(Tn["D3"]) * (s[:, None, None] * s[None, :, None] * s[None, None, :])[:, :, :, None] * pre
        out["M2"] = float(D3.sum(axis=(1, 2)).max())
    return out


def periodic_data(u, chart):
    """(P, F, phi): P = periodic data (6, grid): angle parts and full actions, F = winding matrix, identity for Delaunay."""
    gr = ST.Grid(u.shape[1:])
    if chart == "del":
        return u.copy(), np.eye(3, dtype=int), None, gr
    R = SPEC.regular_chart(u, gr)
    if chart == "reg":
        return R["P"], R["F"], R["phi"], gr
    a1, a2, a3, L1, L2, I6 = R["P"]
    Fs = np.array([[1, -1, 0], [0, 1, 0], [0, 1, 1]]) @ R["F"]
    return np.stack([a1 - a2, a2, a2 + a3, L1, R["I5"], I6]), Fs, R["phi"], gr


def shifted(P, gr, sig, rho):
    """P(theta + i sig rho), complex; sig in {-1, 1}^3, rho in 2 pi units"""
    C = np.fft.fftn(P, axes=(-3, -2, -1))
    ks = [np.fft.fftfreq(n, 1.0 / n) for n in gr.shape]
    w = 1
    for i in range(3):
        sh = [1, 1, 1]; sh[i] = -1
        w = w * np.exp(-ks[i] * sig[i] * rho).reshape(sh)
    return np.fft.ifftn(C * w, axes=(-3, -2, -1)), C, ks


def tube_points(P, F, gr, rho, marg_ang, marg_act, ns, seed=1):
    """complex sample points of the tube of K over T_rho, enlarged by the margins (random corner phases)."""
    rng = np.random.default_rng(seed)
    pts = []
    th = gr.th
    for sig in itertools.product((-1, 1), repeat=3):
        Q, _, _ = shifted(P, gr, sig, rho)
        id_ = [sum(F[i, j] * (th[j] + 1j * sig[j] * rho) for j in range(3)) for i in range(3)]
        idx = rng.integers(0, Q[0].size, ns // 8)
        z = np.stack([(Q[i].ravel()[idx] + (id_[i].ravel()[idx] if i < 3 else 0)) for i in range(6)])
        ph = np.exp(1j * rng.uniform(0, TP, z.shape))
        z = z + ph * np.array([marg_ang] * 3 + [marg_act] * 3)[:, None]
        pts.append(z)
    return np.concatenate(pts, axis=1)


def box_points(P, F, gr, rho, marg_ang, marg_act, ns, seed=2):
    """complex samples of the polydisc box: T_{rho + iota} x discs around the mean action, radius = half range + margin."""
    rng = np.random.default_rng(seed)
    cen = [P[i].mean() for i in range(3, 6)]
    rad = [0.5 * float(P[i].max() - P[i].min()) + marg_act for i in range(3, 6)]
    iota = 0.0
    for sig in itertools.product((-1, 1), repeat=3):
        Q, _, _ = shifted(P, gr, sig, rho)
        iota = max(iota, float(np.max(np.abs(Q[:3].imag))))
    rh = rho + iota + marg_ang
    ang = rng.uniform(0, TP, (3, ns)) + 1j * rh * rng.choice([-1.0, 1.0], (3, ns))
    # the worst action corners included: boundary of each disc
    act = np.stack([cen[i] + rad[i] * np.exp(1j * rng.uniform(0, TP, ns)) for i in range(3)])
    return np.concatenate([ang, act]), dict(iota=iota, rad=rad, cen=[float(x.real) for x in cen])


def frames_on_strip(P, F, gr, rho, ell):
    """sup over the distinguished boundary of T_rho of the row-sum norms of DK~, DK~^T, B, N, N^T (chart scale ell).
    theta~ primary: DK~ = D K (F^-1), period-1 angle derivative = 2 pi d/dtheta."""
    Fi = np.linalg.inv(F.astype(float))
    res = dict(K=0.0, Lt=0.0, B=0.0, N=0.0, Nt=0.0)
    ks = [np.fft.fftfreq(n, 1.0 / n) for n in gr.shape]
    sh = [(-1, 1, 1), (1, -1, 1), (1, 1, -1)]
    C = np.fft.fftn(P, axes=(-3, -2, -1))
    C[3:, 0, 0, 0] = 0
    I6 = np.eye(6)
    OM = ST.OM
    for sig in itertools.product((-1, 1), repeat=3):
        w = 1
        for i in range(3):
            w = w * np.exp(-ks[i] * sig[i] * rho).reshape(sh[i])
        DK = np.zeros((6, 3) + gr.shape, dtype=complex)
        for j in range(3):
            d = np.fft.ifftn(1j * ks[j].reshape(sh[j]) * C * w, axes=(-3, -2, -1))
            DK[:3, j] = d[:3] * 1.0                                # u/2pi derivative in theta/2pi... = d u / d theta
            DK[3:, j] = d[3:] * TP / ell
        for i in range(3):
            for j in range(3):
                DK[i, j] += F[i, j]
        # reparametrize: primary in theta' = F theta
        DKp = np.einsum("ij...,jk->ik...", DK, Fi)
        Dm = np.moveaxis(DKp, (0, 1), (-2, -1))
        G = np.swapaxes(Dm, -1, -2) @ Dm
        B = np.linalg.inv(G)
        Nm = (OM @ Dm) @ B
        rows = lambda M: float(np.abs(M).sum(axis=-1).max())
        res["K"] = max(res["K"], rows(Dm))
        res["Lt"] = max(res["Lt"], rows(np.swapaxes(Dm, -1, -2)))
        res["B"] = max(res["B"], rows(B))
        res["N"] = max(res["N"], rows(Nm))
        res["Nt"] = max(res["Nt"], rows(np.swapaxes(Nm, -1, -2)))
    return res


def torsion_grid(chart, P, F, phi, gr, step=2, c=1.0, ell=1.0):
    """<T~>, sup |T~| on the real grid (subsampled by step), Hessian by the TPS; returns inverse row norm too."""
    Fi = np.linalg.inv(F.astype(float))
    idx = (slice(None), slice(None, None, step), slice(None, None, step), slice(None, None, step))
    th = [t[::step, ::step, ::step] for t in gr.th]
    Q = P[idx]
    z = np.stack([Q[i] + (sum(F[i, j] * th[j] for j in range(3)) if i < 3 else 0) for i in range(6)])
    shape = z.shape[1:]
    zz = z.reshape(6, -1).astype(complex)
    Tn = tensors(chart, zz, phi, deg=2)
    s = np.array([TP] * 3 + [ell] * 3)
    pre = c / (TP * ell)
    H = (Tn["D2"].real * (s[:, None] * s[None, :])[:, :, None] * pre)     # (6, 6, ns)
    H = np.moveaxis(H, -1, 0)                                             # (ns, 6, 6)
    # DK on the full grid, subsampled
    C = np.fft.fftn(P, axes=(-3, -2, -1)); C[3:, 0, 0, 0] = 0
    ks = [np.fft.fftfreq(n, 1.0 / n) for n in gr.shape]
    sh = [(-1, 1, 1), (1, -1, 1), (1, 1, -1)]
    DK = np.zeros((6, 3) + shape)
    for j in range(3):
        d = np.fft.ifftn(1j * ks[j].reshape(sh[j]) * C, axes=(-3, -2, -1)).real
        DK[:3, j] = d[:3][idx]
        DK[3:, j] = d[3:][idx] * TP / ell
    for i in range(3):
        for j in range(3):
            DK[i, j] += F[i, j]
    DKp = np.einsum("ij...,jk->ik...", DK, Fi)
    Dm = np.moveaxis(DKp, (0, 1), (-2, -1)).reshape(-1, 6, 3)
    G = np.swapaxes(Dm, -1, -2) @ Dm
    B = np.linalg.inv(G)
    OM = ST.OM
    Nm = (OM @ Dm) @ B
    DX = -OM @ H
    W = DX + OM @ DX @ OM
    Tm = np.swapaxes(Nm, -1, -2) @ OM @ W @ Nm
    avg = Tm.mean(axis=0)
    # the bordered (isoenergetic) average [[<T>, omega~], [<Y>, 0]], Y = grad h~ . N; the v2 certifier checks this form
    g = np.moveaxis(Tn["D1"].real * s[:, None] * pre, -1, 0)              # (ns, 6)
    Y = np.einsum("ni,nij->nj", g, Nm).mean(axis=0)
    omt = c * (F @ ST.OMEGA) / TP
    ext = np.zeros((4, 4))
    ext[:3, :3] = avg; ext[:3, 3] = omt; ext[3, :3] = Y
    return dict(Tavg=avg, tinv=float(np.abs(np.linalg.inv(avg)).sum(axis=1).max()),
                tinv_iso=float(np.abs(np.linalg.inv(ext)).sum(axis=1).max()),
                Tsup=float(np.abs(Tm).sum(axis=-1).max()), Th=float(np.abs(W).sum(axis=-1).max()))


def main():
    d = np.load(sys.argv[1])
    u = d["u"]
    # consistency: the TPS against the exact gradient and Hessian of sjs_torus on real points
    gr = ST.Grid(u.shape[1:])
    rng = np.random.default_rng(0)
    th = gr.theta_chart()
    idx = rng.integers(0, u[0].size, 20)
    z = np.stack([(u[i] + (th[i] if i < 3 else 0)).ravel()[idx] for i in range(6)])
    Tn = tensors("del", z.astype(complex), deg=3)
    g, h = ST.grad_hess_slab(z.reshape(6, 20, 1, 1), ST.MU0)
    print("check TPS vs exact: grad %.1e, hess %.1e" % (np.abs(Tn["D1"].real - g[:, :, 0, 0]).max(),
                                                         np.abs(Tn["D2"].real - h[:, :, :, 0, 0]).max()))
    tt = torsion_grid("del", *periodic_data(u, "del")[:3], gr)
    print("Delaunay, c = ell = 1 (2 pi factors as in the theorem's period-1 chart): |<T>^-1| %.4f" % tt["tinv"])
    for chart in ("del", "reg", "syn"):
        P, F, phi, gr = periodic_data(u, chart)
        print("== chart", chart, "F", F.tolist(), "phi", phi)
        for rho in (0.02, 0.05, 0.1):
            for ns in (4000,):
                pts = tube_points(P, F, gr, rho, 1e-3, 1e-5, ns)
                Tt = tensors(chart, pts, phi)
                mt = majorants(Tt, 1.0, 1.0)
                bx, info = box_points(P, F, gr, rho, 1e-3, 1e-5, ns)
                Tb = tensors(chart, bx, phi)
                mb = majorants(Tb, 1.0, 1.0)
                print("rho %.2f tube M0 %.3g M1 %.3g M2 %.3g | box M0 %.3g M1 %.3g M2 %.3g iota %.4f rad %s" % (
                    rho, mt["M0"], mt["M1"], mt["M2"], mb["M0"], mb["M1"], mb["M2"], info["iota"],
                    ["%.2e" % x for x in info["rad"]]), flush=True)


if __name__ == "__main__":
    main()
