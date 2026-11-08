#!/usr/bin/env python3
"""SJS-X1: FH25's invariant torus in the synodic regular chart, on a grid in an adapted frame, to double-double accuracy.

Untrusted design tooling.  The torus is K(p) = (A p + q(p), act(p)) in the chart of hsyn.py, p in T^3 on an N1 x N2 x N3 grid,
frequency w' = G^-T omega, where theta = G^T p are the angles of SJS-PLAN's coarse torus (sjs_torus.py) and A = Fs G^T is the winding
of the chart's angles.  G is an adapted frame (SJS-PLAN 1.3): the Fourier support of q, act in p is a compact box.
  init:   SJS-PLAN's Delaunay torus (t96.npz) -> chart data on its theta grid (sjs_chart.periodic_data) -> Fourier coefficients
          re-indexed by k' = G k into the p grid.
  newton: FH25's quasi-Newton step at fixed frequency (as sjs_torus.newton, mode 'invariant'), double precision, slab by slab.
  dd:     defect correction.  The state is the DD Fourier coefficients C (exactly zero outside the band); the residual
          E = X_H(K) - D K w' is evaluated in DD (DD inverse FFT, DD gradient of H, DD FFT); the Newton correction is computed
          in double from E and added to C in DD.
Usage:
  x1_torus.py init T96.npz --grid N1 N2 N3 --out S.npz
  x1_torus.py newton S.npz --iters 6 --out S.npz
  x1_torus.py dd S.npz --iters 4 --out S.npz
"""
import argparse, json, math, os, sys, time
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import hsyn as HS
from dd import DD, CDD, fftn as dd_fftn
sys.path.pop(0)

TP = 2 * math.pi
OM = np.block([[np.zeros((3, 3)), -np.eye(3)], [np.eye(3), np.zeros((3, 3))]])
FRAME = np.array([[-1, 0, 1], [-1, -1, 0], [-2, -1, 0]])     # SJS-PLAN 1.3, best frame for the regular chart (k' = G k)
SYN = np.array([[1, -1, 0], [0, 1, 0], [0, 1, 1]])          # b = SYN a


def log(*a):
    print(*a, flush=True)


class Grid:
    def __init__(self, shape, G, Fs, cut=0.45):
        self.shape = tuple(int(n) for n in shape)
        self.G = np.array(G, dtype=int)
        self.Fs = np.array(Fs, dtype=int)
        self.Gi = np.rint(np.linalg.inv(self.G)).astype(int)
        self.A = self.Fs @ self.G.T                           # chart angles = A p + q
        self.omega = self.Gi.T @ HS.OMEGA                     # w' = G^-T omega
        self.n = int(np.prod(self.shape))
        ax = [TP * np.arange(n) / n for n in self.shape]
        self.ax = ax
        self.kf = [np.fft.fftfreq(n, 1.0 / n) for n in self.shape]
        self.kr = self.kf[:2] + [np.fft.rfftfreq(self.shape[2], 1.0 / self.shape[2])]
        kk = np.meshgrid(*self.kr, indexing="ij", sparse=True)
        self.kk = kk
        kw = kk[0] * self.omega[0] + kk[1] * self.omega[1] + kk[2] * self.omega[2]
        self.kw = kw
        with np.errstate(divide="ignore", invalid="ignore"):
            self.Rw = np.where(kw == 0, 0, 1j / np.where(kw == 0, 1, kw))
        self.cutr = (np.abs(kk[0]) <= cut * self.shape[0]) & (np.abs(kk[1]) <= cut * self.shape[1]) & (np.abs(kk[2]) <= cut * self.shape[2])
        kf = np.meshgrid(*self.kf, indexing="ij", sparse=True)
        self.cutf = (np.abs(kf[0]) <= cut * self.shape[0]) & (np.abs(kf[1]) <= cut * self.shape[1]) & (np.abs(kf[2]) <= cut * self.shape[2])

    def f(self, a):
        return np.fft.rfftn(a, axes=(-3, -2, -1))

    def fi(self, a):
        return np.fft.irfftn(a, s=self.shape, axes=(-3, -2, -1))

    def R(self, s):
        return self.fi(self.f(s) * self.Rw)

    def filt(self, a):
        return self.fi(self.f(a) * self.cutr)

    def ident(self, i, j=None):
        """i-th chart angle's identity part (A p)_i on the grid (or on slab j of the first axis)"""
        th = np.meshgrid(*self.ax, indexing="ij", sparse=True)
        v = self.A[i, 0] * th[0] + self.A[i, 1] * th[1] + self.A[i, 2] * th[2]
        return np.broadcast_to(v, self.shape)


def DK_of(gr, u):
    """(6, 3, ...) derivative of the periodic part, plus the identity A on the angle rows"""
    DK = np.empty((6, 3) + gr.shape)
    for c in range(6):                                            # one component at a time (memory)
        U = gr.f(u[c])
        for j in range(3):
            DK[c, j] = gr.fi(1j * gr.kk[j] * U)
        del U
    for i in range(3):
        for j in range(3):
            DK[i, j] += gr.A[i, j]
    return DK


def chart_points(gr, u):
    z = u.reshape(6, -1).copy()
    for i in range(3):
        z[i] += gr.ident(i).reshape(-1)
    return z


def newton_step(gr, u, phi, E=None, slab=None):
    """FH25's quasi-Newton correction du at fixed frequency (sjs_torus.newton, 'invariant'); returns du, info"""
    n = gr.n
    DK = DK_of(gr, u).reshape(6, 3, n)
    uf = u.reshape(6, n)
    ident = [gr.ident(i).reshape(-1) for i in range(3)]
    if E is None:
        E = np.empty((6, n))
        own_E = True
    else:
        E = E.reshape(6, n)
        own_E = False
    T = np.empty((3, 3, n)); etaL = np.empty((3, n)); etaN = np.empty((3, n))
    sl = slab or 32768
    for a in range(0, n, sl):
        s = slice(a, min(n, a + sl))
        z = uf[:, s].copy()
        for i in range(3):
            z[i] += ident[i][s]
        grad, hess = HS.grad_hess(z, phi, chunk=sl)               # slab by slab: the full Hessian is never stored
        if own_E:
            E[:3, s] = grad[3:] - np.einsum("cjn,j->cn", DK[:3, :, s], gr.omega)
            E[3:, s] = -grad[:3] - np.einsum("cjn,j->cn", DK[3:, :, s], gr.omega)
        Dm = np.moveaxis(DK[:, :, s], -1, 0)                      # (m, 6, 3)
        B = np.linalg.inv(np.swapaxes(Dm, -1, -2) @ Dm)
        Nm = (OM @ Dm) @ B
        H = np.moveaxis(hess, -1, 0)
        DX = -OM @ H
        W = DX + OM @ DX @ OM
        Tm = np.swapaxes(Nm, -1, -2) @ OM @ W @ Nm
        T[:, :, s] = np.moveaxis(Tm, 0, -1)
        OE = OM @ np.moveaxis(E[:, s], 0, -1)[..., None]
        etaL[:, s] = np.moveaxis(-(np.swapaxes(Nm, -1, -2) @ OE)[..., 0], 0, -1)
        etaN[:, s] = np.moveaxis((np.swapaxes(Dm, -1, -2) @ OE)[..., 0], 0, -1)
        del grad, hess, H, DX, W, Tm, Nm, B, Dm, OE
    del ident
    err = float(np.max(np.abs(E)))
    del E
    sh = gr.shape
    T = T.reshape((3, 3) + sh); etaL = etaL.reshape((3,) + sh); etaN = etaN.reshape((3,) + sh)
    # component by component and in place (memory): etaN <- R etaN, etaL <- etat = etaL - T R etaN, T <- R (T - <T>)
    for i in range(3):
        etaN[i] = gr.R(etaN[i])
    for i in range(3):
        for j in range(3):
            etaL[i] -= T[i, j] * etaN[j]
    Tavg = T.mean(axis=(-3, -2, -1))
    for i in range(3):
        for j in range(3):
            T[i, j] = gr.R(T[i, j] - Tavg[i, j])
    xi0 = np.linalg.solve(Tavg, etaL.mean(axis=(-3, -2, -1)))
    for i in range(3):
        etaN[i] += xi0[i]                                         # xiN
    for i in range(3):
        etaL[i] = gr.R(etaL[i])
        for j in range(3):
            etaL[i] -= T[i, j] * xi0[j]                           # xiL
    del T
    xiL = etaL.reshape(3, n); xiN = etaN.reshape(3, n)
    du = np.empty((6, n))
    for a in range(0, n, sl):
        s = slice(a, min(n, a + sl))
        Dm = np.moveaxis(DK[:, :, s], -1, 0)
        B = np.linalg.inv(np.swapaxes(Dm, -1, -2) @ Dm)
        Nm = (OM @ Dm) @ B
        du[:, s] = np.moveaxis((Dm @ np.moveaxis(xiL[:, s], 0, -1)[..., None] + Nm @ np.moveaxis(xiN[:, s], 0, -1)[..., None])[..., 0], 0, -1)
    info = dict(err=err, Tinv=float(np.max(np.sum(np.abs(np.linalg.inv(Tavg)), axis=1))), Tavg=Tavg.tolist())
    return du.reshape((6,) + sh), info


# ---- the DD residual --------------------------------------------------------------------------------------------------
def pair_ifft(gr, Ca, Cb):
    """two Hermitian DD coefficient arrays -> two real DD grids (one complex DD inverse FFT)"""
    x = CDD(Ca.re - Cb.im, Ca.im + Cb.re)
    y = dd_fftn(x, sign=1)
    return y.re, y.im


def _rev(d):
    """index map k -> -k on the full lattice"""
    h = d
    for ax in range(-3, 0):
        h = np.roll(np.flip(h, axis=ax), 1, axis=ax)
    return h


def pair_fft(gr, a, b):
    """two real DD grids -> their DD coefficient arrays (normalized by 1/n)"""
    X = dd_fftn(CDD(a, b), sign=-1)
    rev = lambda D: DD(_rev(D.hi), _rev(D.lo))
    Xr, Xi = X.re, X.im
    Rr, Ri = rev(Xr), rev(Xi)
    if gr.n & (gr.n - 1) == 0:                                   # 1/(2n) exact for n a power of two
        sc = lambda v: v * (0.5 / gr.n)
    else:
        sc = lambda v: v / DD(np.full(v.shape, 2.0 * gr.n))
    Ca = CDD(sc(Xr + Rr), sc(Xi - Ri))
    Cb = CDD(sc(Xi + Ri), sc(Rr - Xr))
    return Ca, Cb


def ident_dd(gr):
    """(A p)_i as DD grids, i < 3; p_j = 2 pi m / N_j in DD"""
    import mpmath
    out = []
    axes = []
    for nj in gr.shape:
        vals = [mpmath.mpf(2) * mpmath.pi * m / nj for m in range(nj)]
        hi = np.array([float(v) for v in vals]); lo = np.array([float(v - float(v)) for v in vals])
        axes.append(DD(hi, lo))
    for i in range(3):
        acc = DD(np.zeros(gr.shape))
        for j in range(3):
            if gr.A[i, j] == 0:
                continue
            shp = [1, 1, 1]; shp[j] = gr.shape[j]
            a = DD(np.broadcast_to(axes[j].hi.reshape(shp), gr.shape).copy(), np.broadcast_to(axes[j].lo.reshape(shp), gr.shape).copy())
            acc = acc + a * float(gr.A[i, j])
        out.append(acc)
    return out


def kw_dd(gr):
    """k'.w' on the full lattice in DD, w' = G^-T omega with omega in DD from FH's digits"""
    om = HS.omega_dd()
    wp = []
    for i in range(3):
        acc = DD(np.float64(0.0))
        for j in range(3):
            acc = acc + om[j] * float(gr.Gi.T[i, j])
        wp.append(acc)
    kf = np.meshgrid(*gr.kf, indexing="ij")
    out = DD(np.zeros(gr.shape))
    for i in range(3):
        out = out + DD(np.broadcast_to(wp[i].hi, gr.shape) * 0 + wp[i].hi, np.broadcast_to(wp[i].lo, gr.shape) * 0 + wp[i].lo) * kf[i]
    return out, wp


def residual_dd(gr, C, phi, ID=None, KW=None):
    """C: list of 6 CDD coefficient arrays -> (E coefficients as 6 CDD, K grids as 6 DD)"""
    t0 = time.time()
    if ID is None:
        ID = ident_dd(gr)
    if KW is None:
        KW = kw_dd(gr)
    kw, wp = KW
    Kg = []
    for c in (0, 2, 4):
        a, b = pair_ifft(gr, C[c], C[c + 1])
        Kg += [a, b]
    t1 = time.time()
    for i in range(3):
        Kg[i] = Kg[i] + ID[i]
    zf = [DD(x.hi.reshape(-1), x.lo.reshape(-1)) for x in Kg]
    del Kg
    g = HS.grad_dd(zf, phi)
    del zf
    t2 = time.time()
    XH = [g[3], g[4], g[5], -g[0], -g[1], -g[2]]
    XH = [DD(x.hi.reshape(gr.shape), x.lo.reshape(gr.shape)) for x in XH]
    del g
    E = []
    for c in (0, 2, 4):
        Ea, Eb = pair_fft(gr, XH[c], XH[c + 1])
        XH[c] = XH[c + 1] = None
        E += [Ea, Eb]
    del XH
    # minus D K w': i k'.w' C_k on the periodic part, and A w' at k = 0 for the angles
    Aw = [sum((wp[j] * float(gr.A[i, j]) for j in range(3)), DD(np.float64(0.0))) for i in range(3)]
    for c in range(6):
        dre = -(C[c].im * kw)        # i kw (re + i im) = -kw im + i kw re
        dim = C[c].re * kw
        E[c] = CDD(E[c].re - dre, E[c].im - dim)
        if c < 3:                    # E_0 = <X_H> - A w' for the angles
            e0 = E[c].re[0, 0, 0] - Aw[c]
            E[c].re.hi[0, 0, 0] = e0.hi
            E[c].re.lo[0, 0, 0] = e0.lo
    t3 = time.time()
    return E, None, (t1 - t0, t2 - t1, t3 - t2)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("mode", choices=["init", "newton", "dd"])
    ap.add_argument("src")
    ap.add_argument("--grid", type=int, nargs=3)
    ap.add_argument("--out")
    ap.add_argument("--iters", type=int, default=4)
    ap.add_argument("--cut", type=float, default=0.45)
    a = ap.parse_args()
    t0 = time.time()
    if a.mode == "init":
        sys.path.insert(0, os.path.join(HERE, "..", "plan"))
        import sjs_chart as SC
        sys.path.pop(0)
        d = np.load(a.src)
        P, Fs, phi, gr0 = SC.periodic_data(d["u"], "syn")
        Fs = np.array(Fs, dtype=int)
        log("synodic winding Fs", Fs.tolist(), "det", round(np.linalg.det(Fs)), "phi", phi)
        sh0 = P.shape[1:]
        C0 = np.fft.fftn(P, axes=(-3, -2, -1)) / np.prod(sh0)
        k0 = np.meshgrid(*[np.fft.fftfreq(n, 1.0 / n) for n in sh0], indexing="ij")
        kp = np.einsum("ij,j...->i...", FRAME, np.stack(k0)).astype(int)
        gr = Grid(a.grid, FRAME, Fs, a.cut)
        Cn = np.zeros((6,) + gr.shape, dtype=complex)
        ok = np.ones(sh0, dtype=bool)
        for i in range(3):
            ok &= np.abs(kp[i]) <= a.cut * gr.shape[i]
        idx = tuple(np.mod(kp[i][ok], gr.shape[i]) for i in range(3))
        lost = 0.0
        for c in range(6):
            Cn[c][idx] = C0[c][ok]
            lost = max(lost, float(np.abs(C0[c][~ok]).max() / max(np.abs(C0[c].reshape(-1)[1:]).max(), 1e-300)))
        u = np.real(np.fft.ifftn(Cn * gr.n, axes=(-3, -2, -1)))
        log("re-indexed %d coefficients into the p grid %s; largest dropped (relative per component) %.2e" % (ok.sum(), gr.shape, lost))
        np.savez(a.out, u=u, G=FRAME, Fs=Fs, phi=phi, grid=np.array(gr.shape), cut=a.cut)
        return
    d = np.load(a.src)
    G, Fs, phi = d["G"], d["Fs"], float(d["phi"])
    shape = tuple(int(x) for x in d["grid"])
    if a.grid and tuple(a.grid) != shape:
        U = np.fft.fftn(d["u"], axes=(-3, -2, -1)) / np.prod(shape)
        new = tuple(a.grid)
        Un = np.zeros((6,) + new, dtype=complex)
        kf = np.meshgrid(*[np.fft.fftfreq(n, 1.0 / n) for n in shape], indexing="ij")
        ok = np.ones(shape, dtype=bool)
        for i in range(3):
            ok &= np.abs(kf[i]) < new[i] / 2
        idx = tuple(np.mod(kf[i][ok].astype(int), new[i]) for i in range(3))
        for c in range(6):
            Un[c][idx] = U[c][ok]
        u = np.real(np.fft.ifftn(Un * np.prod(new), axes=(-3, -2, -1)))
        shape = new
        log("regridded to", shape)
    else:
        u = d["u"]
    gr = Grid(shape, G, Fs, a.cut)
    hist = []
    if a.mode == "newton":
        for it in range(a.iters):
            du, info = newton_step(gr, u, phi)
            u = gr.filt(u + du)
            log("newton %d err %.3e du %.2e |T^-1| %.3f <I5> %.10f t %.0f" % (it, info["err"], np.abs(du).max(), info["Tinv"],
                                                                             u[4].mean(), time.time() - t0))
            hist.append(dict(it=it, err=info["err"], du=float(np.abs(du).max()), Tinv=info["Tinv"]))
        np.savez(a.out, u=u, G=G, Fs=Fs, phi=phi, grid=np.array(gr.shape), cut=a.cut, hist=json.dumps(hist))
        return
    raise SystemExit("dd mode: see x1_dd.py")


if __name__ == "__main__":
    main()
