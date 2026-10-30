#!/usr/bin/env python3
"""LOCK-GEN (D45): the N-th noble librational torus (default N = 65, omega = 1/(N+g), g = (sqrt5-1)/2) of the
seven-term model in high precision, and its embedding K(theta) = (theta1 + U(theta), P(theta)) in exact elliptic
polar coordinates (alpha, I) x clock around a rational centre c(phi).  Untrusted tooling: design numbers only.

Stage A (double).  V = 2 pi psi on T^2, odd, Galerkin on the half diamond S = {|k|/K + |l|/L <= 1} in the sine basis
s_kl = sin 2 pi (k theta1 + l theta2):  R(V) = Dt^2 V + 2 eps sum_m A_m sin(2 pi (2-m) theta2 + 2 V),
Dt = omega d1 + d2 (index units).  Jacobian J[lam, kap] = -(omega k + l)^2 delta + chat(lam-kap) - chat(lam+kap),
c = dR/dV.  Bordered continuation in the amplitude b_(1,0) from the periodic orbit to omega = 1/(N+g), then a
fixed-omega Newton.
Stage B (high precision, hpsolve style).  Fixed-point (SO_HP_BITS) residual on an nx x nt grid, chord iteration with
the double LU of J.  Reported: max |Rhat| projected to S and over all grid modes (the truncation residual).
Stage C (polar).  X = psi - c(phi), Y = (p-1) - c'(phi), I = pi (Om X^2 + Y^2/Om),
alpha = atan2(sqrt(Om) X, Y/sqrt(Om)) / 2pi, U = alpha - theta1, P = I on the grid (mp), Fourier data of (U, P),
truncation to the smallest rectangle |k| <= Ks, |l| <= Ls keeping the dropped tail below TAIL, and the residual of the
TRUNCATED polar embedding of the flow
    psi' = p - 1,  p' = -4 pi eps sum_m A_m sin 2 pi (2 psi + (2-m) phi),  phi' = 1:
    E_alpha = omega + Dt U - (X' Y - X Y') / (2 pi (Om X^2 + Y^2/Om)),  E_I = Dt P - 2 pi (Om X X' + Y Y'/Om),
with X' = Y, Y' = psi'' - c''.  Om is chosen (rational, by a double scan) to minimise (max P - min P) / mean P.

    SO_HP_BITS=192 python3 lock_hp.py OUTDIR [N=65] [K=160] [L=40] [nx=512] [nt=128] [iters=12]
"""
import os, sys, json, time, math, pickle
from fractions import Fraction as F
import numpy as np
import mpmath as mp
from model import A_EXACT, EPS

Ad = {m: float(a) for m, a in A_EXACT.items()}
epsd = float(EPS)
SH = {m: 2 - m for m in Ad}                     # theta2 shift of the forcing characters
CENTRE = [F(-3, 250000), F(-699, 2000000000), F(-883, 50000000000)]   # lock_po.py, L = 3, rel 1e-3 (psi, turns)
TAIL = 1e-38


def log(*a):
    print(*a, flush=True)


class Gal:
    """Double-precision Galerkin model on the half diamond."""

    def __init__(self, K, L, nx, nt):
        self.K, self.L, self.nx, self.nt = K, L, nx, nt
        idx = [(k, l) for k in range(0, K + 1) for l in range(-L, L + 1)
               if (k > 0 or l > 0) and abs(k) / K + abs(l) / L <= 1]
        self.idx = idx
        self.k = np.array([a for a, _ in idx]); self.l = np.array([b for _, b in idx])
        self.pos = {kl: i for i, kl in enumerate(idx)}
        self.t1 = np.arange(nx)[:, None] / nx; self.t2 = np.arange(nt)[None, :] / nt

    def vhat(self, b):
        vh = np.zeros((self.nx, self.nt), complex)
        vh[self.k % self.nx, self.l % self.nt] = b / 2j
        vh[-self.k % self.nx, -self.l % self.nt] = -b / 2j
        return vh

    def grid(self, b):
        return np.real(np.fft.ifft2(self.vhat(b))) * self.nx * self.nt

    def sine(self, f):
        fh = np.fft.fft2(f) / (self.nx * self.nt)
        return -2 * np.imag(fh[self.k % self.nx, self.l % self.nt])

    def sym(self, om):
        return om * self.k + self.l

    def resid(self, b, om):
        V = self.grid(b)
        g = sum(2 * epsd * Ad[m] * np.sin(2 * np.pi * SH[m] * self.t2 + 2 * V) for m in Ad)
        return -self.sym(om) ** 2 * b + self.sine(g), V

    def jac(self, V, om):
        c = sum(4 * epsd * Ad[m] * np.cos(2 * np.pi * SH[m] * self.t2 + 2 * V) for m in Ad)
        ch = np.real(np.fft.fft2(c)) / (self.nx * self.nt)
        k, l = self.k, self.l
        J = ch[(k[:, None] - k[None, :]) % self.nx, (l[:, None] - l[None, :]) % self.nt] \
            - ch[(k[:, None] + k[None, :]) % self.nx, (l[:, None] + l[None, :]) % self.nt]
        J[np.diag_indices_from(J)] -= self.sym(om) ** 2
        return J

    def transfer(self, other, b):
        nb = np.zeros(len(self.idx))
        for i, kl in enumerate(other.idx):
            j = self.pos.get(kl)
            if j is not None:
                nb[j] = b[i]
        return nb


def newton_fixed(G, b, om, tol=1e-14, it=20):
    for i in range(it):
        R, V = G.resid(b, om)
        r = np.max(np.abs(R))
        if r < tol:
            break
        b = b - np.linalg.solve(G.jac(V, om), R)
    return b, r


def continuation(G, om_target, b0):
    """Bordered Newton in the amplitude a = b_(1,0), secant predictor, stop past om_target."""
    i10 = G.pos[(1, 0)]
    om = 0.0261687
    b = b0.copy()
    hist = []
    a, da = 0.05, 0.05
    b[i10] = a
    while True:
        for _ in range(30):
            R, V = G.resid(b, om)
            J = G.jac(V, om)
            dRo = -2 * G.k * G.sym(om) * b
            n = len(b)
            B = np.zeros((n + 1, n + 1)); B[:n, :n] = J; B[:n, n] = dRo; B[n, i10] = 1
            rhs = np.concatenate([R, [b[i10] - a]])
            d = np.linalg.solve(B, rhs)
            b = b - d[:n]; om = om - d[n]
            if np.max(np.abs(R)) < 1e-13:
                break
        hist.append((a, om, b.copy()))
        log("  cont a=%.3f omega=%.8f 1/om-g=%.3f res=%.1e" % (a, om, 1 / om - (math.sqrt(5) - 1) / 2,
                                                              np.max(np.abs(R))))
        if om < om_target:
            break
        if len(hist) >= 2:   # secant predictor
            (a1, o1, b1), (a2, o2, b2) = hist[-2], hist[-1]
            b = b2 + (b2 - b1); om = o2 + (o2 - o1)
        a += da
        b[i10] = a
    (a1, o1, b1), (a2, o2, b2) = hist[-2], hist[-1]
    t = (om_target - o1) / (o2 - o1)
    return b1 + t * (b2 - b1)


# ---------------------------------------------------------------- high precision
def hp_setup(bits):
    os.environ.setdefault("SO_HP_BITS", str(bits))
    import hpfft
    return hpfft


def omega_mp(N):
    A = 2 * N - 1
    D = (A * A - 5) // 2
    return (mp.mpf(A) - mp.sqrt(5)) / D


class HPT:
    def __init__(self, G, N, hpfft):
        self.G, self.f = G, hpfft
        P = hpfft.P
        self.P = P
        mp.mp.prec = P + 80
        self.om = omega_mp(N)
        nx, nt = G.nx, G.nt
        self.logN = (nx * nt).bit_length() - 1
        kk = np.fft.fftfreq(nx, 1.0 / nx).astype(int); ll = np.fft.fftfreq(nt, 1.0 / nt).astype(int)
        self.kk, self.ll = kk, ll
        self.mult = np.empty((nx, nt), dtype=object)
        self.dmul = np.empty((nx, nt), dtype=object)
        for a in range(nx):
            for c in range(nt):
                d = self.om * int(kk[a]) + int(ll[c])
                self.mult[a, c] = -int(mp.nint(d * d * 2 ** P))
                self.dmul[a, c] = int(mp.nint(d * 2 ** P))
        self.coef = {m: self.fx(2 * EPS * A_EXACT[m]) for m in Ad}

    def fx(self, fr):
        P = self.P
        fr = F(fr)
        return (fr.numerator << P) // fr.denominator if fr >= 0 else -((-fr.numerator << P) // fr.denominator)

    def vim_from_b(self, bfx):
        """bfx: list of fixed-point ints (sine coefficients on S) -> vhat imaginary part array."""
        G = self.G
        vim = self.f.zeros((G.nx, G.nt))
        for (k, l), v in zip(G.idx, bfx):
            vim[k % G.nx, l % G.nt] = -(v >> 1)
            vim[-k % G.nx, -l % G.nt] = v >> 1
        return vim

    def expj2(self, gr):
        P = self.P
        er = np.empty(gr.shape, dtype=object); ei = np.empty(gr.shape, dtype=object)
        sc = mp.mpf(2) ** (1 - P)
        for i in np.ndindex(gr.shape):
            z = mp.expj(int(gr[i]) * sc)
            er[i] = int(mp.nint(z.real * 2 ** P)); ei[i] = int(mp.nint(z.imag * 2 ** P))
        return er, ei

    def residual_hat(self, vim):
        P, f = self.P, self.f
        z = f.zeros(vim.shape)
        gr, _ = f.fft2(z, vim, +1)
        er, ei = self.expj2(gr)
        Fr, Fi = f.fft2(er, ei, -1)
        Fr = Fr >> self.logN; Fi = Fi >> self.logN
        refl = lambda a: np.roll(np.flip(a, (0, 1)), 1, axis=(0, 1))
        Rr = z.copy(); Ri = (self.mult * vim) >> P
        Frr, Fir = refl(Fr), refl(Fi)
        for m, sl in SH.items():
            a_r = np.roll(Fr, (0, sl), axis=(0, 1)); a_i = np.roll(Fi, (0, sl), axis=(0, 1))
            b_r = np.roll(Frr, (0, -sl), axis=(0, 1)); b_i = np.roll(Fir, (0, -sl), axis=(0, 1))
            qr = (a_i + b_i) >> 1; qi = -((a_r - b_r) >> 1)
            c = self.coef[m]
            Rr = Rr + ((c * qr) >> P); Ri = Ri + ((c * qi) >> P)
        return Rr, Ri

    def lg(self, x):
        return float(mp.log10(mp.mpf(abs(int(x))) / 2 ** self.P)) if x else -999.0

    def run(self, b, iters, tol=-45):
        G, P = self.G, self.P
        bfx = [int(v * 2 ** 53) << (P - 53) for v in b]
        R, V = G.resid(b, float(self.om))
        lu = __import__("scipy.linalg", fromlist=["lu_factor"])
        LU = lu.lu_factor(G.jac(V, float(self.om)))
        hist = []
        t0 = time.time()
        for it in range(iters):
            vim = self.vim_from_b(bfx)
            Rr, Ri = self.residual_hat(vim)
            rS = [-2 * int(Ri[k % G.nx, l % G.nt]) for (k, l) in G.idx]   # sine coefficients on S
            mS = max(abs(x) for x in rS)
            mall = max(max(abs(int(x)) for x in Rr.ravel()), max(abs(int(x)) for x in Ri.ravel()))
            hist.append((it, self.lg(mS), self.lg(mall), round(time.time() - t0)))
            log("  hp it=%d log10 max|R_S|=%.2f max|Rhat_all|=%.2f t=%.0fs" % hist[-1])
            if self.lg(mS) < tol or it == iters - 1:
                break
            e = max(mS.bit_length() - 60, 0)
            rd = np.array([float(x >> e) for x in rS])
            d = lu.lu_solve(LU, rd)
            bfx = [v - (int(x) << e) for v, x in zip(bfx, np.rint(d))]
        self.Rr, self.Ri = Rr, Ri
        return bfx, hist


# ---------------------------------------------------------------- polar
def polar_double(G, b, om, Om):
    V = G.grid(b)
    psi = V / (2 * np.pi)
    vh = G.vhat(b)
    k = np.fft.fftfreq(G.nx, 1.0 / G.nx)[:, None]; l = np.fft.fftfreq(G.nt, 1.0 / G.nt)[None, :]
    pm1 = np.real(np.fft.ifft2(1j * (om * k + l) * vh)) * G.nx * G.nt   # Dt V = dpsi/dt = p - 1
    cc = sum(float(c) * np.sin(2 * np.pi * (j + 1) * G.t2) for j, c in enumerate(CENTRE))
    dc = sum(float(c) * 2 * np.pi * (j + 1) * np.cos(2 * np.pi * (j + 1) * G.t2) for j, c in enumerate(CENTRE))
    X = psi - cc; Y = pm1 - dc
    I = np.pi * (Om * X ** 2 + Y ** 2 / Om)
    return X, Y, I


def main(argv):
    out = argv[0]
    N = int(argv[1]) if len(argv) > 1 else 65
    K = int(argv[2]) if len(argv) > 2 else 160
    L = int(argv[3]) if len(argv) > 3 else 40
    nx = int(argv[4]) if len(argv) > 4 else 512
    nt = int(argv[5]) if len(argv) > 5 else 128
    iters = int(argv[6]) if len(argv) > 6 else 12
    bits = int(os.environ.get("SO_HP_BITS", "192"))
    os.makedirs(out, exist_ok=True)
    T = {}
    t0 = time.time()
    g = (math.sqrt(5) - 1) / 2
    omt = 1 / (N + g)
    # ---- stage A
    G0 = Gal(80, 20, 256, 64)
    b0 = np.zeros(len(G0.idx))
    cache = f"{out}/A_N{N}_K{K}_L{L}.npy"
    G = Gal(K, L, nx, nt)
    log("stage A: |S| = %d (coarse %d)" % (len(G.idx), len(G0.idx)))
    if os.path.exists(cache):
        b = np.load(cache)
    else:
        bc = continuation(G0, omt, b0)
        bc, r = newton_fixed(G0, bc, omt)
        log("  coarse fixed-omega residual %.1e" % r)
        b, r = newton_fixed(G, G.transfer(G0, bc), omt)
        log("  fine fixed-omega residual %.1e" % r)
        np.save(cache, b)
    T["A"] = time.time() - t0
    # double polar scan of Om
    X, Y, _ = polar_double(G, b, omt, 1.0)
    best = None
    for Om in np.linspace(0.05, 0.4, 351):
        I = np.pi * (Om * X ** 2 + Y ** 2 / Om)
        q = (I.max() - I.min()) / I.mean()
        if best is None or q < best[0]:
            best = (q, Om)
    Omr = F(best[1]).limit_denominator(100)
    log("  roundest Om = %.4f (spread %.3f) -> rational %s; psi amplitude %.2f deg, max|Y| %.4f" % (
        best[1], best[0], Omr, 360 * np.max(np.abs(X)), np.max(np.abs(Y))))
    # ---- stage B
    hpfft = hp_setup(bits)
    H = HPT(G, N, hpfft)
    T["setup"] = time.time() - t0
    bfx, hist = H.run(b, iters)
    T["B"] = time.time() - t0
    pickle.dump(dict(idx=G.idx, bfx=bfx, P=H.P, N=N, hist=hist), open(f"{out}/B_N{N}_K{K}_L{L}.pkl", "wb"))
    # ---- stage C (polar, mp on the grid)
    P = H.P
    f = hpfft
    vim = H.vim_from_b(bfx)
    z = f.zeros(vim.shape)
    vg, _ = f.fft2(z, vim, +1)                              # V on grid
    dr, _ = f.fft2(-((H.dmul * vim) >> P), z, +1)            # Dt V = i d Vhat -> re part -d*vim
    Om = mp.mpf(Omr.numerator) / Omr.denominator
    sc = mp.mpf(2) ** (-P)
    twopi = 2 * mp.pi
    Ug = np.empty((nx, nt), dtype=object); Pg = np.empty((nx, nt), dtype=object)
    Imin, Imax, Xmax, Ymax = mp.inf, -mp.inf, 0, 0
    cen = [mp.mpf(c.numerator) / c.denominator for c in CENTRE]
    for a in range(nx):
        for c in range(nt):
            ph = mp.mpf(c) / nt
            cc = mp.fsum(cj * mp.sinpi(2 * (j + 1) * ph) for j, cj in enumerate(cen))
            dc = mp.fsum(cj * twopi * (j + 1) * mp.cospi(2 * (j + 1) * ph) for j, cj in enumerate(cen))
            X = int(vg[a, c]) * sc / twopi - cc
            Y = int(dr[a, c]) * sc - dc
            I = mp.pi * (Om * X ** 2 + Y ** 2 / Om)
            al = mp.atan2(mp.sqrt(Om) * X, Y / mp.sqrt(Om)) / twopi
            U = al - mp.mpf(a) / nx
            U = U - mp.nint(U)
            Ug[a, c] = int(mp.nint(U * 2 ** P)); Pg[a, c] = int(mp.nint(I * 2 ** P))
            Imin, Imax = min(Imin, I), max(Imax, I)
            Xmax, Ymax = max(Xmax, abs(X)), max(Ymax, abs(Y))
    T["polar_grid"] = time.time() - t0
    logN = H.logN
    Uhr, Uhi = f.fft2(Ug, z, -1); Phr, Phi = f.fft2(Pg, z, -1)
    Uhr, Uhi, Phr, Phi = [x >> logN for x in (Uhr, Uhi, Phr, Phi)]
    kk, ll = H.kk, H.ll
    mag = np.vectorize(lambda r, i: max(abs(int(r)), abs(int(i))), otypes=[object])
    MU = mag(Uhr, Uhi); MP = mag(Phr, Phi)
    lgv = np.vectorize(lambda x: H.lg(x), otypes=[float])
    LU_, LP_ = lgv(MU), lgv(MP)
    decK = {int(k): float(max(LU_[kk == k].max(), LP_[kk == k].max())) for k in range(0, nx // 2)}
    decL = {int(l): float(max(LU_[:, ll == l].max(), LP_[:, ll == l].max())) for l in range(0, nt // 2)}
    # smallest rectangle with dropped tail sum below TAIL (sum over dropped |coef|, U and P)
    tot = lambda Ks, Ls: sum(10 ** v for arr in (LU_, LP_) for v in arr[(np.abs(kk)[:, None] > Ks) |
                                                                       (np.abs(ll)[None, :] > Ls)])
    Ks = next((k for k in range(1, nx // 2) if decK[k] < math.log10(TAIL) - 2), nx // 2 - 1)
    Ls = next((l for l in range(1, nt // 2) if decL[l] < math.log10(TAIL) - 2), nt // 2 - 1)
    while tot(Ks, Ls) > TAIL and Ks < nx // 2 - 1:
        Ks += 2; Ls = min(Ls + 1, nt // 2 - 1)
    tail = tot(Ks, Ls)
    keep = (np.abs(kk)[:, None] <= Ks) & (np.abs(ll)[None, :] <= Ls)
    nz = int(np.sum(keep & ((MU > 0) | (MP > 0))))
    # residual of the truncated polar embedding on the grid
    mk = lambda arr: np.where(keep, arr, 0).astype(object)
    Ur, Ui, Pr_, Pi_ = mk(Uhr), mk(Uhi), mk(Phr), mk(Phi)
    Ut, _ = f.fft2(Ur, Ui, +1); Pt, _ = f.fft2(Pr_, Pi_, +1)
    DUt, _ = f.fft2(-((H.dmul * Ui) >> P), (H.dmul * Ur) >> P, +1)
    DPt, _ = f.fft2(-((H.dmul * Pi_) >> P), (H.dmul * Pr_) >> P, +1)
    # Dt in index units: d/dt = 2 pi Dt
    eps = mp.mpf(EPS.numerator) / EPS.denominator
    Am = {m: mp.mpf(a.numerator) / a.denominator for m, a in A_EXACT.items()}
    Ea, EI = mp.mpf(0), mp.mpf(0)
    for a in range(nx):
        for c in range(nt):
            ph = mp.mpf(c) / nt
            al = mp.mpf(a) / nx + int(Ut[a, c]) * sc
            I = int(Pt[a, c]) * sc
            X = mp.sqrt(I / (mp.pi * Om)) * mp.sinpi(2 * al); Y = mp.sqrt(I * Om / mp.pi) * mp.cospi(2 * al)
            cc = mp.fsum(cj * mp.sinpi(2 * (j + 1) * ph) for j, cj in enumerate(cen))
            d2c = -mp.fsum(cj * (twopi * (j + 1)) ** 2 * mp.sinpi(2 * (j + 1) * ph) for j, cj in enumerate(cen))
            psi = X + cc
            psidd = -4 * mp.pi * eps * mp.fsum(Am[m] * mp.sinpi(2 * (2 * psi + (2 - m) * ph)) for m in Am)
            Xd, Yd = Y, psidd - d2c
            ea = H.om + twopi * int(DUt[a, c]) * sc - (Xd * Y - X * Yd) / (Om * X ** 2 + Y ** 2 / Om) / twopi
            eI = twopi * int(DPt[a, c]) * sc - twopi * (Om * X * Xd + Y * Yd / Om)
            Ea, EI = max(Ea, abs(ea)), max(EI, abs(eI))
    T["polar_resid"] = time.time() - t0
    # Units: alpha, U in turns, t in orbital periods (d/dt = 2 pi Dt); E_alpha in turns per period, E_I in action
    # units per period.
    rec = dict(N=N, omega=mp.nstr(H.om, 30), K=K, L=L, S_size=len(G.idx), grid=[nx, nt], bits=P,
               hp_hist=hist, Om=str(Omr), Om_double=best[1], spread=best[0],
               psi_amp_deg=float(360 * Xmax), max_abs_Y=float(Ymax),
               I_min=mp.nstr(Imin, 10), I_max=mp.nstr(Imax, 10),
               decay_k=decK, decay_l=decL, support=dict(Ks=Ks, Ls=Ls, tail=tail, nonzero_coeffs=nz),
               polar_resid_sup=dict(E_alpha=mp.nstr(Ea, 5), E_I=mp.nstr(EI, 5)),
               centre=[str(c) for c in CENTRE], times=T)
    json.dump(rec, open(f"{out}/lock_N{N}_K{K}_L{L}.json", "w"), indent=1)
    log(json.dumps({k: v for k, v in rec.items() if k not in ("decay_k", "decay_l", "hp_hist")}, indent=1))
    log("decay_k (every 10):", {k: round(v, 1) for k, v in decK.items() if k % 10 == 0})
    log("decay_l (every 4):", {k: round(v, 1) for k, v in decL.items() if k % 4 == 0})


if __name__ == "__main__":
    main(sys.argv[1:])
