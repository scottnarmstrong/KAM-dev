#!/usr/bin/env python3
"""MAG-PILOT producer: one rotational invariant graph of the magnetic field-line model (plan-magnetic-barrier §1).

Untrusted numerical tooling (phase 1 gate), not a certificate.

Model (period-one angles):  H = J + h(p) + V(q, phi),  h(p) = p - 3/4 p^2 + 1/3 p^3 - 1/16 p^4,
  V = eps (cos a + cos b) + kappa eps^2 A^2,  kappa = -h''(p_c)/2 = 1427/3200,  a = 2pi(2q - phi),
  b = 2pi(3q - 2phi),  A = c1 cos a - c2 cos b,  c1 = 32000/2777,  c2 = 96000/7669.
Field lines: q' = h'(p), p' = -V_q, phi' = 1.  Frequency (alpha, 1), alpha = (7913 - sqrt5)/13618 (VL21 (12)).

Unknown: odd periodic u(theta, phi), q = theta + u, p = g(alpha + D u), g = (h')^{-1} near p_c,
D = alpha d_theta + d_phi.  Lagrangian residual  L(u) = D[g(alpha + Du)] + V_q(theta + u, phi)  (= the p row;
the q row vanishes on the grid by construction).  Newton step: Levi-Civita reducibility, w = N W, N = 1 + u_theta,
D[a D W] = -N L, a = N^2 / h''(p)  (exact up to O(L w) terms; all solves diagonal in Fourier).

Stages: `double` (continuation eps 0 -> EPS in double), `hp` (256-bit fixed-point residual via
scripts/spin_orbit/hpfft.py, double-precision scaled corrections), `pad` (finite-candidate residual on a 2x grid).
"""
import os, sys, json, time, math, argparse, resource
from fractions import Fraction as F
os.environ.setdefault("SO_HP_BITS", "256")
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "spin_orbit"))
import numpy as np
import mpmath
from hpfft import P, fft2

EPS = F(3, 2500)
PC = F(7, 20)
KAPPA = F(1427, 3200)
C1, C2 = F(32000, 2777), F(96000, 7669)
RHO = 0.003
CUT = float(os.environ.get('MAG_CUT', '0.6667'))
OUT = "/mnt/HC_Volume_106379410/kam-data/mag"

mpmath.mp.prec = P + 64
ALPHA_MP = (7913 - mpmath.sqrt(5)) / 13618
ALPHA = float(ALPHA_MP)
TWOPI = 2 * math.pi


def hp_(p):            # h'(p)
    return 1 - 1.5 * p + p * p - 0.25 * p ** 3


def hpp(p):            # h''(p)
    return -1.5 + 2 * p - 0.75 * p * p


class Grid:
    def __init__(self, nx, nt, eps=float(EPS)):
        self.nx, self.nt, self.N = nx, nt, nx * nt
        self.eps = eps
        k = np.fft.fftfreq(nx, 1.0 / nx); l = np.fft.fftfreq(nt, 1.0 / nt)
        self.K, self.L = np.meshgrid(k, l, indexing="ij")
        self.mask = np.ones((nx, nt)); self.mask[nx // 2, :] = 0; self.mask[:, nt // 2] = 0
        # candidate support (2/3 dealiasing rule): |k| <= CUT*nx/2, |l| <= CUT*nt/2
        self.cmask = ((np.abs(k)[:, None] <= CUT * nx / 2) & (np.abs(l)[None, :] <= CUT * nt / 2)).astype(float)
        self.dmul = 2j * np.pi * (ALPHA * self.K + self.L)
        self.dinv = np.zeros_like(self.dmul); nz = self.dmul != 0
        self.dinv[nz] = 1 / self.dmul[nz]
        self.dinv *= self.mask
        self.th = (np.arange(nx) / nx)[:, None] * np.ones((1, nt))
        self.ph = np.ones((nx, 1)) * (np.arange(nt) / nt)[None, :]
        self.w = np.exp(TWOPI * RHO * (np.abs(self.K) + np.abs(self.L)))
        self.ni = (-np.arange(nx)) % nx; self.nj = (-np.arange(nt)) % nt

    def fwd(self, f): return np.fft.fft2(f) / self.N
    def inv(self, fh): return np.real(np.fft.ifft2(fh) * self.N)

    def odd(self, fh):
        im = np.imag(fh); im = (im - im[self.ni][:, self.nj]) / 2
        return 1j * im * self.cmask

    def Vq(self, q, ph, eps):
        a = TWOPI * (2 * q - ph); b = TWOPI * (3 * q - 2 * ph)
        Ca, Sa, Cb, Sb = np.cos(a), np.sin(a), np.cos(b), np.sin(b)
        c1, c2, ka = float(C1), float(C2), float(KAPPA)
        A = c1 * Ca - c2 * Cb
        return eps * (-2 * TWOPI * Sa - 3 * TWOPI * Sb) + ka * eps * eps * 2 * A * (-2 * TWOPI * c1 * Sa + 3 * TWOPI * c2 * Sb)

    def ginv(self, y):
        p = np.full(y.shape, float(PC))
        for _ in range(8):
            p = p - (hp_(p) - y) / hpp(p)
        return p

    def state(self, uh):
        u = self.inv(uh); Du = self.inv(self.dmul * uh); ut = self.inv(2j * np.pi * self.K * uh)
        p = self.ginv(ALPHA + Du)
        return u, ut, p

    def residual(self, uh, eps):
        u, ut, p = self.state(uh)
        Lg = self.inv(self.dmul * self.fwd(p) * self.mask) + self.Vq(self.th + u, self.ph, eps)
        return Lg, u, ut, p

    def correction(self, Lg, ut, p):
        """Levi-Civita step for residual grid Lg (scaled to O(1) for double accuracy)."""
        s = np.max(np.abs(Lg)) or 1.0
        Nn = 1 + ut; a = Nn * Nn / hpp(p)
        NL = self.fwd(Nn * Lg / s) * self.mask; NL[0, 0] = 0
        Y = self.inv(-NL * self.dinv)
        c = -np.mean(Y / a) / np.mean(1 / a)
        W = self.inv(self.fwd((Y + c) / a) * self.dinv)
        return self.odd(self.fwd(Nn * W)) * s

    def wnorm(self, fh): return float(np.sum(np.abs(fh) * self.w))


def double_solve(g, steps=6, iters=25, uh=None, eps_list=None, log=print):
    uh = np.zeros((g.nx, g.nt), complex) if uh is None else uh
    prev = None
    for eps in (eps_list or [float(EPS) * (i + 1) / steps for i in range(steps)]):
        if prev is not None:
            pass
        best = None
        for it in range(iters):
            Lg, u, ut, p = g.residual(uh, eps)
            r = g.wnorm(g.fwd(Lg)); m = np.max(np.abs(Lg))
            if best is not None and r > 0.5 * best and it > 3:
                break
            best = r if best is None else min(best, r)
            uh = uh + g.correction(Lg, ut, p)
        log("eps %.6g it %d  sup|L| %.3e  wL %.3e" % (eps, it, m, r))
        prev = uh
    return uh


def pad(uh, nx2, nt2):
    nx, nt = uh.shape
    out = np.zeros((nx2, nt2), dtype=uh.dtype)
    ks = np.fft.fftfreq(nx, 1.0 / nx).astype(int); ls = np.fft.fftfreq(nt, 1.0 / nt).astype(int)
    out[np.ix_(ks % nx2, ls % nt2)] = uh
    return out


# ---------------------------------------------------------------------------------------- fixed point (hp)
ONE = 1 << P


def fx_float(a):
    out = np.empty(a.shape, dtype=object)
    flat = a.ravel(); o = out.ravel()
    for i in range(flat.size):
        m, e = math.frexp(float(flat[i]))
        o[i] = (int(m * (1 << 53)) << (P - 53 + e)) if P - 53 + e >= 0 else int(m * (1 << 53)) >> (53 - P - e)
    return out


def fx_mp(x): return int(mpmath.nint(x * ONE))


def to_float(a):
    return np.array([float(F(int(v), ONE)) if v else 0.0 for v in a.ravel()]).reshape(a.shape)


def zeros_obj(shape):
    z = np.empty(shape, dtype=object); z.fill(0); return z


class HPGrid:
    """256-bit fixed-point evaluation of the residual rows on an nx x nt grid for the finite candidate uh."""

    def __init__(self, nx, nt):
        self.nx, self.nt, self.N = nx, nt, nx * nt
        self.logN = self.N.bit_length() - 1
        k = np.fft.fftfreq(nx, 1.0 / nx).astype(int); l = np.fft.fftfreq(nt, 1.0 / nt).astype(int)
        self.k, self.l = k, l
        two_pi = 2 * mpmath.pi
        # D multiplier 2 pi i (alpha k + l): imaginary part, fixed point
        dk = [fx_mp(two_pi * ALPHA_MP * int(x)) for x in k]; dl = [fx_mp(two_pi * int(x)) for x in l]
        self.dim = np.array([[a + b for b in dl] for a in dk], dtype=object)
        self.twopi = fx_mp(two_pi)
        # grid phases exp(2 pi i (m theta - n phi)) for (m, n) = (2, 1), (3, 2)
        def ph(m, n):
            cr = np.array([fx_mp(mpmath.cos(two_pi * m * j / nx)) for j in range(nx)], dtype=object)
            ci = np.array([fx_mp(mpmath.sin(two_pi * m * j / nx)) for j in range(nx)], dtype=object)
            dr = np.array([fx_mp(mpmath.cos(two_pi * n * j / nt)) for j in range(nt)], dtype=object)
            di = np.array([fx_mp(-mpmath.sin(two_pi * n * j / nt)) for j in range(nt)], dtype=object)
            R = (np.multiply.outer(cr, dr) - np.multiply.outer(ci, di)) >> P
            I = (np.multiply.outer(cr, di) + np.multiply.outer(ci, dr)) >> P
            return R, I
        self.pa = ph(2, 1); self.pb = ph(3, 2)
        self.alpha = fx_mp(ALPHA_MP)
        self.eps = fx_mp(mpmath.mpf(EPS.numerator) / EPS.denominator)
        self.c = {n: fx_mp(mpmath.mpf(v.numerator) / v.denominator) for n, v in
                  dict(c1=C1, c2=C2, ka=KAPPA).items()}

    def ifft_re(self, re, im):
        gr, gi = fft2(re, im, +1)
        return gr

    def fft_n(self, gr):
        Fr, Fi = fft2(gr, zeros_obj(gr.shape), -1)
        return Fr >> self.logN, Fi >> self.logN

    def mul(self, a, b): return (a * b) >> P

    def expi(self, x):
        """exp(i x), x fixed-point real grid (|x| < 2): scaled Taylor + 12 squarings."""
        s = 12
        y = x >> s
        cr = zeros_obj(x.shape) + ONE; ci = zeros_obj(x.shape)
        tr, ti = cr.copy(), ci.copy()
        for n in range(1, 40):
            tr, ti = (-(ti * y) >> P) // n, ((tr * y) >> P) // n
            if not any(tr.ravel()) and not any(ti.ravel()):
                break
            cr = cr + tr; ci = ci + ti
        for _ in range(s):
            cr, ci = (cr * cr - ci * ci) >> P, (2 * cr * ci) >> P
        return cr, ci

    def hprime(self, p):
        p2 = self.mul(p, p); p3 = self.mul(p2, p)
        return ONE - ((3 * p) >> 1) + p2 - (p3 >> 2)

    def hsecond(self, p):
        return -((3 * ONE) >> 1) + 2 * p - ((3 * self.mul(p, p)) >> 2)

    def ginv(self, y, p0):
        p = p0
        for _ in range(4):
            p = p - ((self.hprime(p) - y) << P) // self.hsecond(p)
        return p

    def Vq(self, u):
        Er, Ei = self.expi(self.mul(self.twopi, u))
        E2r, E2i = (Er * Er - Ei * Ei) >> P, (2 * Er * Ei) >> P
        E3r, E3i = (E2r * Er - E2i * Ei) >> P, (E2r * Ei + E2i * Er) >> P
        Ca = (E2r * self.pa[0] - E2i * self.pa[1]) >> P; Sa = (E2r * self.pa[1] + E2i * self.pa[0]) >> P
        Cb = (E3r * self.pb[0] - E3i * self.pb[1]) >> P; Sb = (E3r * self.pb[1] + E3i * self.pb[0]) >> P
        c1, c2, ka, ep, tp = self.c["c1"], self.c["c2"], self.c["ka"], self.eps, self.twopi
        A = (c1 * Ca - c2 * Cb) >> P
        lin = (ep * ((-2 * tp * Sa - 3 * tp * Sb) >> P)) >> P
        dA = ((-2 * tp * c1) >> P) * Sa + ((3 * tp * c2) >> P) * Sb >> P
        quad = (((ka * ep >> P) * ep >> P) * ((2 * A * dA) >> P)) >> P
        return lin + quad

    def rows(self, ure, uim, ph_hat=None, p0=None):
        """ure/uim: fixed-point coefficients of u on this grid.  If ph_hat (p coefficients) is None, p := g(alpha+Du)
        on this grid (solve mode, q row = 0); else p is the trigonometric polynomial ph_hat (candidate mode).
        Returns (Rq_hat, Rp_hat, p_hat) as (re, im) pairs."""
        u = self.ifft_re(ure, uim)
        Du = self.ifft_re(-self.mul(self.dim, uim), self.mul(self.dim, ure))
        y = self.alpha + Du
        if ph_hat is None:
            p = self.ginv(y, p0)
            p_hat = self.fft_n(p)
            Rq = None
        else:
            p_hat = ph_hat
            p = self.ifft_re(*p_hat)
            Rq = self.fft_n(y - self.hprime(p))
        Dp = self.ifft_re(-self.mul(self.dim, p_hat[1]), self.mul(self.dim, p_hat[0]))
        Rp = self.fft_n(Dp + self.Vq(u))
        return Rq, Rp, p_hat, p


def wnorm_fx(g, pair):
    re, im = to_float(pair[0]), to_float(pair[1])
    return float(np.sum(np.hypot(re, im) * g.w)), re + 1j * im


def mask_obj(a, g):
    a = a.copy(); a[g.nx // 2, :] = 0; a[:, g.nt // 2] = 0; return a


def hp_stage(nx, nt, uh, nsteps, log):
    g = Grid(nx, nt); H = HPGrid(nx, nt)
    ure = zeros_obj((nx, nt)); uim = fx_float(np.imag(uh))
    hist = []
    for s in range(nsteps + 1):
        t0 = time.time()
        _, ut, pd = g.state(np.zeros_like(uh) + 1j * to_float(uim))
        _, Rp, p_hat, p = H.rows(ure, uim, p0=fx_float(pd))
        r, Lh = wnorm_fx(g, (mask_obj(Rp[0], g), mask_obj(Rp[1], g)))
        rsup = float(np.max(np.abs(np.real(np.fft.ifft2(Lh) * g.N))))
        log("hp %dx%d step %d  wL %.3e  sup|L| %.3e  (%.0fs)" % (nx, nt, s, r, rsup, time.time() - t0))
        hist.append(dict(step=s, weighted=r, sup=rsup))
        if s == nsteps:
            break
        Lg = np.real(np.fft.ifft2(Lh * g.mask) * g.N)
        dh = g.correction(Lg, ut, pd)
        uim = uim + fx_float(np.imag(dh))
    return uim, p_hat, hist


def pad_obj(a, nx2, nt2):
    nx, nt = a.shape
    out = zeros_obj((nx2, nt2))
    ks = np.fft.fftfreq(nx, 1.0 / nx).astype(int); ls = np.fft.fftfreq(nt, 1.0 / nt).astype(int)
    out[np.ix_(ks % nx2, ls % nt2)] = a
    return out


def candidate_residual(uim, p_hat, nx, nt, fx_, ft_, log):
    """Finite candidate (u, p trig polynomials from the nx x nt solve, Nyquist dropped) on an fx_*nx x ft_*nt grid."""
    g = Grid(nx, nt)
    nx2, nt2 = fx_ * nx, ft_ * nt
    g2 = Grid(nx2, nt2); H2 = HPGrid(nx2, nt2)
    t0 = time.time()
    ui = pad_obj(mask_obj(uim, g), nx2, nt2)
    ph = (pad_obj(mask_obj(p_hat[0], g), nx2, nt2), pad_obj(mask_obj(p_hat[1], g), nx2, nt2))
    Rq, Rp, _, _ = H2.rows(zeros_obj((nx2, nt2)), ui, ph_hat=ph)
    rq, _ = wnorm_fx(g2, Rq); rp, _ = wnorm_fx(g2, Rp)
    log("candidate %dx%d on %dx%d: weighted Rq %.3e  Rp %.3e  (%.0fs)" % (nx, nt, nx2, nt2, rq, rp, time.time() - t0))
    return dict(grid=[nx2, nt2], weighted_q=rq, weighted_p=rp)


def census(g, uim, p_hat):
    uc = np.abs(to_float(uim)); pc = np.hypot(to_float(p_hat[0]), to_float(p_hat[1]))
    out = {}
    for cut in (1e-26, 1e-28, 1e-30, 1e-32):
        keys = ((uc * g.w > cut) | (pc * g.w > cut))
        K, L = g.K[keys], g.L[keys]
        out["%.0e" % cut] = dict(union_keys=int(keys.sum()), maxk=int(np.max(np.abs(K))) if keys.any() else 0,
                                 maxl=int(np.max(np.abs(L))) if keys.any() else 0)
    # edge mass: weighted coefficient mass in the outer quarter of each direction
    m = np.maximum(uc, pc) * g.w
    out["edge_k"] = float(np.sum(m[np.abs(g.K) >= g.nx // 4]))
    out["edge_l"] = float(np.sum(m[np.abs(g.L) >= g.nt // 4]))
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("nx", type=int); ap.add_argument("nt", type=int)
    ap.add_argument("--hp", type=int, default=3, help="hp correction steps")
    ap.add_argument("--seed", default=None, help="npz with a double uh to interpolate from")
    ap.add_argument("--pad", default="2,2")
    a = ap.parse_args()
    t0 = time.time()
    tag = "%dx%d" % (a.nx, a.nt)
    logf = open(os.path.join(OUT, "run-%s.log" % tag), "w")
    def log(s):
        line = "[%7.0fs] %s" % (time.time() - t0, s); print(line, flush=True); logf.write(line + "\n"); logf.flush()
    g = Grid(a.nx, a.nt)
    if a.seed:
        s0 = np.load(a.seed)["uh"]
        uh = double_solve(g, uh=pad(s0, a.nx, a.nt) if s0.shape[0] <= a.nx else None, eps_list=[float(EPS)], log=log)
    else:
        uh = double_solve(g, log=log)
    np.savez(os.path.join(OUT, "double-%s.npz" % tag), uh=uh)
    Lg, u, ut, p = g.residual(uh, float(EPS))
    log("double: flux range [%.9f, %.9f]  min slope 1+u_theta %.9f" % (p.min(), p.max(), (1 + ut).min()))
    uim, p_hat, hist = hp_stage(a.nx, a.nt, uh, a.hp, log)
    np.savez(os.path.join(OUT, "hp-%s.npz" % tag), uim=np.array([str(int(v)) for v in uim.ravel()]),
             pre=np.array([str(int(v)) for v in p_hat[0].ravel()]), shape=np.array([a.nx, a.nt]), P=P)
    res = dict(grid=[a.nx, a.nt], eps=str(EPS), alpha="(7913-sqrt5)/13618", alpha_float=repr(ALPHA), P=P,
               hp=hist, census=census(g, uim, p_hat),
               flux=[float(p.min()), float(p.max())], min_slope=float((1 + ut).min()))
    fx_, ft_ = (int(x) for x in a.pad.split(","))
    if fx_ * ft_ > 1:
        res["candidate"] = candidate_residual(uim, p_hat, a.nx, a.nt, fx_, ft_, log)
    res["seconds"] = time.time() - t0
    res["maxrss_kib"] = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
    log(json.dumps(res))
    json.dump(res, open(os.path.join(OUT, "result-%s.json" % tag), "w"), indent=1)


if __name__ == "__main__":
    main()
