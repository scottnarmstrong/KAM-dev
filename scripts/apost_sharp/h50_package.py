#!/usr/bin/env python3
"""Benchmark package H50: the lower lunar rotational torus nu = 1 - 1/(50+g), rotated frame, double precision.

Untrusted tooling, heuristic (double precision, sampled sups, not enclosures).  H50 is the harder companion of package
R1 (CONSTANTS-STUDY section 2.2; scripts/apost_sharp/r1_norms.py): the same seven-term model (eps = 69/200000,
e = 0.0549, scripts/spin_orbit/model.py), the barrier frequency moved from 1 - 1/(40+g) to 1 - 1/(50+g),
g = (sqrt5-1)/2, closer to the synchronous separatrix (docs/explorations/lunar-band-2p8-2p9.md).  Steps:

 1. Torus.  Odd v = sum_{(k,l) in H} b_kl sin(2 pi (k psi + l phi)) on the half box H = {0 <= k <= K even, |l| <= Lm},
    solving the pi-free invariance equation R(v) = Dt^2 v + 2 eps sum_m A_m sin(2 pi (2 psi + (2-m) phi) + 2 v) = 0,
    Dt e_kl = i((nu-1) k + l) e_kl (model.py), by Galerkin-Newton with a dense Jacobian (numpy only) and secant
    continuation in eps from the integrable case.  The same solver applied to N = 40 reproduces the certificate data
    certificates/lunar-spin-orbit/lower.json to double precision (checked below).
 2. Coefficient decay (digits per unit index of the envelopes max_l |b_kl| in k, max_k |b_kl| in l, max over |k|_1 = n),
    analyticity widths w = slope ln10 / (2 pi), the same fit applied to the N = 40 certificate data, and a pendulum
    cross-check (dominant term, w = K'(m) / (4 K(m))).  The strip rho' of H50 keeps R1's fraction rho/w_psi.
 3. Norms exactly as r1_norms.py (its functions are imported, not copied): Hamiltonian majorant parts, |L|, |L^T|, |B|,
    |N|, |N^T|, sup |T| (strip and T_{rho - delta0}), the bordered torsion inverse, |omega|; at rho' and at 1/70, time
    scales c in {3/2, 7/4, 2}.
 4. Diophantine data of omega' = (nu - 1, 1): numerical infimum of |k.omega'| |k|_1 over |k|_1 <= 2000, and the
    algebraic-norm lower bounds of KAM/Certificate/QuadraticDiophantine.lean redone in exact arithmetic for N = 50.
 5. Frequency-specific small-divisor sums S(omega*, delta) = sum_{k != 0} |k.omega*|^-2 exp(-4 pi delta |k|_1),
    omega* = c omega'/s, with the Abel-summation tail bound from S_{|k|_1 <= M} <= 6 gamma^-2 M^2, and the constant
    c(delta) = gamma delta (2 pi)^-1 2 S^{1/2} (n = 2, tau = 1).  Same for R1.

Package conventions (as R1): n = 2, tau = 1, rho_inf = rho/1000, mu = 1/160, s = 1 + 10^-6, nu_ray = 10^-6,
sigma_omega = 2, delta0 = (rho - rho_inf)/6 (the sharp design's 3 delta schedule), gamma = c gamma'/s; majorants =
sampled sup x 1.05, plus mu for sigma_K, sigma_B, sigma_T.  The V8 threshold (thresholds.py, Russmann, iso, one M)
is printed as an indicator only.
Usage:  python3 -I scripts/apost_sharp/h50_package.py [--json OUT]       (about a minute, at most 4 BLAS threads)
"""
import os
for _v in ("OPENBLAS_NUM_THREADS", "OMP_NUM_THREADS", "MKL_NUM_THREADS"):
    os.environ.setdefault(_v, "4")
import json, math, sys, time
from fractions import Fraction as F
import numpy as np
import mpmath as mp

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, os.path.join(ROOT, "scripts", "spin_orbit"))
sys.path.insert(0, HERE)
import model        # noqa: E402  exact model data
import r1_norms     # noqa: E402  norm measurement of package R1 (reused unchanged)
import thresholds   # noqa: E402  exact design thresholds (indicator only)

EPS = float(model.EPS)
A = {m: float(a) for m, a in model.A_EXACT.items()}
G = (math.sqrt(5) - 1) / 2
MU, S_RAY, NU_RAY, SIGMA_OMEGA, LAM, MAJ = 1 / 160, 1 + 1e-6, 1e-6, 2, 3, 1.05
CS = (1.5, 1.75, 2.0)
RHO_H50 = 1 / 83                 # the H50 strip: R1's rho/w_psi kept, (1/70) x (w_psi(H50)/w_psi(N40)) = 1/83 (step 2)
CUT = 1e-24                      # coefficient cut used when building candidates (as r1_norms.load)
LN10 = math.log(10)


def alpha(N):
    return 1 / (N + G)


# ------------------------------------------------------------------------------------------- 1. torus
class Galerkin:
    """Half box H of EVEN k (every forcing mode has psi-index 2, so the equation commutes with psi -> psi + 1/2 and
    the solution has only even k; the certificate data have only even k), grid nx x nt (nx > 4K, nt > 4Lm, so that
    the Jacobian entries g_{kappa -+ kappa'} do not alias)."""

    def __init__(self, s, K, Lm, nx=512, nt=128):
        assert 4 * K < nx and 4 * Lm < nt
        self.s, self.K, self.Lm, self.nx, self.nt = s, K, Lm, nx, nt
        H = [(k, l) for k in range(0, K + 1, 2) for l in range(-Lm, Lm + 1) if k > 0 or l > 0]
        self.kh = np.array([h[0] for h in H])
        self.lh = np.array([h[1] for h in H])
        self.n = len(H)
        self.lam2 = (s * self.kh + self.lh) ** 2
        psi = np.arange(nx)[:, None] / nx
        phi = np.arange(nt)[None, :] / nt
        self.theta = {m: 2 * np.pi * (2 * psi + (2 - m) * phi) for m in A}
        self.ip = ((self.kh[:, None] - self.kh[None, :]) % nx, (self.lh[:, None] - self.lh[None, :]) % nt)
        self.iq = ((self.kh[:, None] + self.kh[None, :]) % nx, (self.lh[:, None] + self.lh[None, :]) % nt)

    def vgrid(self, b):
        C = np.zeros((self.nx, self.nt), complex)
        C[self.kh % self.nx, self.lh % self.nt] = b / 2j
        C[(-self.kh) % self.nx, (-self.lh) % self.nt] = -b / 2j
        return np.real(np.fft.ifft2(C)) * self.nx * self.nt

    def sine_coeffs(self, f):
        fh = np.fft.fft2(f) / (self.nx * self.nt)
        return -2 * fh[self.kh % self.nx, self.lh % self.nt].imag

    def resid(self, b, eps):
        """Galerkin residual (sine coefficients of R on H) and the grid values of v."""
        v = self.vgrid(b)
        Fm = sum(A[m] * np.sin(self.theta[m] + 2 * v) for m in A)
        return -self.lam2 * b + 2 * eps * self.sine_coeffs(Fm), v

    def jac(self, v, eps):
        g = 4 * eps * sum(A[m] * np.cos(self.theta[m] + 2 * v) for m in A)      # even
        gh = np.real(np.fft.fft2(g)) / (self.nx * self.nt)
        J = gh[self.ip] - gh[self.iq]                                             # sine-basis multiplication
        J[np.diag_indices(self.n)] -= self.lam2
        return J

    def newton(self, b, eps, tol=1e-14, maxit=25):
        hist = []
        for it in range(maxit):
            R, v = self.resid(b, eps)
            hist.append(float(np.abs(R).max()))
            if hist[-1] < tol or (it >= 3 and hist[-1] > 0.5 * hist[-2]):
                break
            b = b - np.linalg.solve(self.jac(v, eps), R)
        return b, hist


def solve_torus(N, K, Lm, nsteps=50, nx=512, nt=128):
    """Secant continuation in eps from 0 to the model's eps; returns (solver, b, log)."""
    Gk = Galerkin(-alpha(N), K, Lm, nx, nt)
    b, bprev, log = np.zeros(Gk.n), None, []
    for j in range(1, nsteps + 1):
        eps = EPS * j / nsteps
        guess = b if bprev is None else 2 * b - bprev
        bn, hist = Gk.newton(guess, eps, tol=1e-17 if j < nsteps else 1e-19)
        if hist[-1] > 1e-14:
            raise RuntimeError("continuation failed at step %d (eps = %g): %s" % (j, eps, hist))
        bprev, b = b, bn
        log.append(len(hist))
    return Gk, b, dict(newton_iterations=log, final_history=hist)


def full_residual(N, co, nx=1024, nt=256):
    """sup over a fine grid of the UNprojected residual R(v) of the truncated torus (pi-free units), and of p."""
    s = -alpha(N)
    C = np.zeros((nx, nt), complex)
    D2 = np.zeros((nx, nt), complex)
    D1 = np.zeros((nx, nt), complex)
    for k, l, b in co:
        lam = s * k + l
        for sg, c in ((1, b / 2j), (-1, -b / 2j)):
            C[(sg * k) % nx, (sg * l) % nt] += c
            D2[(sg * k) % nx, (sg * l) % nt] += -(lam ** 2) * c
            D1[(sg * k) % nx, (sg * l) % nt] += 1j * sg * lam * c
    ev = lambda X: np.fft.ifft2(X).real * nx * nt
    v, d2v, dv = ev(C), ev(D2), ev(D1)
    psi = np.arange(nx)[:, None] / nx
    phi = np.arange(nt)[None, :] / nt
    R = d2v + 2 * EPS * sum(A[m] * np.sin(2 * np.pi * (2 * psi + (2 - m) * phi) + 2 * v) for m in A)
    p = 1 + s + dv                       # p = nu + Dt v  (model.py)
    return float(np.abs(R).max()), float(p.min()), float(p.max())


def cert_coeffs(which="lower"):
    d = json.load(open(os.path.join(ROOT, "certificates", "lunar-spin-orbit", "%s.json" % which)))
    P = d["scale_bits"]
    return [(int(k), int(l), int(n) / 2 ** P) for k, l, n in d["v_sin"]]


def build_h50(N=50, K=48, Lm=12):
    """Box K = 48 (even k), |l| <= 12: just below the first psi-resonance (50, 1) (1 - 50 alpha = 0.012), where double
    precision roundoff (~1e-20 in R) is amplified by 1/lambda^2 to ~1e-16 while the true coefficient is ~1e-23.
    Resolution: a mode is 'resolved' if two solves on different grids (512 x 128, 1024 x 256) agree to 10 %."""
    t0 = time.time()
    Gk, b, info = solve_torus(N, K, Lm)
    co = [(int(k), int(l), float(x)) for k, l, x in zip(Gk.kh, Gk.lh, b)]
    G2, b2, _ = solve_torus(N, K, Lm, nx=1024, nt=256)
    resolved = {(int(k), int(l)) for k, l, x, y in zip(Gk.kh, Gk.lh, b, b2) if abs(x - y) <= 0.1 * abs(x)}
    big, b3, _ = solve_torus(N, 64, 16)        # truncation check against a larger box (K = 64 contains the
                                               # resonant modes (50, 1), (52, 1), whose values are roundoff)
    d3 = {(int(k), int(l)): x for k, l, x in zip(big.kh, big.lh, b3)}
    diff = max(abs(x - d3[(k, l)]) for k, l, x in co)
    res, pmin, pmax = full_residual(N, co)
    edge_k = max(abs(x) for k, l, x in co if k >= K - 2)
    edge_l = max(abs(x) for k, l, x in co if abs(l) >= Lm - 1)
    reson = {"(%d,1)" % k: d3[(k, 1)] for k in (50, 52)}
    smallest = min(abs(x) for k, l, x in co if (k, l) in resolved)
    rep = dict(N=N, nu=1 - alpha(N), box=dict(K=K, Lm=Lm, k_parity="even", n_modes=len(co)), grid=[512, 128],
               continuation_steps=50, newton_final_history=info["final_history"],
               galerkin_residual=info["final_history"][-1], full_residual_sup_R=res,
               full_residual_sup_r=2 * math.pi * res,
               full_residual_grid=[1024, 256], edge_max_k=edge_k, edge_max_l=edge_l,
               max_diff_vs_box_64x16=diff, box64_resonant_mode_values=reson, n_resolved=len(resolved),
               smallest_resolved=smallest, max_diff_grid_1024x256=float(np.abs(b - b2).max()),
               p_range=[pmin, pmax], max_abs_p_minus_1=max(abs(pmin - 1), abs(pmax - 1)),
               support={"%g" % t: sum(1 for _, _, x in co if abs(x) > t) for t in (1e-8, 1e-10, 1e-12, 1e-15)},
               seconds=round(time.time() - t0, 1))
    return co, resolved, rep


def check_n40():
    """The solver at N = 40 against the certificate data (box K = 38, Lm = 12: below the resonance (40, 1))."""
    Gk, b, _ = solve_torus(40, 38, 12, nsteps=40)
    cert = {(k, l): x for k, l, x in cert_coeffs("lower")}
    diff = max(abs(x - cert.get((int(k), int(l)), 0.0)) for k, l, x in zip(Gk.kh, Gk.lh, b))
    return dict(box=[38, 12], max_abs_diff_vs_certificate=diff)


# ------------------------------------------------------------------------------------------- 2. decay
def envelopes(co):
    ek, el, e1 = {}, {}, {}
    for k, l, b in co:
        a = abs(b)
        ek[abs(k)] = max(ek.get(abs(k), 0.0), a)
        el[abs(l)] = max(el.get(abs(l), 0.0), a)
        e1[abs(k) + abs(l)] = max(e1.get(abs(k) + abs(l), 0.0), a)
    return ek, el, e1


def fit(env, i0, i1, floor):
    """Least-squares slope (digits per unit index) of log10 env on i0 <= i <= i1 where env >= floor."""
    pts = [(i, math.log10(env[i])) for i in sorted(env) if i0 <= i <= i1 and env[i] >= floor]
    x = np.array([p[0] for p in pts], float)
    y = np.array([p[1] for p in pts])
    sl = -np.polyfit(x, y, 1)[0]
    return dict(digits_per_index=float(sl), width=float(sl * LN10 / (2 * math.pi)), window=[int(x[0]), int(x[-1])],
                n_points=len(pts))


def decay(co, N, resolved=None, floor=1e-21, full=False):
    """Fit windows: 4 <= k <= N - 10 (pre-resonant: the (k, 1) divisor 1 - k alpha stays >= 0.2), l >= 1,
    4 <= |k|_1 <= N - 10; only resolved modes (all for the certificate data) above floor."""
    if resolved is not None:
        co = [(k, l, b) for k, l, b in co if (k, l) in resolved]
    ek, el, e1 = envelopes(co)
    out = dict(psi=fit(ek, 4, N - 10, floor), phi=fit(el, 1, 10 ** 6, floor), iso=fit(e1, 4, N - 10, floor))
    if full:   # asymptotic rate through the resonance bumps (certificate data down to 1e-125)
        out["psi_asymptotic"] = fit(ek, 4, 10 ** 6, 1e-125)
        out["phi_asymptotic"] = fit(el, 1, 10 ** 6, 1e-125)
        out["iso_asymptotic"] = fit(e1, 4, 10 ** 6, 1e-125)
    out["envelope_psi_log10"] = {k: round(math.log10(ek[k]), 2) for k in sorted(ek) if k <= 60 and ek[k] > 0}
    out["envelope_phi_log10"] = {l: round(math.log10(el[l]), 2) for l in sorted(el) if l <= 16 and el[l] > 0}
    return out


def pendulum_width(N):
    """Dominant-term pendulum psi'' = -4 pi eps A2 sin(4 pi psi): rotation number |nu - 1| = pi sqrt(eps A2)/(k K(k^2)),
    angle-variable width w = K'/(4K); returns (k^2, w, energy above the separatrix as a fraction)."""
    mp.mp.dps = 30
    ea = mp.mpf(EPS * A[2])
    target = mp.pi * mp.sqrt(ea) / mp.mpf(alpha(N))
    lo, hi = mp.mpf("1e-6"), 1 - mp.mpf("1e-12")          # sqrt(m) K(m) increases on (0, 1): bisection
    for _ in range(120):
        m = (lo + hi) / 2
        lo, hi = (m, hi) if mp.sqrt(m) * mp.ellipk(m) < target else (lo, m)
    w = mp.ellipk(1 - m) / (4 * mp.ellipk(m))
    return dict(m=float(m), width=float(w), digits_per_k=float(2 * mp.pi * w / mp.log(10)),
                energy_above_separatrix=float(2 / m - 2))        # m = 2 eps A2 / (E + eps A2), E_sep = eps A2


# ------------------------------------------------------------------------------------------- 3. norms
class CoeffCand(r1_norms.Cand):
    """r1_norms.Cand built from a coefficient list (k, l, b) and a frequency nu instead of the certificate file."""

    def __init__(self, nu, co, N1=256, N2=64):
        self.nu = nu
        self.co = [(k, l, b) for k, l, b in co if abs(b) > CUT]
        assert max(abs(k) for k, _, _ in self.co) < N1 // 2 and max(abs(l) for _, l, _ in self.co) < N2 // 2
        self.N1, self.N2 = N1, N2
        self.psi = np.arange(N1)[:, None] / N1 + 0 * np.arange(N2)[None, :]
        self.phi = np.arange(N2)[None, :] / N2 + 0 * np.arange(N1)[:, None]
        self.kk = np.fft.fftfreq(N1, 1 / N1)[:, None] * np.ones((1, N2))
        self.ll = np.fft.fftfreq(N2, 1 / N2)[None, :] * np.ones((N1, 1))


def measure(cand, rho, c, mu=MU, lam=LAM):
    """r1_norms.measure for an arbitrary candidate (same code path: objects, rowsum, H_parts)."""
    rhoinf = rho / 1000
    delta0 = min(1.0, (rho - rhoinf) / (2 * lam))
    out = {}
    for tag, y in (("strip", rho), ("strip_minus_delta0", rho - delta0)):
        acc = dict(L=0.0, LT=0.0, B=0.0, N=0.0, NT=0.0, T=0.0, Y=0.0)
        imX = np.zeros(8)
        pmax = 0.0
        for (yp, yf) in ((y, y), (y, -y)):
            o = r1_norms.objects(cand, yp, yf, c)
            for k in acc:
                acc[k] = max(acc[k], r1_norms.rowsum(o[k]) if k != "Y" else float(np.abs(o["Y"]).max()))
            gg = o["g"]
            pmax = max(pmax, float(np.abs(gg["p"] - 1).max()))
            for m in range(1, 8):
                imX[m] = max(imX[m], float(np.abs((2 * gg["q"] - m * gg["ph"]).imag).max()))
        out[tag] = acc
        if tag == "strip":
            out["H"] = {k: float(v) for k, v in r1_norms.H_parts(imX, pmax, mu, c).items()}
            out["pmax_strip"] = pmax
    o = r1_norms.objects(cand, 0.0, 0.0, c)
    Tavg = o["T"].mean(axis=(0, 1))
    om = c * np.array([cand.nu - 1, 1.0])
    ext = np.zeros((3, 3), complex)
    ext[:2, :2] = Tavg
    ext[:2, 2] = om
    ext[2, :2] = o["Y"].mean(axis=(0, 1))
    out["real"] = dict(T_sup=r1_norms.rowsum(o["T"]), Tavg=np.real(Tavg).tolist(),
                       ext_inv=r1_norms.rowsum(np.linalg.inv(ext)), omega_norm=float(np.abs(om).max()))
    out["params"] = dict(rho=rho, rhoinf=rhoinf, mu=mu, c=c, delta0=delta0)
    return out


def majorants(r, mu=MU):
    """Package majorants from a measure() result: sampled sup x 1.05, + mu for sigma_K, sigma_B, sigma_T."""
    H = {k: MAJ * v for k, v in r["H"].items()}
    return dict(H_parts=H, M=max(H.values()), sigma_K=MAJ * r["strip"]["L"] + mu, LT=MAJ * r["strip"]["LT"],
                sigma_B=MAJ * r["strip"]["B"] + mu, N=MAJ * r["strip"]["N"], NT=MAJ * r["strip"]["NT"],
                T_sup_minus_delta0=MAJ * r["strip_minus_delta0"]["T"], sigma_T=MAJ * r["real"]["ext_inv"] + mu,
                omega=r["real"]["omega_norm"])


def up4(x):
    return F(math.ceil(x * 10 ** 4 - 1e-9), 10 ** 4)


def v8_threshold(mj, rho, c, gprime):
    """Indicator: log10 threshold of the sharp design V8 (thresholds.sharp, Russmann, iso, one M; majorants rounded
    up to 4 decimals), for the scaled Hamiltonian cH and for the unscaled error eta (minus log10 c)."""
    s = 1 + F(1, 10 ** 6)
    gamma = F(c).limit_denominator(100) * gprime / s
    rho = F(rho).limit_denominator(10 ** 4)
    k = thresholds.sharp(n=2, tau=1, kappa=1, cR=thresholds.cohConstR_lean(2, 1), M=up4(mj["M"]),
                         sK=up4(mj["sigma_K"]), sB=up4(mj["sigma_B"]), sT=up4(mj["sigma_T"]), mu=F(1, 160), rho=rho,
                         rhoinf=rho / 1000, gbar=gamma, nu=F(1, 10 ** 6), iso=True)
    t = thresholds.lg(thresholds.threshold(k, gamma))
    return dict(log10_threshold=round(t, 2), log10_threshold_unscaled_eta=round(t - math.log10(c), 2),
                active=k["active"])


def l_proxy(log10_thr, rho, d_psi):
    """Model of the truncation depth (digits) for a residual 2 orders below the threshold: coefficients cut at 10^-L
    leave a residual at the psi-edge k ~ L/d_psi, weighted on T_rho by exp(2 pi rho L/d_psi) (CONSTANTS-STUDY 2.3)."""
    return (2 - log10_thr) / (1 - 2 * math.pi * rho / (d_psi * LN10))


# ------------------------------------------------------------------------------------------- 4. Diophantine
def dio_numeric(om1, kmax=2000):
    """inf |k1 om1 + k2| (|k1| + |k2|) over 0 < |k|_1 <= kmax (k -> -k symmetry: k1 >= 0)."""
    best = (1.0, (0, 1))
    for k1 in range(0, kmax + 1):
        x = k1 * om1
        for k2 in {math.floor(-x), math.ceil(-x)}:
            if (k1 == 0 and k2 <= 0) or k1 + abs(k2) > kmax:
                continue
            v = abs(x + k2) * (k1 + abs(k2))
            if v < best[0]:
                best = (v, (k1, k2))
    return dict(infimum=best[0], binding_k=list(best[1]))


def norm_argument(L, x_lo, c):
    """The argument of `norm_bound` (KAM/Certificate/QuadraticDiophantine.lean), generalised.  x an irrational root of
    an integer quadratic L x^2 - B x + C of discriminant 5 (conjugate x', |x - x'| = sqrt5/L <= 9/(4L)); then
    |a x + b| >= 1/(c (|a| + |b|)) for all integers (a, b) != 0 provided (i) |a| + |b| = 1: 1 >= 1/c and |x| >= 1/c
    (x_lo a rational lower bound of |x|); (ii) |a| + |b| >= 2: L/(4c^2) + 9/(4c) <= 1 (norm |(ax+b)(ax'+b)| >= 1/L).
    Exact rational check."""
    lhs = F(L) / (4 * c * c) + F(9) / (4 * c)
    return dict(c=str(c), case1=bool(x_lo >= 1 / c and 1 >= 1 / c), case2_lhs=float(lhs), case2=bool(lhs <= 1),
                proved=bool(x_lo >= 1 / c and lhs <= 1))


def q5_check(N):
    """Exact data of nu = 1 - 1/(N+g) in Q(sqrt5): alpha = 1/(N+g) = (2N-1-sqrt5)/(2L), L = N^2-N-1, root of
    L a^2 - (2N-1) a + 1; minimal polynomials of nu (theta frame) and nu - 1 = -alpha (rotated frame)."""
    L = N * N - N - 1
    a0, a1 = F(2 * N - 1, 2 * L), F(-1, 2 * L)             # alpha = a0 + a1 sqrt5

    def poly0(p, q, Lc, Bc, Cc):                            # Lc x^2 - Bc x + Cc at x = p + q sqrt5: (rational, sqrt5)
        return (Lc * (p * p + 5 * q * q) - Bc * p + Cc, Lc * 2 * p * q - Bc * q)
    B_th, C_th = 2 * L - (2 * N - 1), L - (2 * N - 1) + 1  # theta frame: x = 1 - alpha (N = 40: 1559, 3039, 1481)
    ok = poly0(1 - a0, -a1, L, B_th, C_th) == (0, 0) and poly0(-a0, -a1, L, -(2 * N - 1), 1) == (0, 0)
    alpha_lo = a0 + a1 * F(2237, 1000)                      # sqrt5 < 2.237: a rational lower bound of alpha
    info = dict(L=L, theta_poly=[L, -B_th, C_th], rot_poly=[L, 2 * N - 1, 1], exact_roots=bool(ok))
    return info, alpha_lo, L


def diophantine(N):
    info, alpha_lo, L = q5_check(N)
    al = alpha(N)
    ct = F(N + 2, 2)                                        # theta-frame constant (21 for N = 40, 26 for N = 50)
    theta_proof = norm_argument(L, F(1, 2), ct)             # |nu| >= 1/2
    direct = {str(1 / c): norm_argument(L, alpha_lo, c) for c in (F(N + 1), F(8 * N + 5, 8))}
    return dict(N=N, alpha=al, q5=info, rotated=dio_numeric(-al), theta=dio_numeric(1 - al),
                theta_frame_proof=theta_proof, gamma_theta=str(1 / ct),
                gamma_rot_transfer=str(1 / (2 * ct)), gamma_rot_transfer_float=float(1 / (2 * ct)),
                direct_rotated_proofs=direct)


# ------------------------------------------------------------------------------------------- 5. small divisors
def shell_sums(om1, nmax):
    """a_m = sum_{|k|_1 = m} |k1 om1 + k2|^-2 over the half lattice (k1 > 0, or k1 = 0 < k2), m <= nmax."""
    a = np.zeros(nmax + 1)
    j = np.arange(1, nmax + 1)
    a[1:] += 1.0 / (j * 1.0) ** 2
    for k1 in range(1, nmax + 1):
        k2 = np.arange(0, nmax - k1 + 1, dtype=float)
        tp = 1.0 / (k1 * om1 + k2) ** 2
        tn = 1.0 / (k1 * om1 - k2) ** 2
        tot = tp + tn
        tot[0] = tp[0]
        a[k1:] += tot
    return 2 * a                                             # full lattice (k and -k)


def tail_bound(gam, x, N):
    """Abel summation with A(M) <= 6 gam^-2 M^2: sum_{|k|_1 > N} ... <= 6 gam^-2 (1 - e^-x) sum_{m > N} m^2 e^{-x m}."""
    y = math.exp(-x)
    n1 = N + 1
    s2 = y ** n1 * (n1 ** 2 / (1 - y) + 2 * n1 * y / (1 - y) ** 2 + y * (1 + y) / (1 - y) ** 3)
    return 6 / gam ** 2 * (1 - y) * s2


def smalldiv(om1, c, gprime, rho, a_shell):
    """S(omega*, delta), its tail bound and c(delta) at delta0 / 2^j, j = 0..3; omega* = (c/s)(om1, 1)."""
    nmax = len(a_shell) - 1
    sc = (S_RAY / c) ** 2                                    # |k.omega*|^-2 = (s/c)^2 |k.omega'|^-2
    gam = c * gprime / S_RAY
    delta0 = (rho - rho / 1000) / 6
    m = np.arange(nmax + 1)
    A_cum = np.cumsum(a_shell) * sc
    bound_ok = bool(np.all(A_cum[1:] <= 6 / gam ** 2 * m[1:] ** 2))
    rows = []
    for j in range(4):
        d = delta0 / 2 ** j
        x = 4 * math.pi * d
        terms = a_shell * sc * np.exp(-x * m)
        Scum = np.cumsum(terms)
        S = float(Scum[-1])
        tails = np.array([tail_bound(gam, x, n) for n in range(0, nmax + 1, 50)])
        ok = [n for n, t in zip(range(0, nmax + 1, 50), tails) if t < 0.01 * Scum[n]]
        tb = tail_bound(gam, x, nmax)
        rows.append(dict(delta=d, S=S, tail_bound_at_nmax=tb, N_for_1pct=ok[0] if ok else None,
                         c_delta=gam * d / (2 * math.pi) * 2 * math.sqrt(S),
                         c_delta_upper=gam * d / (2 * math.pi) * 2 * math.sqrt(S + tb)))
    return dict(c=c, gamma=gam, rho=rho, delta0=delta0, nmax=nmax, classical_bound_holds=bound_ok, rows=rows)


# ------------------------------------------------------------------------------------------- driver
def fmt(x, nd=4):
    return ("%%.%df" % nd) % x


def print_report(out, norms, pk, dio, sd, att):
    rep, dec = out["torus_H50"], out["decay"]
    print("1. H50 torus: nu = %.15f, box even k <= %d, |l| <= %d (%d modes), Galerkin residual %.1e, fine-grid "
          "sup|R| %.1e (r = 2 pi R: %.1e); edge |b| %.1e (k) / %.1e (l); vs box 64x16 %.1e; p in [%.5f, %.5f]" % (
              rep["nu"], rep["box"]["K"], rep["box"]["Lm"], rep["box"]["n_modes"], rep["galerkin_residual"],
              rep["full_residual_sup_R"], rep["full_residual_sup_r"], rep["edge_max_k"], rep["edge_max_l"],
              rep["max_diff_vs_box_64x16"], rep["p_range"][0], rep["p_range"][1]))
    print("   solver at N = 40: max |b - b_cert| = %.1e;  H50 resolved modes %d (smallest %.1e)" % (
        out["solver_check_N40"]["max_abs_diff_vs_certificate"], rep["n_resolved"], rep["smallest_resolved"]))
    print("   half-lattice support |b| > t: H50 %s;  N40 %s" % (rep["support"], out["support_N40_certificate"]))
    print("2. decay, digits per index (width):")
    for name, d in (("H50", dec["H50"]), ("N40", dec["N40_certificate"])):
        print("   %s: psi %.3f (%.3f) on k in %s, phi %.3f (%.3f), |k|_1 %.3f (%.3f)" % (
            name, d["psi"]["digits_per_index"], d["psi"]["width"], d["psi"]["window"], d["phi"]["digits_per_index"],
            d["phi"]["width"], d["iso"]["digits_per_index"], d["iso"]["width"]))
    d = dec["N40_certificate"]
    print("   N40 asymptotic (to 1e-125): psi %.3f (%.3f), phi %.3f (%.3f), |k|_1 %.3f (%.3f)" % (
        d["psi_asymptotic"]["digits_per_index"], d["psi_asymptotic"]["width"], d["phi_asymptotic"]["digits_per_index"],
        d["phi_asymptotic"]["width"], d["iso_asymptotic"]["digits_per_index"], d["iso_asymptotic"]["width"]))
    r = dec["psi_width_ratios_H50_over_N40"]
    print("   pendulum widths N = 40/50/60: %s;  psi-width ratio H50/N40: fit %.3f, same k-range %.3f, pendulum %.3f;"
          "  (1/70) x ratio = 1/%.1f;  chosen rho' = %s" % (
              ", ".join("%.3f" % dec["pendulum"][N]["width"] for N in (40, 50, 60)), r["window_fit"],
              r["same_k_range"], r["pendulum"], dec["rho_proportional_reciprocal"], dec["rho_H50_fraction"]))
    print("3. norms (sampled sups; measure() reproduces r1_norms.measure() to %.1e):" %
          out["measure_validation_vs_r1_norms"])
    cols = [(n, c) for n in ("H50", "H50_rho70", "R1") for c in CS]
    print("| quantity | " + " | ".join("%s c=%s" % nc for nc in cols) + " |")
    print("|---|" + "---:|" * len(cols))
    getters = [("H:" + q, (lambda q: lambda x: x["H"][q])(q)) for q in ("dH", "XH", "DXH", "D2XH", "D2H")] + [
        ("|L|", lambda x: x["strip"]["L"]), ("|L^T|", lambda x: x["strip"]["LT"]), ("|B|", lambda x: x["strip"]["B"]),
        ("|N|", lambda x: x["strip"]["N"]), ("|N^T|", lambda x: x["strip"]["NT"]),
        ("sup|T| strip", lambda x: x["strip"]["T"]), ("sup|T| rho-delta0", lambda x: x["strip_minus_delta0"]["T"]),
        ("|<T_ext>^-1|", lambda x: x["real"]["ext_inv"]), ("|omega|", lambda x: x["real"]["omega_norm"]),
        ("max|p-1| strip", lambda x: x["pmax_strip"])]
    for q, f in getters:
        print("| %s | " % q + " | ".join(fmt(f(norms[n][str(c)])) for n, c in cols) + " |")
    print("| V8 log10 thr (eta) | " + " | ".join(
        "%.2f" % pk[n][str(c)]["v8"]["log10_threshold_unscaled_eta"] for n, c in cols) + " |")
    print("4. Diophantine:")
    for N in (40, 50):
        d = dio[N]
        print("   N=%d: alpha %.6f; rotated inf %.6f at k=%s; theta inf %.6f at k=%s; theta-frame proof c = %s "
              "(case 2: %.4f <= 1: %s) -> transfer gamma' = %s; direct rotated: %s" % (
                  N, d["alpha"], d["rotated"]["infimum"], d["rotated"]["binding_k"], d["theta"]["infimum"],
                  d["theta"]["binding_k"], d["theta_frame_proof"]["c"], d["theta_frame_proof"]["case2_lhs"],
                  d["theta_frame_proof"]["proved"], d["gamma_rot_transfer"],
                  ", ".join("%s %s" % (k, v["proved"]) for k, v in d["direct_rotated_proofs"].items())))
    print("5. small-divisor sums, c(delta) = gamma delta (2 pi)^-1 2 sqrt(S)  (cohConstR 2 1 = %.5f):" %
          out["small_divisors"]["cohConstR_2_1"])
    for name in ("H50", "H50_rho70", "R1"):
        s_ = sd[name]
        print("   %s rho = 1/%.0f, gamma = %.6f, nmax = %d, classical bound holds: %s" % (
            name, 1 / s_["rho"], s_["gamma"], s_["nmax"], s_["classical_bound_holds"]))
        for j, row in enumerate(s_["rows"]):
            print("      delta0/%d: S = %.4e  c(delta) = %.5f  tail/S <= %.1e  (1%% reached at N = %s)" % (
                2 ** j, row["S"], row["c_delta"], row["tail_bound_at_nmax"] / row["S"], row["N_for_1pct"]))
    print("V8 attribution (log10 threshold on eta, c = 7/4): " + "; ".join("%s %.2f" % a for a in att))
    print("truncation-depth model L (digits): %s" %
          {k: round(v, 1) for k, v in out["truncation_depth_model"]["L"].items()})
    print("H50 package: %s" % json.dumps({k: v for k, v in out["H50_package"].items() if k != "majorants"}))
    print("H50 majorants (c = 7/4): %s" % json.dumps(out["H50_package"]["majorants"]))


def main():
    t0 = time.time()
    out = dict(inputs=dict(eps=str(model.EPS), e=str(model.E_ORB), modes=7, g="(sqrt5-1)/2", mu="1/160", s="1+1e-6",
                           nu_ray=NU_RAY, sigma_omega=SIGMA_OMEGA, lam=LAM, majorant_factor=MAJ, cut=CUT,
                           sup_grid=[256, 64], c_scan=list(CS)))
    # 1. torus
    co50, resolved, rep = build_h50()
    out["torus_H50"] = rep
    out["solver_check_N40"] = check_n40()
    co40 = cert_coeffs("lower")
    out["support_N40_certificate"] = {"%g" % t: sum(1 for _, _, x in co40 if abs(x) > t)
                                      for t in (1e-8, 1e-10, 1e-12, 1e-15)}
    # 2. decay and the strip
    d50 = decay(co50, 50, resolved)
    d40 = decay(co40, 40, full=True)
    ek50 = envelopes([(k, l, b) for k, l, b in co50 if (k, l) in resolved])[0]
    same_k = dict(H50=fit(ek50, 4, 30, 1e-21), N40=d40["psi"])             # identical k-range [4, 30]
    pend = {N: pendulum_width(N) for N in (40, 50, 60)}
    ratios = dict(window_fit=d50["psi"]["width"] / d40["psi"]["width"],
                  same_k_range=same_k["H50"]["width"] / same_k["N40"]["width"],
                  pendulum=pend[50]["width"] / pend[40]["width"])
    rho_prop = (1 / 70) * ratios["window_fit"]
    rho_h = RHO_H50
    out["decay"] = dict(H50=d50, N40_certificate=d40, same_k_range_4_30=same_k, pendulum=pend,
                        psi_width_ratios_H50_over_N40=ratios, rho_proportional=rho_prop,
                        rho_proportional_reciprocal=1 / rho_prop, rho_H50=rho_h,
                        rho_H50_fraction="1/%d" % round(1 / rho_h))
    # 3. norms
    c50 = CoeffCand(1 - alpha(50), co50)
    c40 = CoeffCand(1 - alpha(40), co40)
    ref = r1_norms.measure()                                  # R1 straight from r1_norms (validation of measure())
    mine = measure(c40, 1 / 70, 1.75)
    dev = max([abs(mine["strip"][k] - ref["strip"][k]) for k in mine["strip"]]
              + [abs(mine["H"][k] - ref["H"][k]) for k in ref["H"]]
              + [abs(mine["real"]["ext_inv"] - ref["real"]["ext_inv"])])
    out["measure_validation_vs_r1_norms"] = dev
    norms = {}
    for name, cand, rho in (("H50", c50, rho_h), ("H50_rho70", c50, 1 / 70), ("R1", c40, 1 / 70)):
        norms[name] = {str(c): measure(cand, rho, c) for c in CS}
    fine = measure(CoeffCand(1 - alpha(50), co50, 512, 128), rho_h, 1.75)
    out["norms"] = norms
    out["norms_grid_check_H50_512x128_c1.75"] = dict(strip=fine["strip"], ext_inv=fine["real"]["ext_inv"], H=fine["H"])
    # 4. Diophantine
    dio = {N: diophantine(N) for N in (40, 50)}
    out["diophantine"] = {str(N): v for N, v in dio.items()}
    gp = {50: F(1, 52), 40: F(1, 42)}                         # gamma' of the packages (theta-frame proof + transfer)
    # 5. small divisors
    t5 = time.time()
    sd, shells = {}, {}
    for name, N, rho, c in (("H50", 50, rho_h, 1.75), ("H50_rho70", 50, 1 / 70, 1.75), ("R1", 40, 1 / 70, 1.75)):
        nmax = int(math.ceil(22 / (4 * math.pi * (rho - rho / 1000) / 48)))     # exp(-22) at delta0/8
        if N not in shells or shells[N][0] < nmax:
            shells[N] = (nmax, shell_sums(-alpha(N), nmax))
        sd[name] = smalldiv(-alpha(N), c, float(gp[N]), rho, shells[N][1][:nmax + 1])
    out["small_divisors"] = dict(sd, cohConstR_2_1=float(thresholds.cohConstR_lean(2, 1)),
                                 cohConst_parseval_optimal=float(thresholds.cohConst_parseval_n2()),
                                 seconds=round(time.time() - t5, 1))
    # package assembly and the V8 indicator
    pk = {}
    for name, rho, N in (("H50", rho_h, 50), ("H50_rho70", 1 / 70, 50), ("R1", 1 / 70, 40)):
        pk[name] = {}
        for c in CS:
            mj = majorants(norms[name][str(c)])
            pk[name][str(c)] = dict(majorants=mj, gamma=c * float(gp[N]) / S_RAY, v8=v8_threshold(mj, rho, c, gp[N]))
    out["packages"] = pk
    eta = lambda name: pk[name]["1.75"]["v8"]["log10_threshold_unscaled_eta"]
    att = [("R1", eta("R1")),
           ("R1 norms, gamma' = 1/52, rho = 1/70",
            v8_threshold(majorants(norms["R1"]["1.75"]), 1 / 70, 1.75, gp[50])["log10_threshold_unscaled_eta"]),
           ("H50 norms, gamma' = 1/52, rho = 1/70", eta("H50_rho70")),
           ("H50 norms, gamma' = 1/52, rho = 1/83 (H50)", eta("H50"))]
    out["v8_attribution"] = att
    d_as = dict(R1=d40["psi_asymptotic"]["digits_per_index"],
                H50=d40["psi_asymptotic"]["digits_per_index"] * ratios["window_fit"])
    out["truncation_depth_model"] = dict(
        d_psi_asymptotic=d_as, note="H50 asymptotic decay estimated as N40 asymptotic x window ratio",
        L=dict(H50=l_proxy(eta("H50"), rho_h, d_as["H50"]), H50_rho70=l_proxy(eta("H50_rho70"), 1 / 70, d_as["H50"]),
               R1=l_proxy(eta("R1"), 1 / 70, d_as["R1"])))
    mj = pk["H50"]["1.75"]["majorants"]
    out["H50_package"] = dict(
        n=2, tau=1, rho=rho_h, rho_fraction="1/%d" % round(1 / rho_h), rho_inf=rho_h / 1000, mu="1/160", c=1.75,
        s="1+1e-6", gamma_prime="1/52", gamma="(7/4)/(52 s) = 7/(208 s)", gamma_float=1.75 / 52 / S_RAY,
        nu_ray=NU_RAY, sigma_omega=SIGMA_OMEGA, delta0=(rho_h - rho_h / 1000) / 6, majorants=mj,
        majorants_rounded_up_4dp={k: str(up4(mj[k])) for k in ("M", "sigma_K", "sigma_B", "sigma_T")},
        v8_indicator=pk["H50"]["1.75"]["v8"],
        best_c_in_scan_by_v8=max(CS, key=lambda c: pk["H50"][str(c)]["v8"]["log10_threshold_unscaled_eta"]))
    out["seconds"] = round(time.time() - t0, 1)
    print_report(out, norms, pk, dio, sd, att)
    print("total %.0fs" % out["seconds"])
    if len(sys.argv) > 2 and sys.argv[1] == "--json":
        with open(sys.argv[2], "w") as fh:
            json.dump(out, fh, indent=1, default=lambda o: float(o) if isinstance(o, np.floating) else str(o))


if __name__ == "__main__":
    main()
