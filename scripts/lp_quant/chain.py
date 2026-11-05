#!/usr/bin/env python3
"""LP-QUANT: the constant chain of LP1/LP2, three routes.  Untrusted design tooling.

Route L (Lean, literal): KAM/Planetary/StrongAMD/{NonresonantScale, NonresonantReuse/*, PlanarSafety/Prograde}.lean, with
  the two compactness outputs (R, M of `exists_strongTube`; r_g, r_1 of `exists_isSharedTube`, `exists_budget_radius`)
  replaced by numerics.  Fixed choices of the proof: D0 = 1, s0 = b0 = R/16, s = sigma = s0/pi, w = 2 b0, p = 2.
Route E (engine with free parameters): the same theorem `KAM.Nekhoroshev.nonresonant`, inequalities (37)-(38), every free
  parameter optimized; switches for each sharpening (see Opts).
Route P (paper): MAIN Lemmas 9-12, vector-field norm, B_D = 16 e D, q_D = 1/(96 e D) (c_D is left implicit in the source;
  audit note N5 checks the bookkeeping at this value).

Engine premises in period-one convention (`ExtNFHyp`, `nonresonant`), p = 2, q = conjExp p = 2:
   (E1) K L r <= alpha/2   (E2) eps <= alpha r /(256 K)   (E3) 64 pi k s r <= w^2   (E4) 2 pi K s >= 6
   (E5) |t| <= s r/(5 eps) exp(2 pi K s/6);   conclusion: drift <= r/2.
 alpha = min_{0<|j|<=K} |j.omega|/(2 pi), L = sup-norm Lipschitz constant of omega/(2 pi), eps = |mu f/(2 pi)|_{r,s}.

Labels: exact (formula), bounded (rigorous up to rounding), estimated (sampled sup).  M is `estimated` everywhere.
"""
from dataclasses import dataclass, replace
import json
import math
import os
import sys
import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import geometry as G
import chart as Ch
import divisors as Dv

TP = 2 * math.pi
GYR5 = 5e9
RC = 2e-3  # complex action radius used in every M table; the engine's r is capped by it
COLLARS = (1e-4, 1e-3, 3e-3, 1e-2, 3e-2)  # slow collars b = w of the M tables


def coth(x):
    return 1 / math.tanh(x)


class Ctx:
    """Everything about one system that does not depend on mu."""

    def __init__(self, s, spatial=None, Kmax=None, seed=1):
        self.sys = s
        self.nu, self.I0, self.omega, self.n = s.nu, s.I0, s.omega, s.n
        self.spatial = bool(np.any(s.inc != 0)) if spatial is None else spatial
        self.m = 2 if self.spatial else 1  # slow pairs per planet
        self.k = self.m * self.n  # engine's k
        self.D = 2 * self.n + 2 * self.k  # MAIN Lemma 9
        self.B0 = G.B(self.I0, self.nu)
        self.B0_lb = G.B_lower(self.I0, self.nu)
        self.C0 = G.amd(self.I0, s.e, s.inc)
        self.delta_max = self.B0_lb - self.C0
        self.Imin = float(np.min(self.I0))
        self.Kmax = Kmax or {2: 200000, 3: 1500, 4: 160}.get(self.n, 100)
        Ks = np.unique(np.round(np.logspace(0, math.log10(self.Kmax), {2: 180, 3: 80}.get(self.n, 60))).astype(int))
        self.Ks = [int(k) for k in Ks]
        table = Dv.alpha_table(self.omega, self.Ks)
        self.alpha_rad = {k: table[k] for k in self.Ks}
        self._M = {}
        self._F = {}

    # --- Sup-norm data -------------------------------------------------------------------------------------------------
    def M(self, Cball, rho, b=1e-3, rc=RC):
        key = (round(Cball, 12), round(rho, 6), round(b, 6), round(rc, 6))
        if key not in self._M:
            r = Ch.sup_oracle(Ch.Domain(self.nu, self.I0, Cball, rho, b, rc, self.spatial), seed=11)
            self._M[key] = r["M"] if r["ok"] else math.inf
        return self._M[key]

    def rho_holo(self, Cball, b=1e-3, rc=RC):
        return Ch.holo_rho(self.nu, self.I0, Cball, b, rc, self.spatial)

    def tube_R(self, Cball, hi=0.6):
        """Largest uniform sup-norm radius R with the sampled tube (rho = b = rc = R) inside the holomorphy region: the sharp
        replacement of the compactness output R of `exists_strongTube`."""
        lo = 0.0
        rcmax = 0.45 * self.Imin
        for _ in range(12):
            mid = 0.5 * (lo + hi)
            r = Ch.sup_oracle(Ch.Domain(self.nu, self.I0, Cball, mid, mid, min(mid, rcmax), self.spatial), seed=3, N=8000,
                              rounds=6, keep=200)
            if r["ok"]:
                lo = mid
            else:
                hi = mid
        return lo

    def Ldef(self, r=0.0, mode="sharp"):
        """Lipschitz constant of omega/(2 pi) in the max norm.
        'lean' = lpKeplerLip: sum_i 3 nu_i^3/(2 pi (Imin/2)^4).   'sharp' = max_i 3 nu_i^3/(2 pi (I_i - r)^4)."""
        if mode == "lean":
            return float(np.sum(3 * self.nu ** 3 / (TP * (self.Imin / 2) ** 4)))
        return float(np.max(3 * self.nu ** 3 / (TP * (self.I0 - r) ** 4)))

    def budget(self, delta):
        """(r_g, r_1): Omega_B(4 r_g) <= delta/16 and n r_1 + Omega_B(r_1) <= delta/4 (Lipschitz modulus)."""
        lip = G.lip_B(self.I0, self.nu, 0.0)
        rg = delta / (16 * 4 * lip * 1.05)
        for _ in range(4):
            lip = G.lip_B(self.I0, self.nu, min(4 * rg, 0.4 * self.Imin))
            rg = delta / (16 * 4 * lip)
        return rg, delta / (4 * (self.n + lip))

    def gamma(self, tau):
        """min_{|k|<=K} |k.omega| |k|^tau.  K = 2e4 for n = 2: published periods are decimals, so their ratio is exactly rational
        and the true infimum is 0 (HD 109271: k = (26181, -103100)).  The value stands for a Diophantine vector selected
        inside the measurement box and is an upper estimate of its gamma."""
        K = {2: 20000, 3: 2000, 4: 150}.get(self.n, 80)
        return Dv.gamma_of_tau(self.omega, tau, K)


def lean_literal(ctx, delta, tau, R, D0=1.0, gamma=None):
    """Route L.  Returns the theorem's constants for tube radius R (R must lie inside the holomorphy radius)."""
    n, k = ctx.n, ctx.n if not ctx.spatial else 2 * ctx.n
    gamma = ctx.gamma(tau)[0] if gamma is None else gamma
    Cball = ctx.B0 - delta / 4
    rg, r1 = ctx.budget(delta)
    rs = min(4 * rg, R / 4)
    s0 = b0 = R / 16
    s = sig = s0 / math.pi
    w = 2 * b0
    rho = min(rs, ctx.Imin) / 2
    Mv = ctx.M(Cball, R / 2, R / 2, min(R / 2 + 4 * rg, 0.45 * ctx.Imin))
    if not math.isfinite(Mv):
        return None
    M = max(Mv, 1.0)  # `max M 1` in lp_stopped_drift
    M2 = coth(math.pi * sig) ** n * M / TP
    L = ctx.Ldef(mode="lean")
    m1 = gamma / (4 * math.pi * (L * D0 + 1))  # exists_scale_kappa
    m2 = gamma * D0 / (512 * math.pi * (M2 + 1))
    q = tau + 1
    kappa = min(m1, m2) ** (1 / q)
    E = 2 + 6 / (math.pi * s)
    Bb = w ** 2 / (64 * math.pi * k * s * D0)
    if not kappa > 0 or not Bb > 0 or not rho > 0:
        return None  # a parameter that the tube cannot support; the caller keeps the best of the others
    log10_mu_scale = min(0.0, 2 * q * math.log10(kappa / E), 2 * math.log10(Bb), 2 * math.log10(rho / D0))
    r2 = min(r1, rg)
    log10_mu0 = min(log10_mu_scale, 2 * math.log10(r2))
    c = math.pi * s * kappa / 6
    T0 = s * D0 / (5 * M2)
    a = 1 / (2 * q)
    return dict(route="L", delta=delta, tau=tau, gamma=gamma, R=R, s=s, sigma=sig, w=w, M=Mv, M2=M2, L=L, kappa=kappa, E=E,
                c=c, T0=T0, a=a, rg=rg, r1=r1, log10_mu0=log10_mu0, Cball=Cball,
                limits=dict(arith=2 * q * math.log10(kappa / E), slow=2 * math.log10(Bb), tube=2 * math.log10(rho / D0),
                            budget=2 * math.log10(r2)))


def theorem_time(ch, mu):
    """ln T_mu = ln T0 + c mu^-a, in time units; None when mu > mu0."""
    if math.log10(mu) > ch["log10_mu0"]:
        return None
    return math.log(ch["T0"]) + ch["c"] * mu ** (-ch["a"])


def mu_for_time(ch, lnT):
    """Largest mu <= mu0 with T_mu >= exp(lnT): (c/(lnT - ln T0))^(1/a); returns log10."""
    x = lnT - math.log(ch["T0"])
    if x <= 0:
        return ch["log10_mu0"]
    return min(ch["log10_mu0"], (math.log10(ch["c"]) - math.log10(x)) / ch["a"])


def best_literal(ctx, tau_list=None, deltas=None, Rs=None, verbose=False):
    """Maximize mu0 over the proof's remaining freedom (delta, tau, R)."""
    n = ctx.n
    tau_list = tau_list or [n - 1 + x for x in (0.05, 0.1, 0.25, 0.5, 1.0)]
    deltas = deltas or [ctx.delta_max * f for f in (1.0, 0.7, 0.5, 0.3)]
    best = None
    gam = {t: ctx.gamma(t)[0] for t in tau_list}
    for d in deltas:
        Cball = ctx.B0 - d / 4
        Rh = ctx.tube_R(Cball)
        for R in (Rs or [Rh * f for f in (1.0, 0.8, 0.6, 0.4)]):
            if R <= 0:
                continue
            for t in tau_list:
                r = lean_literal(ctx, d, t, R, gamma=gam[t])
                if r is None:
                    continue
                if best is None or r["log10_mu0"] > best["log10_mu0"]:
                    best = r
    return best


# ---------- Route E ---------------------------------------------------------------------------------------------------
@dataclass(frozen=True)
class Opts:
    ball: str = "literal"  # 'literal': |z|^2/2 <= B - delta/4; 'tailored': C0 + n r + slack
    alpha: str = "dioph"  # 'dioph': gamma K^-tau; 'direct': finite-cutoff min over |k| <= K; 'pair': pair modes only
    lip: str = "lean"  # 'lean', 'sharp'
    fnorm: str = "coth"  # 'coth': coth^n sup (wbound_of_sup_bound); 'direct': Sum_k |f_k| e^{2 pi |k| s}
    const: float = 512.0  # 2^7 p q
    cutfac: float = 6.0  # the 6 in exp(2 pi K s/6) and (E4)
    tau: float = None
    label: str = ""


def balls(ctx, opts, delta):
    if opts.ball == "literal":
        return [ctx.B0 - delta / 4]
    return [ctx.C0 * f + 1e-9 for f in (1.02, 1.1, 1.3, 1.7)]


def strip_table(ctx, Cball, b=1e-3):
    """Holomorphy strip and M(rho) on a grid, for one ball and collar.  Cached."""
    key = ("S", round(Cball, 12), b)
    if key not in ctx._F:
        rh = ctx.rho_holo(Cball, b)
        grid = [rh * f for f in (0.15, 0.3, 0.45, 0.6, 0.75, 0.85, 0.95)]
        ctx._F[key] = (rh, [(g, ctx.M(Cball, g, b)) for g in grid if g > 0])
    return ctx._F[key]


def direct_norm(ctx, Cball, slist, N=384, J=60, seed=3, sub_constant=False, b=0.0):
    """F(s) = sup_J Sum_k |f_k(J)| e^{2 pi |k|_1 s}, the Lean WBound norm of f in the radian-free period-one sense, taken over
    sampled REAL J on the ball (f/(2 pi) is the engine's perturbation).  Pair structure: every mode of f has at most two
    nonzero indices, so the sum is computed pair by pair.  Label `estimated`."""
    key = ("D", round(Cball, 12), tuple(round(x, 8) for x in slist), N, J, sub_constant, b)
    if key in ctx._F:
        return ctx._F[key]
    n, nu, I0 = ctx.n, ctx.nu, ctx.I0
    rng = np.random.default_rng(seed)
    zs = Ch._real_slow(rng, J, n, ctx.m, I0, Cball)
    # J on the sphere enlarged by the collar: real proxy for the complex collar of V_r(base)
    zs = zs / np.sqrt(np.maximum(np.sum(zs * zs, axis=1, keepdims=True), 1e-300)) * (math.sqrt(2 * Cball) + b)
    freq = np.fft.fftfreq(N, 1.0 / N)
    k1, k2 = np.meshgrid(freq, freq, indexing="ij")
    absk = np.abs(k1) + np.abs(k2)
    W = [np.exp(TP * s * absk) for s in slist]
    w1 = [np.exp(TP * s * np.abs(freq)) for s in slist]
    best = np.zeros(len(slist))
    means = []
    for t in range(J):
        z = zs[t]
        arrs = []
        for i in range(n):
            zi = z[2 * ctx.m * i: 2 * ctx.m * (i + 1)]
            arrs.append(Ch.single_planet_arrays(nu[i], I0[i], zi, N))
        total = np.zeros(len(slist))
        mean = 0.0
        for i in range(n):
            q_i, p_i = arrs[i]
            c = np.fft.fft(Ch.self_grid(p_i)) / N
            mean += c[0].real
            c[0] = 0
            for a, w in enumerate(w1):
                total[a] += float(np.sum(np.abs(c) * w))
            for j in range(i + 1, n):
                q_j, p_j = arrs[j]
                c2 = np.fft.fft2(Ch.pair_grid(nu[i], nu[j], q_i, p_i, q_j, p_j)) / N ** 2
                mean += c2[0, 0].real
                c2[0, 0] = 0
                ab = np.abs(c2)
                for a, w in enumerate(W):
                    total[a] += float(np.sum(ab * w))
        means.append(mean)
        best = np.maximum(best, total)  # oscillating part; constants below
    means = np.array(means)
    mid = 0.5 * (means.max() + means.min())
    zero = float(np.max(np.abs(means - mid))) if sub_constant else float(np.max(np.abs(means)))
    out = {s: float(b) + zero for s, b in zip(slist, best)}
    ctx._F[key] = out
    return out


def alpha_of(ctx, K, opts, gamma, tau):
    if opts.alpha == "dioph":
        return gamma / TP * K ** (-tau)
    if opts.alpha == "pair":
        return ctx._alpha_pair[K] / TP
    return ctx.alpha_rad[K] / TP


def engine_candidates(ctx, opts, delta, gamma, tau):
    """Yield (K, s, sigma, Cball, alpha, F, rmax) for all grid choices; F = |f/(2 pi)| norm per unit mu.  rmax collects the
    budget (39), the ball containment C0 + n r <= Cball (tailored), the cap RC of the tables and (E3) with w = b."""
    n = ctx.n
    for Cball in balls(ctx, opts, delta):
        rlim = (Cball - ctx.C0) / n if opts.ball == "tailored" else math.inf
        rmax0 = min(ctx.budget(delta)[1], rlim, RC)
        for b in COLLARS:
            rh, tab = strip_table(ctx, Cball, b)
            if rh <= 0.002:
                continue
            if opts.fnorm == "direct":
                ss = [rh / TP * f for f in (0.1, 0.2, 0.3, 0.4, 0.5, 0.6, 0.7, 0.8)]
                Fd = direct_norm(ctx, Cball, ss, sub_constant=opts.label.endswith("c0"), b=b)
                pairs = [(s, 0.0, Fd[s] / TP) for s in ss]
            else:
                pairs = []
                for rho, Mv in tab:
                    if not math.isfinite(Mv):
                        continue
                    st = rho / TP  # s + sigma
                    for frac in (0.3, 0.5, 0.7, 0.85):
                        s, sig = st * frac, st * (1 - frac)
                        pairs.append((s, sig, coth(math.pi * sig) ** n * Mv / TP))
            for s, sig, F in pairs:
                rm = min(rmax0, b * b / (64 * math.pi * ctx.k * s))  # (E3)
                for K in ctx.Ks:
                    if TP * K * s < opts.cutfac:
                        continue
                    al = alpha_of(ctx, K, opts, gamma, tau)
                    if al > 1e-13:  # beyond this the "divisor" is an exact rational relation of the decimal input, or rounding
                        yield K, s, sig, Cball, al, F, rm


def engine_time(ctx, opts, mu, delta=None, gamma=None, tau=None):
    """Best ln T (time units) at the given mu, engine inequalities (E1)-(E5).  None if no parameter passes."""
    delta = ctx.delta_max if delta is None else delta
    best = None
    pref = math.pi / 3 * 6 / opts.cutfac
    for K, s, sig, Cball, al, F, rmax0 in engine_candidates(ctx, opts, delta, gamma, tau):
        eps = mu * F
        L = ctx.Ldef(0.0, "lean" if opts.lip == "lean" else "sharp")
        r_lo = opts.const / 2 * K * eps / al  # (E2)
        r_hi = min(al / (2 * K * L), rmax0)  # (E1) and the budget
        if r_lo > r_hi:
            continue
        r = r_hi
        lnT = math.log(s * r / (5 * eps)) + pref * K * s
        if best is None or lnT > best["lnT"]:
            best = dict(lnT=lnT, K=K, s=s, sigma=sig, Cball=Cball, alpha=al, F=F, r=r, r_lo=r_lo, L=L)
    return best


def engine_mu(ctx, opts, lnT, delta=None, gamma=None, tau=None):
    """Largest mu admitting a certificate for time exp(lnT) (time units); returns dict with log10 mu."""
    delta = ctx.delta_max if delta is None else delta
    best = None
    pref = math.pi / 3 * 6 / opts.cutfac
    for K, s, sig, Cball, al, F, rmax0 in engine_candidates(ctx, opts, delta, gamma, tau):
        L = ctx.Ldef(0.0, "lean" if opts.lip == "lean" else "sharp")
        r = min(al / (2 * K * L), rmax0)  # the time grows with r: take it maximal
        # (E2): mu F <= al r /(const/2 K);  (E5): mu F <= s r exp(pref K s)/(5 T)
        lmu = min(math.log(al * r / (opts.const / 2 * K * F)),
                  math.log(s * r / (5 * F)) + pref * K * s - lnT)
        if best is None or lmu > best["lmu"]:
            best = dict(lmu=lmu, K=K, s=s, sigma=sig, Cball=Cball, alpha=al, F=F, r=r, L=L)
    if best is None:
        return None
    best["log10_mu"] = best["lmu"] / math.log(10)
    return best


# ---------- Route P ---------------------------------------------------------------------------------------------------
def grad_sup(ctx, Cball, rho, b, rc, seed=13, N=4000):
    """Sampled sup of |d_lam f|, |d_I f|, |d_z f| (max-norm in the coordinates) on the complex domain, by central differences."""
    dom = Ch.Domain(ctx.nu, ctx.I0, Cball, rho, b, rc, ctx.spatial)
    rng = np.random.default_rng(seed)
    st = dom.draw(rng, N)
    h = 1e-6
    out = [0.0, 0.0, 0.0]

    def ev(I, lam, z):
        if ctx.spatial:
            q, p, _, _ = Ch.chart_spatial(ctx.nu, I, lam, z[:, 0::4], z[:, 1::4], z[:, 2::4], z[:, 3::4])
        else:
            q, p, _, _ = Ch.chart_planar(ctx.nu, I, lam, z[:, 0::2], z[:, 1::2])
        return Ch.disturbing(ctx.nu, q, p)[0]

    lam = st["lamr"] + 1j * st["lami"]
    z = st["zr"] + b * np.exp(1j * st["phz"])
    I = ctx.I0 + rc * np.exp(1j * st["Iph"])
    def top(v):
        """max |v|, with a singular sample (nan) reported as inf: python's max would silently drop it."""
        m = float(np.max(np.abs(v)))
        return math.inf if math.isnan(m) else m

    for i in range(ctx.n):
        e = np.zeros(ctx.n)
        e[i] = h
        out[0] = max(out[0], top((ev(I, lam + e, z) - ev(I, lam - e, z)) / (2 * h)))
        out[1] = max(out[1], top((ev(I + e, lam, z) - ev(I - e, lam, z)) / (2 * h)))
    for c in range(z.shape[1]):
        e = np.zeros(z.shape[1])
        e[c] = h
        out[2] = max(out[2], top((ev(I, lam, z + e) - ev(I, lam, z - e)) / (2 * h)))
    return out


def paper_route(ctx, mu, gamma, tau, delta=None, ball="literal", direct=False):
    """Lemmas 9-12 with D0, s, b free.  Returns best ln T = ln(2^N/(8 eps)), or None.
    ball 'tailored' uses the small AMD ball (not in the source's statement, only in the same proof)."""
    delta = ctx.delta_max if delta is None else delta
    Cball = ctx.B0 - delta / 4 if ball == "literal" else ctx.C0 * 1.1
    rh, tab = strip_table(ctx, Cball, 1e-4)
    q_D = 1 / (96 * math.e * ctx.D)
    best = None
    rmax = ctx.budget(delta)[1]
    for rho, Mv in tab:
        if not math.isfinite(Mv):
            continue
        s = rho / 4
        A = max(1.0, (2 * tau / (math.e * s)) ** tau) / gamma
        Cs = ((1 + math.exp(-s)) / (1 - math.exp(-s))) ** ctx.n
        for b in (rho / 4, rho / 8, rho / 16, rho / 32, rho / 64):
            key = ("G", round(Cball, 12), round(rho, 6), round(b, 6))
            if key not in ctx._F:
                ctx._F[key] = grad_sup(ctx, Cball, rho, 4 * b, 1e-3)
            gl, gi, gz = ctx._F[key]
            Lw = float(np.max(3 * ctx.nu ** 3 / ctx.I0 ** 4))
            # optimal r balances 3 Lw r/s and Cs mu gl/r
            if not (math.isfinite(gl) and math.isfinite(gi) and math.isfinite(gz)):
                continue
            for f in (0.5, 1.0, 2.0):
                r = min(f * math.sqrt(Cs * mu * gl * s / (3 * Lw)), rmax)
                eps = max(3 * Lw * r / s, Cs * mu * gl / r, Cs * mu * gi / s, Cs * mu * gz / b)
                if eps > 1 / 8:
                    continue
                Nmax = (q_D / (A * eps)) ** (1 / (tau + 1))
                N = math.floor(Nmax)
                if N < 1:
                    continue
                lnT = N * math.log(2) - math.log(8 * eps)
                if best is None or lnT > best["lnT"]:
                    best = dict(lnT=lnT, N=N, r=r, s=s, b=b, eps=eps, A=A, Cs=Cs)
    return best


def paper_mu(ctx, lnT, gamma, tau, ball="literal", delta=None):
    """Largest mu for which paper_route reaches lnT: bisection in log mu."""
    hi, lo = -2.0, -120.0
    if paper_route(ctx, 10 ** lo, gamma, tau, delta, ball) is None:
        return None
    for _ in range(40):
        mid = 0.5 * (hi + lo)
        r = paper_route(ctx, 10 ** mid, gamma, tau, delta, ball)
        if r is not None and r["lnT"] >= lnT:
            lo = mid
        else:
            hi = mid
    return lo


def lean_output_constants(ctx, ch):
    """The remaining constants of LP1 at the literal chain: A_Lambda, A_a, d_*, d_pair, A_osc, mu_2 (formulas of
    `planar_safety_of_prograde`, `barrier_osc_data`, `exists_osc_estimates`)."""
    I, nu, n = ctx.I0, ctx.nu, ctx.n
    delta = ch["delta"]
    m = delta / 2
    Up = I + 4 * ch["rg"]
    Um = I - 4 * ch["rg"]
    dS_f = G.dstar_formula(I, nu, m)
    amax = float(np.max((Up / nu) ** 2))
    Rr = 2 * amax
    P = float(np.max(nu * np.sqrt(2 / dS_f)))
    c = float(np.min(nu)) / (2 * amax)  # keplerEnergy <= -c
    m0, Mm = float(np.min(nu)), 1 + float(np.sum(nu))
    Dd, Pv, c1 = n * P, P / m0, c / Mm
    AE = Dd * (2 * Pv + Dd) / 2 + 1 / dS_f
    AF = Rr * (Dd * (4 * Pv + 2 * Dd) + 1 / dS_f)
    Bb = Pv ** 2 / 2 + 1 / dS_f
    Aa = (AE + Bb) / c1 ** 2
    Ae = AF + 1
    Aper = 2 * Aa + Ae / (2 * c1)
    eStar = 1 - 2 * c * dS_f / Mm
    s0 = min(1.0, c1 / (2 * AE), (1 - eStar) / (2 * Ae))
    return dict(AL=0.5, Aa=(float(np.max(np.abs(Up))) + 1) * (float(np.sum(1 / nu ** 2)) + 1), dstar_formula=dS_f,
                dstar_sharp=G.dstar_sharp(I, nu, m), dpair_sharp=G.dpair_sharp(I, nu, m), Aosc=Mm * Aper,
                log10_mu_osc=math.log10(min(s0 / Mm, dS_f / (2 * Mm * Aper))))


def ln_years(ctx, years):
    return math.log(years / ctx.sys.years_per_unit)


def years(ctx, lnT):
    return math.exp(min(lnT, 690)) * ctx.sys.years_per_unit


def waterfall(ctx, tau, lnT):
    """log10 of the largest mu reaching exp(lnT) as each sharpening is switched on, cumulatively."""
    g = ctx.gamma(tau)[0]
    base = Opts(tau=tau)
    steps = [("free D0, widths, s/sigma", base),
             ("sharp Lipschitz L", replace(base, lip="sharp")),
             ("tailored AMD ball", replace(base, lip="sharp", ball="tailored")),
             ("finite-cutoff divisors alpha(K)", replace(base, lip="sharp", ball="tailored", alpha="direct")),
             ("direct Fourier norm", replace(base, lip="sharp", ball="tailored", alpha="direct", fnorm="direct")),
             ("constant subtracted", replace(base, lip="sharp", ball="tailored", alpha="direct", fnorm="direct", label="c0"))]
    if ctx.n >= 3:
        ctx._alpha_pair = Dv.alpha_pairs(ctx.omega, ctx.Ks)
        steps.append(("pair modes only (hypothetical engine)",
                      replace(base, lip="sharp", ball="tailored", alpha="pair", fnorm="direct", label="c0")))
    a = "pair" if ctx.n >= 3 else "direct"
    steps.append(("constants 2^7 pq -> 8, cutoff 6 -> 2 (hypothetical engine)",
                  replace(base, lip="sharp", ball="tailored", alpha=a, fnorm="direct", label="c0", const=8.0, cutfac=2.0)))
    out = []
    for name, o in steps:
        r = engine_mu(ctx, o, lnT, gamma=g, tau=tau)
        r0 = engine_mu(ctx, o, -math.inf, gamma=g, tau=tau)
        if r is None or r0 is None:
            out.append(dict(step=name, log10_mu=None, log10_mu0=None))
            continue
        out.append(dict(step=name, log10_mu=r["log10_mu"], log10_mu0=r0["log10_mu"], K=r["K"], s=r["s"], sigma=r["sigma"],
                        alpha=r["alpha"], F=r["F"], r=r["r"], Cball=r["Cball"], K0=r0["K"]))
    return out, dict(zip([x[0] for x in steps], [x[1] for x in steps]))
