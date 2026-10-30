#!/usr/bin/env python3
"""Actual sizes of the first (isoenergetic) Newton step of the lunar candidate, package R1, against the derived bounds.

Untrusted tooling, double precision, heuristic: SAMPLED sups (grid points on the distinguished boundary of the
polystrip, corners (+-y, +-y)), not enclosures.  Question answered: how large are the step-0 objects that the
sharp a-posteriori theorem (blueprint/parts/p2s-sharp.tex, blueprint-I/parts/p2s-iso-sharp.tex) bounds by derived
worst-case constants, if one measures them on the actual candidate?  Norms: max norm on vectors, maximum absolute row
sum on matrices.  Every step-0 object is linear (or, for E_lin and the new error, quadratic) in the invariance error E,
so everything is computed for the normalised error  E^ = E / e_act,  e_act := sampled sup_{T_rho} |E|.

1. The invariance error of the R1 candidate (certificates/lunar-spin-orbit/lower_rot.json: v, p~, J~ truncated at
   10^-88, rounded to 2^-318).  In the rotated frame, with X_H' = (P1 - 1, 1, -V_q, -(V_q + V_phi)) and
   d_omega = 2 pi c Dt (Dt e_k = i lambda_k e_k, lambda_k = (nu - 1) k + l, index units, as scripts/spin_orbit/model.py):
       E = c (eta1, 0, -2 pi R3, -2 pi R4),   eta1 = p~ - (nu + Dt v)                       (rounding only),
       R3 = Dt p~ + 2 eps sum_m A_m Im(e_{s_m} exp(2 i v)),                                  (= R(v) + Dt eta1)
       R4 = Dt (p~ + J~) + eps sum_m A_m (2 - m) Im(e_{s_m} exp(2 i v)),   s_m = (2, 2 - m).
   (So E = (0, 0, -c r, (p - 1) c r) + c (0, 0, 0, 2 pi Dt(J~ - J_exact)), not exactly (0, 0, -r, (p - 1) r): the
   truncation of J~ adds the last term.)  The coefficients are computed EXACTLY (integers, Q(sqrt5)) with the stored
   witness E~ of exp(2 i v), as scripts/spin_orbit/rot_build.py does for the certificate (R3_l1w, R4_l1w are reproduced),
   plus the witness correction  dE = exp(2 i v) - E~ = (E_full - E~) - 2 i dv E_full + O(dv^2) + O(1e-130), where
   E_full, v_full are the 440-bit SO-GEN data (lower.json) and dv = v_full - v exactly; the correction is computed in
   double precision by exact differences and a direct (FFT-free) convolution, so no 1e-78 quantity is ever obtained by
   cancellation in floating point.  Cross-check: the linearisation  R(v) = R(v_full) - Dt^2 dv - 4 eps sum A_m
   Re(e_m E_full) dv  (with R(v_full) ~ 1e-121 neglected) agrees coefficientwise.
2. The frame (L, B, N, T, Y, DH) of scripts/apost_sharp/r1_norms.py at time scale c = 7/4, evaluated directly on each
   shifted grid {Im theta = y}; R (zero-average solution of d_omega u = g) and d_omega are Fourier multipliers applied on
   the same shifted grid (the zero mode is shift invariant, which is checked).
3. The isoenergetic step (blueprint-I/parts/p1-iso-linear.tex, Lemma border-solve, HL19 Lemma 6.1 in this sign
   convention): eta^L = -B L^T E, eta^N = L^T Omega0 E, eta^w = -(<H o K> - E0)/e_act; u^N = R eta^N;
   (xi0, xi^w) = TT^-1 (<eta^L> + <T u^N>, eta^w + <Y u^N>), TT = [[<T>, omega], [<Y>, 0]]; xi^N = xi0 - u^N;
   g^L = T xi^N + omega xi^w - eta^L; xi^L = R g^L; DeltaK = L xi^L + N xi^N; d_omega xi = (g^L, -eta^N);
   Omega_K = R(-(DE)^T Omega0 L - L^T Omega0 DE); E_sym = diag(Omega_K, B Omega_K B);
   E_red = [[B L^T DE, 0], [-L^T Omega0 DE, (DE)^T Omega0 N]];
   E_lin = E_red xi + Omega0 E_sym d_omega xi - (0, Omega_K omega) xi^w   (Lemma bpI:p1:reduced);
   new error  Ebar = P S^-1 E_lin + D2X + xi^w d_omega DeltaK, measured at leading order (S^-1 = I + O(e),
   D2X = (1/2) D^2 X_H[DeltaK, DeltaK]), and the bound-structured value |P| 2 |E_lin| + (M2/2)|DeltaK|^2 + |xi^w||d_omega DeltaK|.
4. The derived bounds of the sharp iso design (Definition bpI:p2s:constants, transcribed from
   scripts/apost_sharp/thresholds.py `sharp(..., iso=True)`, R1 inputs of `package_R1`, Russmann data kappa = 1,
   c_R = cohConstR 2 1), at delta = delta0 = (rho - rho_inf)/6 and gamma = gbar = c/(42 s).

Usage:  python3 -I scripts/apost_sharp/step0_actual.py [--json OUT] [--grid N1 N2] [--check]
  --grid  FFT grid (default 1024 256; about 20 s, 0.9 GB);  --check  also run at the doubled grid (about 3.5 min, 3.3 GB)
  and report the largest relative change of the sampled sups (noise-level quantities xi0, xi^w excluded).
"""
import json, math, os, sys, time
import numpy as np
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, os.path.join(ROOT, "scripts", "spin_orbit"))
sys.path.insert(0, HERE)
import model                                   # noqa: E402  exact model data
import r1_norms                                # noqa: E402  rotated-frame candidate and frame objects
import thresholds as thr                       # noqa: E402  sharp constants (exact)

CERT = os.path.join(ROOT, "certificates", "lunar-spin-orbit")
OM = r1_norms.OM                               # Omega0
EPSA = {m: model.EPS * model.A_EXACT[m] for m in model.M_MODES}       # eps A_m (exact)
EPSA_F = {m: float(q) for m, q in EPSA.items()}
SH = model.SHIFT                               # m -> (2, 2 - m)
TWO_PI = 2 * math.pi

# package R1 (thresholds.package_R1; CONSTANTS-STUDY 2.2; owner ruling O5)
RHO = 1 / 70
RHOINF = RHO / 1000
C_TIME = 7 / 4
S_RAY = 1 + 1e-6
LAM = 3
DELTA0 = (RHO - RHOINF) / (2 * LAM)
M2_R1 = 1.05 * 1.034                            # |D^2 X_h| majorant of R1 (r1_norms: sampled 1.0342, x 1.05)
KBOX, LBOX = 320, 90                            # dense coefficient box for the residual (|k| <= KBOX, |l| <= LBOX)


# =================================================================================================== 1. residual
def _load(name):
    return json.load(open(os.path.join(CERT, name)))


def residual_exact_poly(d):
    """Exact residual polynomials of the stored candidate, with the stored witness E~ of exp(2 i v).
    Returns (rho3, rho4, eta1, energy): dicts kappa -> float for R3 = sum i rho3 e_kappa, R4 = sum i rho4 e_kappa,
    eta1 = sum eta1 e_kappa (real even), and the exact energy error <p~^2/2 + J~ + V_{E~}> (time scale 1)."""
    S = d["scale_bits"]
    assert d["which"] == "lower" and d["frame"] == "rotated" and d["J0_scale_bits"] == S + 1
    b = {(k, l): int(n) for k, l, n in d["v_sin"]}
    P = {(0, 0): 2 * int(d["p0"])}                                      # full-lattice values at scale S+1
    for k, l, n in d["p_cos"]:
        P[(k, l)] = int(n); P[(-k, -l)] = int(n)
    J = {(0, 0): int(d["J0"])}
    for k, l, n in d["J_cos"]:
        J[(k, l)] = int(n); J[(-k, -l)] = int(n)
    E = {(k, l): int(n) for k, l, n in d["E_re"]}                       # scale S, real coefficients
    DA = 1
    for q in EPSA.values():
        DA = DA * q.denominator // math.gcd(DA, q.denominator)
    AINT = {m: int(EPSA[m] * DA) for m in EPSA}                          # eps A_m = AINT_m / DA
    keys = set(P) | set(J)
    for (k, l) in E:
        for m, (a, c) in SH.items():
            keys.add((k + a, l + c)); keys.add((-k - a, -l - c))
    keys.discard((0, 0))
    T = 500
    SQ5 = math.isqrt(5 << (2 * T))                                       # floor(sqrt5 2^T)
    Den = (3118 * DA) << (S + 1)
    rho3, rho4 = {}, {}
    for (k, l) in sorted(keys):
        la, lb = 3118 * l - 79 * k, k                                    # 3118 lambda = la + lb sqrt5 (lower)
        Pv, Jv = P.get((k, l), 0), J.get((k, l), 0)
        G3 = G4 = 0
        for m, (a, c) in SH.items():
            diff = E.get((-k - a, -l - c), 0) - E.get((k - a, l - c), 0)
            G3 += AINT[m] * diff; G4 += AINT[m] * (2 - m) * diff
        X3, Y3 = DA * la * Pv + 2 * 3118 * G3, DA * lb * Pv
        X4, Y4 = DA * la * (Pv + Jv) + 3118 * G4, DA * lb * (Pv + Jv)
        rho3[(k, l)] = (X3 * (1 << T) + Y3 * SQ5) / (Den << T)           # correctly rounded big-int division
        rho4[(k, l)] = (X4 * (1 << T) + Y4 * SQ5) / (Den << T)
    # eta1 = p~ - nu - Dt v: kappa != 0 full-lattice value (c_kappa - lambda b_kappa)/2, zero mode p0/2^S - nu
    eta1 = {}
    for k, l, n in d["p_cos"]:
        bb = b.get((k, l), 0)
        num = (int(n) * 3118 << T) - ((3118 * l - 79 * k) * (1 << T) + k * SQ5) * bb
        val = num / ((3118 << T) << (S + 1))
        eta1[(k, l)] = val; eta1[(-k, -l)] = val
    # nu = 1 - (79 - sqrt5)/3118 = (3039 + sqrt5)/3118
    eta1[(0, 0)] = ((int(d["p0"]) * 3118 << T) - ((3039 << T) + SQ5) * (1 << S)) / ((3118 << T) << S)
    # energy <p~^2/2 + J~ + V_{E~}>: zero mode of p~^2 is sum P_k P_-k (scale 2S+2); V_E zero mode -sum eps A_m E_{-s_m}
    p2_0 = sum(v * P.get((-k, -l), 0) for (k, l), v in P.items())
    en = F(p2_0, 1 << (2 * S + 3)) + F(J[(0, 0)], 1 << (S + 1))
    for m, (a, c) in SH.items():
        en -= EPSA[m] * F(E.get((-a, -c), 0), 1 << S)
    return rho3, rho4, eta1, float(en)


class Box:
    """Dense coefficient array over |k| <= K, |l| <= L (index [k + K, l + L])."""

    def __init__(self, K=KBOX, L=LBOX):
        self.K, self.L = K, L
        self.a = np.zeros((2 * K + 1, 2 * L + 1))

    def add(self, d, scale=1.0):
        for (k, l), v in d.items():
            self.a[k + self.K, l + self.L] += v * scale
        return self

    def shift_get(self, a, c, neg=False):
        """array X with X[kappa] = self[kappa - s] (neg=False) or self[-kappa - s] (neg=True), s = (a, c)."""
        K, L = self.K, self.L
        src = self.a[::-1, ::-1] if neg else self.a                     # reversed: src[kappa] = self[-kappa]
        out = np.zeros_like(self.a)                                      # out[kappa] = src[kappa - (da, dc)]
        da, dc = (a, c) if not neg else (-a, -c)
        ks = slice(max(0, da), 2 * K + 1 + min(0, da)); kd = slice(max(0, -da), 2 * K + 1 + min(0, -da))
        ls = slice(max(0, dc), 2 * L + 1 + min(0, dc)); ld = slice(max(0, -dc), 2 * L + 1 + min(0, -dc))
        out[ks, ls] = src[kd, ld]
        return out


def box_from(a):
    b = Box(); b.a = a
    return b


def model_nu():
    return 1 - r1_norms.ALPHA


def residual_coefficients(log=print):
    """Full residual coefficients (time scale 1, before the factor c): dense real arrays rho3, rho4 (R = sum i rho e_k),
    eta1 (real), plus diagnostics."""
    t0 = time.time()
    d = _load("lower_rot.json")
    dfull = _load("lower.json")
    S, PF = d["scale_bits"], dfull["scale_bits"]
    sh = PF - S
    rho3, rho4, eta1, energy = residual_exact_poly(d)
    log("  exact polynomial residual: %d keys (%.1fs)" % (len(rho3), time.time() - t0))
    # witness correction dE = (E_full - E~) - 2 i dv E_full   (real coefficients)
    Et = {(k, l): int(n) for k, l, n in d["E_re"]}
    Ef = {(k, l): int(n) for k, l, n in dfull["E_re"]}
    dE1 = {}
    for kk in set(Et) | set(Ef):
        x = Ef.get(kk, 0) - (Et.get(kk, 0) << sh)
        if x:
            dE1[kk] = x / 2.0 ** PF
    bt = {(k, l): int(n) for k, l, n in d["v_sin"]}
    bf = {(k, l): int(n) for k, l, n in dfull["v_sin"]}
    ddv = {}                                                             # -2 i dv: real full-lattice coefficients
    for kk in set(bt) | set(bf):
        x = bf.get(kk, 0) - (bt.get(kk, 0) << sh)                        # dv = sum db sin, db = x / 2^PF
        if x:
            db = x / 2.0 ** PF
            ddv[kk] = -db; ddv[(-kk[0], -kk[1])] = db                    # -2i (db/(2i)) e_k - 2i (-db/(2i)) e_-k
    Dv = Box().add(ddv)
    Efull = {kk: n / 2.0 ** PF for kk, n in Ef.items()}
    big = {kk: v for kk, v in Efull.items() if abs(v) > 1e-30}           # E_full truncated at 1e-30 for the product
    prod = np.zeros_like(Dv.a)
    for (k, l), v in big.items():
        prod += v * Dv.shift_get(k, l)                                   # (-2 i dv E_full)[kappa] = sum E_s ddv[kappa - s]
    dEbox = Box().add(dE1)
    dEbox.a += prod
    G3 = np.zeros_like(prod); G4 = np.zeros_like(prod)
    for m, (a, c) in SH.items():
        diff = dEbox.shift_get(a, c, neg=True) - dEbox.shift_get(a, c)  # dE[-kappa - s] - dE[kappa - s]
        G3 += EPSA_F[m] * diff; G4 += EPSA_F[m] * (2 - m) * diff
    R3 = Box().add(rho3); R4 = Box().add(rho4); H1 = Box().add(eta1)
    R3w, R4w = G3, G4 / 2
    # cross-check (row P1): R3 = Dt eta1 + R(v) and R(v) = R(v_full) - Dt^2 dv - 4 W dv + O(dv^2), W = sum eps A_m
    # Re(e_m E_full); R(v_full) (~1e-121, the SO-GEN residual) is neglected.  In the "rho" convention (coefficient / i):
    # dv_k = ddv_k/(-2i) = i ddv_k/2 -> rho(dv) = ddv/2;  -Dt^2 -> +lambda^2;  Dt eta1 -> lambda eta1.
    kk_, ll_ = np.meshgrid(np.arange(-KBOX, KBOX + 1), np.arange(-LBOX, LBOX + 1), indexing="ij")
    lam = (model_nu() - 1) * kk_ + ll_
    dvc = Box().add({kk: v / 2 for kk, v in ddv.items()}).a
    W = np.zeros_like(prod)                                              # real coefficients
    for m, (a, c) in SH.items():
        Wm = {}
        for (k, l), v in big.items():
            Wm[(k + a, l + c)] = Wm.get((k + a, l + c), 0) + v / 2
            Wm[(-k - a, -l - c)] = Wm.get((-k - a, -l - c), 0) + v / 2
        W += EPSA_F[m] * Box().add(Wm).a
    it = np.argwhere(np.abs(W) > 1e-30)
    conv = np.zeros_like(prod)
    for (i, j) in it:
        conv += W[i, j] * box_from(dvc).shift_get(i - KBOX, j - LBOX)
    rhoB = lam ** 2 * dvc - 4 * conv + lam * H1.a
    rhoA = R3.a + R3w
    w = np.exp(TWO_PI * RHO * (np.abs(kk_) + np.abs(ll_)))
    diag = dict(energy_unscaled=energy,
                R3_poly_l1w=float((np.abs(R3.a) * w).sum()), R4_poly_l1w=float((np.abs(R4.a) * w).sum()),
                R3_witness_l1w=float((np.abs(R3w) * w).sum()), R4_witness_l1w=float((np.abs(R4w) * w).sum()),
                R3_total_l1w=float((np.abs(rhoA) * w).sum()), R4_total_l1w=float((np.abs(R4.a + R4w) * w).sum()),
                eta1_l1w=float((np.abs(H1.a) * w).sum()),
                crosscheck_rowP1_l1w_diff=float((np.abs(rhoA - rhoB) * w).sum()),
                dv_prod_term_l1w=float((np.abs(prod) * w).sum()), dE_dropped_l1w=float((np.abs(dEbox.a - prod) * w).sum()))
    log("  witness correction and cross-check (%.1fs)" % (time.time() - t0))
    return dict(rho3=rhoA, rho4=R4.a + R4w, eta1=H1.a, kk=kk_, ll=ll_, diag=diag)


# =================================================================================================== 2. grids
class Grid:
    def __init__(self, N1, N2):
        self.N1, self.N2 = N1, N2
        self.cand = r1_norms.Cand("lower", N1, N2)
        self.kk, self.ll = self.cand.kk, self.cand.ll
        self.nu = self.cand.nu
        self.lam = (self.nu - 1) * self.kk + self.ll
        self.mult = 2j * math.pi * C_TIME * self.lam                    # d_omega multiplier
        self.omega = C_TIME * np.array([self.nu - 1, 1.0])

    def coef_grid(self, arr, kk, ll):
        """place a dense box (indices kk, ll) into an N1 x N2 coefficient grid (must not wrap)."""
        assert 2 * np.abs(kk).max() < self.N1 and 2 * np.abs(ll).max() < self.N2, "grid too small for the box"
        C = np.zeros((self.N1, self.N2), complex)
        np.add.at(C, (kk % self.N1, ll % self.N2), arr)
        return C

    def eval(self, C, y):
        """values on the grid at Im theta = y of sum C_k e_k."""
        w = np.exp(-TWO_PI * (self.kk * y[0] + self.ll * y[1]))
        return np.fft.ifft2(C * w) * (self.N1 * self.N2)

    def coef_at(self, vals):
        """shifted coefficients (C_k e^{-2 pi k.y}) of grid values on a shifted grid; axes (0, 1)."""
        return np.fft.fft2(vals, axes=(0, 1)) / (self.N1 * self.N2)

    def solve(self, vals):
        """R: zero-average solution of d_omega u = g on the same shifted grid; returns (u, <g>)."""
        Ch = self.coef_at(vals)
        avg = Ch[0, 0].copy()
        Ch[0, 0] = 0
        m = self.mult.reshape(self.mult.shape + (1,) * (vals.ndim - 2))
        with np.errstate(divide="ignore", invalid="ignore"):
            Ch = np.where(m != 0, Ch / np.where(m != 0, m, 1), 0)
        return np.fft.ifft2(Ch, axes=(0, 1)) * (self.N1 * self.N2), avg

    def domega(self, vals):
        m = self.mult.reshape(self.mult.shape + (1,) * (vals.ndim - 2))
        return np.fft.ifft2(self.coef_at(vals) * m, axes=(0, 1)) * (self.N1 * self.N2)


def vmax(v):
    return float(np.abs(v).max())


def mv(Mx, v):
    return np.einsum("...ij,...j->...i", Mx, v)


def mm(A, B):
    return np.einsum("...ij,...jk->...ik", A, B)


def tr(A):
    return np.swapaxes(A, -1, -2)


def d2xh(g, dK, c):
    """(1/2) D^2 X_H(K)[dK, dK] for H = c (P1^2/2 - P1 + P2 + V(Q1 + Q2, Q2)), V = -sum eps A_m cos 2 pi (2 q - m phi)."""
    dq = dK[..., 0] + dK[..., 1]; df = dK[..., 1]
    d2Vq = 0; d2Vf = 0
    for m in model.M_MODES:
        X = TWO_PI * (2 * g["q"] - m * g["ph"])
        a = EPSA_F[m]; s2 = (TWO_PI * (2 * dq - m * df)) ** 2 * np.sin(X)
        d2Vq = d2Vq - a * 2 * TWO_PI * s2                               # V_q = sum a 4 pi sin X
        d2Vf = d2Vf + a * m * TWO_PI * s2                               # V_phi = -sum a 2 pi m sin X
    out = np.zeros(dK.shape, complex)
    out[..., 2] = -c * d2Vq / 2
    out[..., 3] = -c * (d2Vq + d2Vf) / 2
    return out


# =================================================================================================== 3. the step
def residual_grid(G, res):
    """normalised-error ingredients on grid G: coefficient grids of E (time scale c) per component."""
    kk, ll = res["kk"], res["ll"]
    C = [G.coef_grid(C_TIME * res["eta1"], kk, ll), None,
         G.coef_grid(-TWO_PI * C_TIME * 1j * res["rho3"], kk, ll),
         G.coef_grid(-TWO_PI * C_TIME * 1j * res["rho4"], kk, ll)]
    C[1] = np.zeros_like(C[0])
    return C


def E_at(G, Cs, y, scale):
    Ev = np.stack([G.eval(C, y) for C in Cs], axis=-1) / scale
    tk, tl = 2j * math.pi * G.kk, 2j * math.pi * G.ll
    DE = np.stack([np.stack([G.eval(C * tk, y), G.eval(C * tl, y)], axis=-1) for C in Cs], axis=-2) / scale
    return Ev, DE


def step_at(G, Cs, e_act, y, consts=None, eta_w=0.0, keep=()):
    """All step-0 objects at the shifted grid Im theta = y.  consts = (xi0, xiw) fixes the constants; else they are
    computed here.  Returns (sups, consts, averages, checks, solution of the bordered system, kept arrays)."""
    o = r1_norms.objects(G.cand, y[0], y[1], C_TIME)
    L, B, N, T, Y, g = o["L"], o["B"], o["N"], o["T"], o["Y"], o["g"]
    del o
    Ev, DE = E_at(G, Cs, y, e_act)
    LT = tr(L)
    etaL = -mv(mm(B, LT), Ev)
    etaN = mv(LT, mv(OM, Ev))
    uN, avg_etaN = G.solve(etaN)
    avgs = dict(etaN=avg_etaN, etaL=G.coef_at(etaL)[0, 0], TuN=G.coef_at(mv(T, uN))[0, 0],
                YuN=G.coef_at(np.einsum("...j,...j->...", Y, uN)[..., None])[0, 0, 0],
                T=G.coef_at(T)[0, 0], Y=G.coef_at(Y)[0, 0])
    TT = np.zeros((3, 3), complex)
    TT[:2, :2] = avgs["T"]; TT[:2, 2] = G.omega; TT[2, :2] = avgs["Y"]
    rhs = np.concatenate([avgs["etaL"] + avgs["TuN"], [eta_w + avgs["YuN"]]])
    sol = np.linalg.solve(TT, rhs)
    if consts is None:
        consts = (sol[:2], sol[2])
    xi0, xiw = consts
    xiN = xi0 - uN                                                      # Lemma bpI:p1:border-solve
    gL = mv(T, xiN) + G.omega * xiw - etaL
    xiL, avg_gL = G.solve(gL)
    dK = mv(L, xiL) + mv(N, xiN)                                        # DeltaK_0 = P xi
    # geometry (Lemma bp:p2s:geometry; frame identities (b), (d), (e))
    dOm = -mm(mm(tr(DE), OM), L) - mm(mm(LT, OM), DE)                   # d_omega Omega_K
    OmK, avg_dOm = G.solve(dOm)                                         # <Omega_K> = 0 (exactness)
    BOB = mm(mm(B, OmK), B)
    r11 = mm(mm(B, LT), DE); r21 = -mm(mm(LT, OM), DE); r22 = mm(mm(tr(DE), OM), N)   # E_red blocks
    Ered_rows = np.concatenate([np.abs(r11).sum(-1), np.abs(r21).sum(-1) + np.abs(r22).sum(-1)], axis=-1)
    # E_lin = E_red xi + Omega0 E_sym d_omega xi - (0, Omega_K omega) xi^w,  d_omega xi = (g^L, -eta^N)
    ElinL = mv(r11, xiL) + mv(BOB, etaN)
    ElinN = mv(r21, xiL) + mv(r22, xiN) + mv(OmK, gL) - mv(OmK, np.broadcast_to(G.omega, gL.shape)) * xiw
    PElin = mv(L, ElinL) + mv(N, ElinN)
    dwdK = G.domega(dK)
    Q2 = d2xh(g, dK, C_TIME)
    Ebar = PElin + Q2 + xiw * dwdK                                      # leading order of Lemma bpI:p2:newton-error
    rs = lambda Mx: float(np.abs(Mx).sum(-1).max())
    out = dict(E=vmax(Ev), DE=rs(DE), T=rs(T), etaL=vmax(etaL), etaN=vmax(etaN), uN=vmax(uN), xiN=vmax(xiN),
               gL=vmax(gL), xiL=vmax(xiL), xi=max(vmax(xiL), vmax(xiN)), dK=vmax(dK),
               dxi=max(vmax(gL), vmax(etaN)), OmK=rs(OmK), BOB=rs(BOB), Esym=max(rs(OmK), rs(BOB)),
               Ered=float(Ered_rows.max()), Elin=max(vmax(ElinL), vmax(ElinN)),
               P=float((np.abs(L).sum(-1) + np.abs(N).sum(-1)).max()), PElin=vmax(PElin), D2X=vmax(Q2),
               xiw_dwdK=vmax(xiw * dwdK), Ebar=vmax(Ebar), dwdK=vmax(dwdK))
    checks = dict(avg_etaN=float(np.abs(avg_etaN).max()), avg_gL=float(np.abs(avg_gL).max()),
                  avg_dOmega=float(np.abs(avg_dOm).max()))
    loc = locals()
    kept = {k: loc[k] for k in keep}
    return out, consts, avgs, checks, sol, kept


def spectrum(G, pair, y):
    """weighted Fourier mass sum_kappa max_i |f_i,kappa| exp(2 pi y |kappa|_1) of a real-on-reals vector function f by
    |kappa|_1 bins, read off from its values at the corners (y, y) and (y, -y): there the shifted coefficients of the
    quadrants {k <= 0, l <= 0} and {k <= 0, l > 0} are |f_kappa| exp(2 pi y |kappa|_1); the other half by realness."""
    c1 = np.abs(G.coef_at(pair[0])).max(axis=-1)
    c2 = np.abs(G.coef_at(pair[1])).max(axis=-1)
    k, l = G.kk, G.ll
    m = np.where((k <= 0) & (l <= 0), c1, 0.0) + np.where((k <= 0) & (l > 0), c2, 0.0)
    n1 = np.abs(k) + np.abs(l)
    tot = m.sum()
    hist = {}
    for lo in (0, 20, 40, 60, 80, 100, 120, 140, 160, 180, 200, 240, 280, 320, 400):
        hi = {0: 20, 20: 40, 40: 60, 60: 80, 80: 100, 100: 120, 120: 140, 140: 160, 160: 180, 180: 200, 200: 240,
              240: 280, 280: 320, 320: 400, 400: 10 ** 6}[lo]
        hist["%d-%d" % (lo, hi - 1)] = float(m[(n1 >= lo) & (n1 < hi)].sum() / tot)
    return hist


def run(N1, N2, res, log=print):
    t0 = time.time()
    G = Grid(N1, N2)
    Cs = residual_grid(G, res)
    # e_act: sampled sup over T_rho (corners) of max_i |E_i|; split by component
    e_act = 0.0; comp = np.zeros(4)
    for y in ((RHO, RHO), (RHO, -RHO)):
        Ev = np.stack([G.eval(C, y) for C in Cs], axis=-1)
        e_act = max(e_act, vmax(Ev)); comp = np.maximum(comp, np.abs(Ev).max(axis=(0, 1)))
    # row P2 decomposition: E4 = -(p - 1) E3 - d_omega(J~ - J_exact)  (J~ - J_exact: truncation of J), on T_rho
    jt = pr = 0.0
    for y in ((RHO, RHO), (RHO, -RHO)):
        g = G.cand.geometry(*y)
        pE3 = (g["p"] - 1) * G.eval(Cs[2], y)
        jt = max(jt, vmax(G.eval(Cs[3], y) + pE3)); pr = max(pr, vmax(pE3))
    eta_w = -C_TIME * res["diag"]["energy_unscaled"] / e_act
    _, consts, avgs0, chk0, sol0, _ = step_at(G, Cs, e_act, (0.0, 0.0), eta_w=eta_w)
    xi0, xiw = consts
    strips = {"rho": RHO, "rho-delta0": RHO - DELTA0, "rho-2delta0": RHO - 2 * DELTA0}
    sups = {}; maxdev = 0.0; chks = dict(chk0); spec = {}
    for name, yy in strips.items():
        acc = {}; pairs = {"Ev": [], "dK": [], "Ebar": []}
        for y in ((yy, yy), (yy, -yy)):
            o, _, av, ck, sol, kept = step_at(G, Cs, e_act, y, consts=consts, eta_w=eta_w, keep=tuple(pairs))
            for k_, v_ in o.items():
                acc[k_] = max(acc.get(k_, 0.0), v_)
            maxdev = max(maxdev, float(np.abs(sol - sol0).max()))
            for k_, v_ in ck.items():
                chks[k_] = max(chks.get(k_, 0.0), v_)
            for k_ in pairs:
                pairs[k_].append(kept[k_])
            del kept
        sups[name] = acc
        spec[name] = {k_: spectrum(G, v_, yy) for k_, v_ in pairs.items()}
        del pairs
    T0 = np.real(avgs0["T"])
    log("  grid %dx%d done (%.1fs)" % (N1, N2, time.time() - t0))
    return dict(grid=[N1, N2], e_act=e_act, e_act_components=comp.tolist(), Jtrunc_part_row4=jt / e_act, pm1_E3_part_row4=pr / e_act,
                eta_w=eta_w, xi0=np.real(xi0).tolist(), xi0_abs=float(np.abs(xi0).max()), xiw=float(np.real(xiw)),
                xi0_imag=float(np.abs(np.imag(xi0)).max()), sups=sups, spectra=spec, avgT=T0.tolist(),
                avgY=np.real(avgs0["Y"]).tolist(), shift_invariance_of_constants=maxdev, checks=chks)


# =================================================================================================== 4. derived
def derived_constants():
    """Definition bpI:p2s:constants (iso) for R1, Russmann data; transcription of thresholds.sharp(iso=True)."""
    p, gamma = thr.package_R1()
    cR = thr.cohConstR_lean(2, 1)
    n = F(2); kappa = 1
    M, sK, sB, sT, g = p["M"], p["sK"], p["sB"], p["sT"], p["gbar"]
    Theta = 2 * n * sK * sB * (M + 1)
    C_Om = 2 * n * (n + 1) * cR * sK
    C_sym = max(F(1), sB ** 2) * C_Om
    C_red = 2 * n * sK * max(n * sB, n + sB)
    C_T0 = 4 * n * M * sK ** 2 * sB ** 2
    H_T = C_T0 + 1
    C_S = sT * max(2 * n * sK * sB * g + 2 * n * cR * sK * H_T, g + 2 * n * cR * M * sK ** 2 * sB)
    C_xiN = C_S + 2 * n * cR * sK
    C_g = H_T * C_xiN + Theta * C_S + 2 * n * sK * sB * g
    C_dxi = max(C_g, 2 * n * sK * g)
    C_xi = max(cR * C_g, g * C_xiN)
    C_DK = sK * (cR * C_g + sB * g * C_xiN)
    C_Dw = Theta * g * C_S
    C_P = (M * sK + n) * (1 + sB) + 2 * n * sK ** 2 * sB ** 2 * (2 * M * sK + n + 1)
    C_dK = C_P * C_xi + sK * (1 + sB) * g * C_dxi
    C_lin = C_red * C_xi + C_sym * C_dxi + Theta * C_Om * C_S
    C_E1 = 2 * sK * (1 + sB) * g ** 2 * C_lin + M / 2 * C_DK ** 2 + g * C_S * C_dK
    C_E2 = g * n * (2 * n * sK * g + Theta * C_Om) * cR * C_g + M / 2 * C_DK ** 2
    C_E = max(C_E1, C_E2)
    ref = thr.sharp(n=2, tau=1, kappa=1, cR=cR, M=M, sK=sK, sB=sB, sT=sT, mu=p["mu"], rho=p["rho"],
                    rhoinf=p["rhoinf"], gbar=g, nu=p["nu"], iso=True)
    assert ref["C_DK"] == C_DK and ref["C_E"] == C_E and ref["C_Dw"] == C_Dw and ref["H_T"] == H_T
    d0 = float(ref["delta0"]); gm = float(gamma)
    u = 1 / (gm * d0 ** kappa); U2 = 1 / (gm ** 2 * d0 ** (2 * kappa))
    fl = lambda q: float(q)
    bounds = {   # derived bound per unit epsilon (per epsilon^2 for E_lin, Ebar), at delta = delta0
        "DE": (fl(n) / d0, "n/delta0", "rho-delta0"),
        "T": (fl(H_T), "H_T = C_T0 + 1", "rho-delta0"),
        "Ered": (fl(C_red) / d0, "C_red/delta0", "rho-delta0"),
        "OmK": (fl(C_Om) * u / d0, "C_Omega/(gamma delta0^2)", "rho-2delta0"),
        "Esym": (fl(C_sym) * u / d0, "C_sym/(gamma delta0^2)", "rho-2delta0"),
        "etaL": (fl(2 * n * sK * sB), "2n sK sB", "rho"),
        "etaN": (fl(2 * n * sK), "2n sK", "rho"),
        "uN": (fl(cR * 2 * n * sK) * u, "c_R 2n sK/(gamma delta0)", "rho-delta0"),
        "xi0": (fl(C_S) * u, "C_S/(gamma delta0)", "const"),
        "xiw": (fl(C_S) * u, "C_S/(gamma delta0)", "const"),
        "xiN": (fl(C_xiN) * u, "C_xiN/(gamma delta0)", "rho-delta0"),
        "gL": (fl(C_g) * u, "C_g/(gamma delta0)", "rho-delta0"),
        "xiL": (fl(cR * C_g) * U2, "c_R C_g/(gamma^2 delta0^2)", "rho-2delta0"),
        "xi": (fl(C_xi) * U2, "C_xi/(gamma^2 delta0^2)", "rho-2delta0"),
        "dK": (fl(C_DK) * U2, "C_DK/(gamma^2 delta0^2)", "rho-2delta0"),
        "dxi": (fl(C_dxi) * u, "C_dxi/(gamma delta0)", "rho-2delta0"),
        "Dw": (fl(C_Dw) * U2, "C_Dw/(gamma^2 delta0^2)", "const"),
        "dwdK": (fl(C_dK) * U2, "C_dK/(gamma^2 delta0^2)", "rho-2delta0"),
        "Elin": (fl(C_lin) * U2 / d0, "C_lin/(gamma^2 delta0^3)", "rho-2delta0"),
        "Ebar": (fl(C_E) * U2 ** 2, "C_E/(gamma^4 delta0^4)", "rho-2delta0"),
    }
    consts = {k: float(v) for k, v in dict(cR=cR, M=M, sK=sK, sB=sB, sT=sT, gamma=gamma, Theta=Theta, C_Omega=C_Om,
                                             C_sym=C_sym, C_red=C_red, H_T=H_T, C_S=C_S, C_xiN=C_xiN, C_g=C_g,
                                             C_dxi=C_dxi, C_xi=C_xi, C_DK=C_DK, C_Dw=C_Dw, C_dK=C_dK, C_lin=C_lin,
                                             C_E1=C_E1, C_E2=C_E2, C_E=C_E).items()}
    consts["delta0"] = d0
    return consts, bounds


# =================================================================================================== 5. support
def support(res):
    """Fourier content of E^ on T_rho: weighted mass by |kappa|_1 and by |lambda|, smallest |lambda| on the support."""
    kk, ll = res["kk"], res["ll"]
    w = np.exp(TWO_PI * RHO * (np.abs(kk) + np.abs(ll)))
    mass = np.maximum(np.abs(res["rho3"]), np.abs(res["rho4"])) * w      # rows P1, P2 dominate (eta1 ~ 1e-96)
    tot = mass.sum()
    lam = np.abs((model_nu() - 1) * kk + ll)
    n1 = np.abs(kk) + np.abs(ll)
    order = np.argsort(-mass, axis=None)
    cum = np.cumsum(mass.ravel()[order]) / tot
    out = {}
    for q in (0.9, 0.99, 0.999):
        idx = order[: int(np.searchsorted(cum, q)) + 1]
        out["q%g" % q] = dict(modes=int(len(idx)), n1_min=int(n1.ravel()[idx].min()), n1_max=int(n1.ravel()[idx].max()),
                              k_max=int(np.abs(kk.ravel()[idx]).max()), l_max=int(np.abs(ll.ravel()[idx]).max()),
                              lam_min=float(lam.ravel()[idx].min()),
                              dio_ratio_min=float((42 * lam * n1).ravel()[idx].min()),
                              lam_min_mode=[int(kk.ravel()[idx][np.argmin(lam.ravel()[idx])]),
                                            int(ll.ravel()[idx][np.argmin(lam.ravel()[idx])])])
    hist_n1 = {}
    for lo in range(0, 340, 20):
        sel = (n1 >= lo) & (n1 < lo + 20)
        hist_n1["%d-%d" % (lo, lo + 19)] = float(mass[sel].sum() / tot)
    hist_lam = {}
    edges = [0, 0.01, 0.1, 0.3, 1, 3, 10, 30, 100]
    for a, b in zip(edges[:-1], edges[1:]):
        sel = (lam >= a) & (lam < b)
        hist_lam["%g-%g" % (a, b)] = float(mass[sel].sum() / tot)
    # mass-weighted mean of 1/(2 pi c |lambda|) (the effective divisor of R on E^'s modes)
    nz = mass > 0
    eff = float((mass[nz] / (TWO_PI * C_TIME * np.maximum(lam[nz], 1e-300))).sum() / tot)
    top = np.unravel_index(order[:8], mass.shape)
    out.update(hist_n1=hist_n1, hist_lambda=hist_lam, mean_inv_divisor=eff,
               top_modes=[[int(kk[i, j]), int(ll[i, j]), float(lam[i, j]), float(mass[i, j] / tot)]
                          for i, j in zip(*top)])
    return out


# =================================================================================================== 6. report
ROWS = [("E", "|E^| on T_rho (normalisation)", "rho"),
        ("DE", "|DE^|  (Cauchy n/delta0)", "rho-delta0"),
        ("T", "|T| (torsion; O(1), bound H_T)", "rho-delta0"),
        ("Ered", "|E_red|/e", "rho-delta0"),
        ("OmK", "|Omega_K|/e", "rho-2delta0"),
        ("Esym", "|E_sym|/e = max(|Omega_K|, |B Omega_K B|)", "rho-2delta0"),
        ("etaL", "|eta^L|/e", "rho"),
        ("etaN", "|eta^N|/e", "rho"),
        ("uN", "|u^N|/e = |R eta^N|/e", "rho-delta0"),
        ("xi0", "|xi_0|/e", "const"),
        ("xiw", "|xi^w|/e", "const"),
        ("xiN", "|xi^N|/e", "rho-delta0"),
        ("gL", "|g^L|/e", "rho-delta0"),
        ("xiL", "|xi^L|/e", "rho-2delta0"),
        ("xi", "|xi|/e", "rho-2delta0"),
        ("dK", "|DeltaK_0|/e", "rho-2delta0"),
        ("dxi", "|d_omega xi|/e", "rho-2delta0"),
        ("Dw", "|Delta omega|/e = |omega||xi^w|/e", "const"),
        ("dwdK", "|d_omega DeltaK|/e", "rho-2delta0"),
        ("Elin", "|E_lin|/e^2", "rho-2delta0"),
        ("Ebar", "|Ebar|/e^2 (leading order)", "rho-2delta0")]


def table(r, bounds):
    rows = []
    for key, label, strip in ROWS:
        if strip == "const":
            act = {"xi0": r["xi0_abs"], "xiw": abs(r["xiw"]), "Dw": abs(r["xiw"]) * C_TIME}[key]
        else:
            act = r["sups"][strip][key]
        der = bounds.get(key, (None, "", ""))[0]
        rows.append(dict(key=key, label=label, strip=strip, actual=act, derived=der,
                         ratio=(act / der if der else None)))
    return rows


def main():
    args = sys.argv[1:]
    out = None; N1, N2 = 1024, 256; check = False
    while args:
        a = args.pop(0)
        if a == "--json":
            out = args.pop(0)
        elif a == "--grid":
            N1, N2 = int(args.pop(0)), int(args.pop(0))
        elif a == "--check":
            check = True
        else:
            raise SystemExit(__doc__)
    t0 = time.time()
    print("package R1: rho = 1/70, rho_inf = rho/1000, c = 7/4, delta0 = %.6g, strips rho, rho-delta0, rho-2delta0"
          % DELTA0)
    res = residual_coefficients()
    dg = res["diag"]
    print("residual (time scale 1, weighted l1 on T_rho):  R3 poly %.4e (certificate R3_l1w 1.5922e-79), witness %.3e,"
          " total %.4e;  R4 poly %.4e (cert 4.5548e-80), witness %.3e, total %.4e;  eta1 %.3e"
          % (dg["R3_poly_l1w"], dg["R3_witness_l1w"], dg["R3_total_l1w"], dg["R4_poly_l1w"], dg["R4_witness_l1w"],
             dg["R4_total_l1w"], dg["eta1_l1w"]))
    print("  cross-check row P1 (exact+witness vs linearisation): weighted l1 difference %.3e (relative %.2e)"
          % (dg["crosscheck_rowP1_l1w_diff"], dg["crosscheck_rowP1_l1w_diff"] / dg["R3_total_l1w"]))
    print("  energy error <H o K> - E0 (time scale 1): %.3e" % dg["energy_unscaled"])
    consts, bounds = derived_constants()
    sup = support(res)
    r = run(N1, N2, res)
    runs = [r]
    if check:
        runs.append(run(2 * N1, 2 * N2, res))
    tab = table(r, bounds)
    print("e_act (c = 7/4) = %.4e   [components %s];  c * eta_cert(l1w) = %.4e;  eta^w = %.2e"
          % (r["e_act"], ", ".join("%.3e" % x for x in r["e_act_components"]),
             C_TIME * 1.0603322684245456e-78, r["eta_w"]))
    print("row P2 = -(p-1) E3 - d_omega(J~ - J_exact): on T_rho sup|E4 + (p-1) E3| = %.4f e_act (J truncation),"
          " sup|(p-1) E3| = %.4f e_act" % (r["Jtrunc_part_row4"], r["pm1_E3_part_row4"]))
    print("xi0 = %s, xi^w = %.4e;  <T> = %s;  <Y> = %s" % (np.round(r["xi0"], 4).tolist(), r["xiw"],
                                                             np.round(r["avgT"], 6).tolist(), np.round(r["avgY"], 6).tolist()))
    print("checks: %s;  constants shift-invariance %.2e" % ({k: "%.1e" % v for k, v in r["checks"].items()},
                                                           r["shift_invariance_of_constants"]))
    print()
    print("| quantity | strip | actual | derived | actual/derived | derived formula |")
    print("|---|---|---:|---:|---:|---|")
    for row in tab:
        b = bounds.get(row["key"], (None, "-", ""))
        print("| %s | %s | %.4g | %s | %s | %s |" % (row["label"], row["strip"], row["actual"],
              "%.4g" % row["derived"] if row["derived"] else "-",
              "%.3g" % row["ratio"] if row["ratio"] else "-", b[1]))
    s2 = r["sups"]["rho-2delta0"]
    bnd = s2["P"] * 2 * s2["Elin"] + M2_R1 / 2 * s2["dK"] ** 2 + abs(r["xiw"]) * s2["dwdK"]
    print()
    print("new error, bound-structured: |P| 2 |E_lin| + (M2/2)|DK|^2 + |xi^w||d_w DK| = %.4g * %.4g * 2 + %.4g/2 * %.4g^2"
          " + %.3g * %.4g = %.4g  (per e^2);  leading-order sup|Ebar| = %.4g;  derived C_E/(gamma^4 delta0^4) = %.4g"
          % (s2["P"], s2["Elin"], M2_R1, s2["dK"], abs(r["xiw"]), s2["dwdK"], bnd, s2["Ebar"], bounds["Ebar"][0]))
    print("  parts of the leading-order Ebar: sup|P E_lin| %.4g, sup|D2X| %.4g, sup|xi^w d_w DK| %.4g"
          % (s2["PElin"], s2["D2X"], s2["xiw_dwdK"]))
    print()
    print("support of E^ (weighted by exp(2 pi rho |k|_1)):", json.dumps({k: v for k, v in sup.items()
                                                                        if k.startswith("q")}))
    print("  mass by |kappa|_1:", {k: round(v, 4) for k, v in sup["hist_n1"].items() if v > 1e-4})
    print("  mass by |lambda| = |(nu-1)k + l|:", {k: round(v, 4) for k, v in sup["hist_lambda"].items()})
    print("  mass-weighted mean 1/(2 pi c |lambda|) = %.4g  vs  Gamma_delta0 = c_R/(gamma delta0) = %.4g"
          % (sup["mean_inv_divisor"], consts["cR"] / (consts["gamma"] * consts["delta0"])))
    print("  top modes [k, l, |lambda|, mass share]:", sup["top_modes"])
    s0, s1 = r["sups"]["rho"], r["sups"]["rho-delta0"]
    print("  gain of R: sup_{rho-delta0}|u^N| / sup_rho|eta^N| = %.3e,  sup_{rho-2delta0}|xi^L| / sup_{rho-delta0}|g^L| = %.3e"
          "  vs  Gamma_delta0 = %.4g" % (s1["uN"] / s0["etaN"], s2["xiL"] / s1["gL"],
                                         consts["cR"] / (consts["gamma"] * consts["delta0"])))
    for strip, key in (("rho", "Ev"), ("rho-2delta0", "dK"), ("rho-2delta0", "Ebar")):
        print("  spectrum of %s on T_%s (weighted mass by |kappa|_1):" % (key, strip),
              {k: round(v, 4) for k, v in r["spectra"][strip][key].items() if v > 1e-4})
    if check:
        r2 = runs[1]
        print()
        print("resolution check %dx%d -> %dx%d (max relative change over all sups): " % (N1, N2, 2 * N1, 2 * N2), end="")
        worst = 0.0; wk = None
        for strip in r["sups"]:
            for k_, v_ in r["sups"][strip].items():
                if k_ == "xiw_dwdK":                                     # xi^w is at noise level (~1e-25)
                    continue
                v2 = r2["sups"][strip][k_]
                rel = abs(v2 - v_) / max(abs(v_), 1e-300)
                if rel > worst:
                    worst, wk = rel, (strip, k_)
        rel = abs(r2["e_act"] - r["e_act"]) / r["e_act"]
        if rel > worst:
            worst, wk = rel, ("rho", "e_act")
        print("%.2e (at %s);  xi0, xi^w (noise level): %.1e, %.1e -> %.1e, %.1e"
              % (worst, wk, r["xi0_abs"], abs(r["xiw"]), r2["xi0_abs"], abs(r2["xiw"])))
    print("total %.1fs" % (time.time() - t0))
    if out:
        json.dump(dict(params=dict(rho=RHO, rhoinf=RHOINF, c=C_TIME, s=S_RAY, delta0=DELTA0, M2=M2_R1),
                       residual=dg, support=sup, derived_constants=consts,
                       derived_bounds={k: dict(value=v[0], formula=v[1], strip=v[2]) for k, v in bounds.items()},
                       runs=runs, table=tab), open(out, "w"), indent=1)


if __name__ == "__main__":
    main()
