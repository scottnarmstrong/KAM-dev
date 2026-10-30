#!/usr/bin/env python3
"""LOCK-GEN part 2 (D45): v2 design numbers of the N = 65 librational certificate in elliptic polar coordinates.
Untrusted design tooling (double precision; every pass/fail decision of the threshold is exact, in v2_q.py).

    OMP_NUM_THREADS=4 python3 lock_v2.py claims [rho] [kappa]      # sampled Ham claims and frame majorants
    OMP_NUM_THREADS=4 python3 lock_v2.py scan OUT.json             # thresholds over (rho, kappa)

The lock Hamiltonian (design §3; `lockHamExpr` proposal of lock_emit.py), z = ((alpha, phi), (I, Jt)):
    X = sqrt(I/(pi Om)) sin 2 pi alpha,  Y = sqrt(I Om/pi) cos 2 pi alpha,  c = sum cs_j sin 2 pi (j+1) phi,
    K = Jt + Y^2/2 - c'^2/2 + X c'' + V(phi + c + X, phi) - 1/2,  V(q, phi) = -sum_m eps A_m cos 2 pi (2q - m phi),
time-scaled to kappa K.  The torus K(theta) = (theta1 + U, theta2, P, Jt) of LOCK-GEN part 1 (lock_hp.py stage A
solution, Galerkin half diamond K = 160, L = 40), Jt from energy conservation (K o K = E0 = 0), frequency
omega' = (omega, 1), omega = 1/(65 + g); the invariance frequency is s omega* = kappa omega'.

* `ham_claims`: the four refined Ham claims of `RefClaim` (dh = sum_a |d_a H|, dx = max_a sum_b |d_ab H|,
  d2x = max_a sum_bc |d_abc H|, d2h = sum_ab |d_ab H|: the hamClaimOk forms), SAMPLED on the distinguished boundary
  of the certificate domain (angles Im = +-rhoH, action I on the circle |I - c1| = r1); a lower bound of what the
  kernel's disc pass certifies (see lock_balls.py for the disc pass itself).
* `frame`: bL, bN, bNt, bT (FrameFacts sums, v2_frame.py formulas) sampled at the four corners Im theta = (+-rho,
  +-rho), and the checkEmbedding / checkGram / checkTorsion sizes sigma_K - mu >= max row sum |DK|,
  sigma_B - mu >= |G^-1|, sigma_T - mu >= |avg T^-1|.
"""
import sys, os, json, math, time, pickle
from fractions import Fraction as F
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from model import A_EXACT, EPS                      # noqa: E402
import lock_ham as LH                               # noqa: E402

TWO_PI = 2 * math.pi
DATA = os.environ.get("SO_LOCK_DIR", "/mnt/HC_Volume_106379410/kam-data/so-lock")
OMEGA_R = F(8, 65)
CENTRE = [F(-3, 250000), F(-699, 2000000000), F(-883, 50000000000)]
EPSA = {m: float(EPS * A_EXACT[m]) for m in A_EXACT}
G_OLD = (math.sqrt(5) - 1) / 2


def omega_lib(N=65):
    return 1 / (N + G_OLD)


# ------------------------------------------------------------------------------------------- order-3 jets
class Jet:
    """f, its gradient g[a], Hessian h[a, b] and third derivative t[a, b, c] in m variables, over sample arrays
    (t is None for order-2 jets, `Jet.ORDER = 2`)."""
    ORDER = 3

    def __init__(self, v, g, h, t):
        self.v, self.g, self.h, self.t = v, g, h, t

    @staticmethod
    def const(x, m, shape):
        z = np.zeros(shape, complex)
        return Jet(z + x, np.zeros((m,) + shape, complex), np.zeros((m, m) + shape, complex),
                   np.zeros((m, m, m) + shape, complex) if Jet.ORDER == 3 else None)

    @staticmethod
    def var(x, i, m):
        J = Jet.const(0, m, x.shape)
        J.v = x.astype(complex)
        J.g[i] = 1
        return J

    def __add__(self, o):
        if not isinstance(o, Jet):
            return Jet(self.v + o, self.g, self.h, self.t)
        return Jet(self.v + o.v, self.g + o.g, self.h + o.h, None if self.t is None else self.t + o.t)

    __radd__ = __add__

    def __neg__(self):
        return Jet(-self.v, -self.g, -self.h, None if self.t is None else -self.t)

    def __sub__(self, o):
        return self + (-o)

    def __rsub__(self, o):
        return (-self) + o

    def __mul__(self, o):
        if not isinstance(o, Jet):
            return Jet(self.v * o, self.g * o, self.h * o, None if self.t is None else self.t * o)
        a, b = self, o
        g = a.g * b.v + a.v * b.g
        h = a.h * b.v + a.v * b.h + np.einsum("i...,j...->ij...", a.g, b.g) + np.einsum("j...,i...->ij...", a.g, b.g)
        if a.t is None:
            return Jet(a.v * b.v, g, h, None)
        t = a.t * b.v + a.v * b.t
        for (x, y) in ((a, b), (b, a)):
            t = t + np.einsum("ij...,k...->ijk...", x.h, y.g) + np.einsum("ik...,j...->ijk...", x.h, y.g) \
                + np.einsum("jk...,i...->ijk...", x.h, y.g)
        return Jet(a.v * b.v, g, h, t)

    __rmul__ = __mul__

    def compose(self, f0, f1, f2, f3):
        """f(self) from the values f, f', f'', f''' at self.v."""
        u = self
        g = f1 * u.g
        h = f2 * np.einsum("i...,j...->ij...", u.g, u.g) + f1 * u.h
        if u.t is None:
            return Jet(f0, g, h, None)
        t = (f3 * np.einsum("i...,j...,k...->ijk...", u.g, u.g, u.g)
             + f2 * (np.einsum("ij...,k...->ijk...", u.h, u.g) + np.einsum("ik...,j...->ijk...", u.h, u.g)
                     + np.einsum("jk...,i...->ijk...", u.h, u.g)) + f1 * u.t)
        return Jet(f0, g, h, t)

    def sin(self):
        s, c = np.sin(self.v), np.cos(self.v)
        return self.compose(s, c, -s, -c)

    def cos(self):
        s, c = np.sin(self.v), np.cos(self.v)
        return self.compose(c, -s, -c, s)

    def sqrt(self):
        r = np.sqrt(self.v)
        return self.compose(r, 0.5 / r, -0.25 / r ** 3, 0.375 / r ** 5)


def lock_ham_jet(z, Om=float(OMEGA_R), cs=None, kappa=1.0):
    """kappa K at the complex points z = (alpha, phi, I, Jt) (arrays), as a Jet in the 4 variables."""
    cs = [float(c) for c in (cs or CENTRE)]
    al, ph, I, Jt = [Jet.var(z[i], i, 4) for i in range(4)]
    s1, c1 = (al * TWO_PI).sin(), (al * TWO_PI).cos()
    X = (I * (1 / (math.pi * Om))).sqrt() * s1
    Y = (I * (Om / math.pi)).sqrt() * c1
    c = sum(((ph * (TWO_PI * (j + 1))).sin() * cj for j, cj in enumerate(cs)), Jet.const(0, 4, z[0].shape))
    cp = sum(((ph * (TWO_PI * (j + 1))).cos() * (cj * TWO_PI * (j + 1)) for j, cj in enumerate(cs)),
             Jet.const(0, 4, z[0].shape))
    cpp = sum(((ph * (TWO_PI * (j + 1))).sin() * (-cj * (TWO_PI * (j + 1)) ** 2) for j, cj in enumerate(cs)),
              Jet.const(0, 4, z[0].shape))
    A = (c + X) * (2 * TWO_PI)
    cA, sA = A.cos(), A.sin()
    V = Jet.const(0, 4, z[0].shape)
    for m, e in EPSA.items():
        V = V - (cA * (ph * (TWO_PI * (2 - m))).cos() - sA * (ph * (TWO_PI * (2 - m))).sin()) * e
    K = Jt + Y * Y * 0.5 - cp * cp * 0.5 + X * cpp + V - 0.5
    return K * kappa


def claim_sums(J):
    """The hamClaimOk forms of a Jet (max over samples): dh, dx, d2x, d2h."""
    A1, A2, A3 = np.abs(J.g), np.abs(J.h), np.abs(J.t)
    return dict(dh=float(A1.sum(0).max()), dx=float(A2.sum(1).max()), d2x=float(A3.sum((1, 2)).max()),
                d2h=float(A2.sum((0, 1)).max()))


# ------------------------------------------------------------------------------------------- the torus
def load_torus(nx=512, nt=128, K=160, L=40, N=65):
    """V on the grid from the stage-A double solution; returns the Fourier data of U, P, Jt on the grid."""
    b = np.load(os.path.join(DATA, "A_N%d_K%d_L%d.npy" % (N, K, L)))
    idx = [(k, l) for k in range(0, K + 1) for l in range(-L, L + 1) if (k > 0 or l > 0) and abs(k) / K + abs(l) / L <= 1]
    assert len(idx) == len(b)
    vh = np.zeros((nx, nt), complex)
    for (k, l), x in zip(idx, b):
        vh[k % nx, l % nt] += x / 2j
        vh[-k % nx, -l % nt] -= x / 2j
    return torus_from_vhat(vh, N)


def centre_fns(t2, cs=None):
    cs = [float(c) for c in (cs or CENTRE)]
    cc = sum(c * np.sin(TWO_PI * (j + 1) * t2) for j, c in enumerate(cs))
    dc = sum(c * TWO_PI * (j + 1) * np.cos(TWO_PI * (j + 1) * t2) for j, c in enumerate(cs))
    return cc, dc


def torus_from_vhat(vh, N=65, Om=float(OMEGA_R)):
    nx, nt = vh.shape
    om = omega_lib(N)
    k = np.fft.fftfreq(nx, 1.0 / nx)[:, None]
    l = np.fft.fftfreq(nt, 1.0 / nt)[None, :]
    V = np.real(np.fft.ifft2(vh)) * nx * nt
    pm1 = np.real(np.fft.ifft2(1j * (om * k + l) * vh)) * nx * nt
    t1 = (np.arange(nx) / nx)[:, None] * np.ones((1, nt))
    t2 = (np.arange(nt) / nt)[None, :] * np.ones((nx, 1))
    cc, dc = centre_fns(t2)
    X = V / TWO_PI - cc
    Y = pm1 - dc
    I = math.pi * (Om * X ** 2 + Y ** 2 / Om)
    al = np.arctan2(math.sqrt(Om) * X, Y / math.sqrt(Om)) / TWO_PI
    U = al - t1
    U = U - np.rint(U)
    z = (t1 + U, t2, I, np.zeros_like(I))
    Jt = -np.real(LH.eval_tree(LH.lock_ham_expr(F(Om).limit_denominator(1000), CENTRE), z))   # K + Jt = E0 = 0
    fh = lambda f: np.fft.fft2(f) / (nx * nt)
    return dict(nx=nx, nt=nt, omega=om, Om=Om, Uh=fh(U), Ph=fh(I), Jh=fh(Jt), I_range=(float(I.min()), float(I.max())),
                k=k * np.ones((1, nt)), l=l * np.ones((nx, 1)))


def mask_of(T):
    nx, nt = T["nx"], T["nt"]
    m = np.ones((nx, nt))
    m[nx // 2, :] = 0
    m[:, nt // 2] = 0
    return m


def eval_shift(T, fh, y1, y2, deriv=None):
    """f(theta + i (y1, y2)) on the grid from its Fourier data (optionally d/dtheta_j, theta in turns)."""
    nx, nt = T["nx"], T["nt"]
    k, l = T["k"], T["l"]
    g = fh * mask_of(T) * np.exp(-TWO_PI * (k * y1 + l * y2))
    if deriv == 0:
        g = g * 1j * TWO_PI * k
    elif deriv == 1:
        g = g * 1j * TWO_PI * l
    elif deriv == "om":
        g = g * 1j * TWO_PI * (T["omega"] * k + l)
    return np.fft.ifft2(g) * nx * nt


def torus_points(T, y1, y2):
    nx, nt = T["nx"], T["nt"]
    t1 = (np.arange(nx) / nx)[:, None] * np.ones((1, nt)) + 1j * y1
    t2 = (np.arange(nt) / nt)[None, :] * np.ones((nx, 1)) + 1j * y2
    return (t1 + eval_shift(T, T["Uh"], y1, y2), t2, eval_shift(T, T["Ph"], y1, y2), eval_shift(T, T["Jh"], y1, y2))


def frame(T, rho, kappa, Om=float(OMEGA_R)):
    """FrameFacts sums (bL, bN, bNt, bT) at the corners, sigma sizes, and the torsion average (real grid)."""
    sup = dict(bL=0.0, bN=0.0, bNt=0.0, bT=0.0, DK=0.0, Ginv=0.0, Im_U=0.0, P_dev=0.0, J_dev=0.0)
    Ominv = np.zeros((4, 4))
    Ominv[0, 2] = Ominv[1, 3] = -1
    Ominv[2, 0] = Ominv[3, 1] = 1
    P0 = float(np.real(T["Ph"][0, 0]))
    J0 = float(np.real(T["Jh"][0, 0]))
    out = {}
    for y1, y2 in [(0.0, 0.0), (rho, rho), (rho, -rho), (-rho, rho), (-rho, -rho)]:
        z = torus_points(T, y1, y2)
        L = np.zeros(z[0].shape + (4, 2), complex)
        L[..., 0, 0] = 1 + eval_shift(T, T["Uh"], y1, y2, 0)
        L[..., 0, 1] = eval_shift(T, T["Uh"], y1, y2, 1)
        L[..., 1, 1] = 1
        for r, key in ((2, "Ph"), (3, "Jh")):
            L[..., r, 0] = eval_shift(T, T[key], y1, y2, 0)
            L[..., r, 1] = eval_shift(T, T[key], y1, y2, 1)
        G = np.einsum("...ri,...rj->...ij", L, L)
        B = np.linalg.inv(G)
        Nm = np.einsum("ab,...bk,...kj->...aj", Ominv, L, B)
        Jet.ORDER = 2
        Hj = lock_ham_jet(z, Om, kappa=kappa)
        Jet.ORDER = 3
        # X_h = (H_I, -H_theta): DX_h rows (dH_I/dz, -dH_theta/dz); variables (alpha, phi, I, Jt)
        h = np.moveaxis(Hj.h, (0, 1), (-2, -1))
        A = np.concatenate([h[..., 2:, :], -h[..., :2, :]], axis=-2)
        nx, nt = T["nx"], T["nt"]
        DN = np.zeros_like(Nm)
        for a in range(4):
            for j in range(2):
                fh = np.fft.fft2(Nm[..., a, j]) / (nx * nt)
                DN[..., a, j] = kappa * eval_shift(T, fh * np.exp(TWO_PI * (T["k"] * y1 + T["l"] * y2)), y1, y2, "om")
        XN = np.einsum("...ab,...bj->...aj", A, Nm) - DN
        Tm = np.einsum("...ai,ab,...bj->...ij", Nm, Ominv, XN)
        if y1 == 0.0:
            out["Tavg"] = Tm.mean(axis=(0, 1)).real.tolist()
            out["Tavg_inv_rowsum"] = float(np.abs(np.linalg.inv(Tm.mean(axis=(0, 1)).real)).sum(-1).max())
            out["DK_real"] = float(np.abs(L).sum(-1).max())
            out["Ginv_real"] = float(np.abs(B).sum(-1).max())
            continue
        sup["bL"] = max(sup["bL"], float(np.abs(L).sum(-2).max()))
        sup["bN"] = max(sup["bN"], float(np.abs(Nm).sum(-1).max()))
        sup["bNt"] = max(sup["bNt"], float(np.abs(Nm).sum(-2).max()))
        sup["bT"] = max(sup["bT"], float(np.abs(Tm).sum(-1).max()))
        sup["DK"] = max(sup["DK"], float(np.abs(L).sum(-1).max()))
        sup["Ginv"] = max(sup["Ginv"], float(np.abs(B).sum(-1).max()))
        sup["Im_U"] = max(sup["Im_U"], float(np.abs(np.imag(z[0])).max()) - rho)
        sup["P_dev"] = max(sup["P_dev"], float(np.abs(z[2] - P0).max()))
        sup["J_dev"] = max(sup["J_dev"], float(np.abs(z[3] - J0).max()))
    out.update(sup)
    out["P0"], out["J0"] = P0, J0
    return out


def domain_of(T, rho, room=F(1, 160)):
    """A certificate domain containing K(strip rho) with room: rhoH, action centres and radii (rationals)."""
    fr = frame(T, rho, 1.0)
    rhoH = F(rho) + F(fr["Im_U"]).limit_denominator(10 ** 6) + room
    c1 = F(fr["P0"]).limit_denominator(10 ** 6)
    r1 = F(fr["P_dev"]).limit_denominator(10 ** 6) + room / 4
    c2 = F(fr["J0"]).limit_denominator(10 ** 6)
    r2 = F(fr["J_dev"]).limit_denominator(10 ** 6) + room / 4
    return dict(rhoH=rhoH, c1=c1, r1=r1, c2=c2, r2=r2)


def ham_claims(dom, kappa, nx=128, nt=32, nI=12, Om=float(OMEGA_R)):
    """Sampled sup of the claim sums over the distinguished boundary of the domain."""
    best = dict(dh=0.0, dx=0.0, d2x=0.0, d2h=0.0)
    rH = float(dom["rhoH"])
    for y1 in (rH, -rH):
        for y2 in (rH, -rH):
            a = (np.arange(nx) / nx)[:, None, None] + 1j * y1
            p = (np.arange(nt) / nt)[None, :, None] + 1j * y2
            I = float(dom["c1"]) + float(dom["r1"]) * np.exp(1j * TWO_PI * np.arange(nI) / nI)[None, None, :]
            sh = np.broadcast_shapes(a.shape, p.shape, I.shape)
            z = tuple(np.broadcast_to(x, sh).copy() for x in (a, p, I, np.zeros(sh) + float(dom["c2"])))
            cs = claim_sums(lock_ham_jet(z, Om, kappa=kappa))
            best = {k: max(best[k], cs[k]) for k in best}
    return best


def ball_claims(dom, kappa=1, form="design"):
    """The disc-pass claims (lock_balls mirror) of kappa K on the domain; None if the pass fails closed."""
    import math as _m
    import lock_jet as LJ
    import lock_balls as LB
    J = LJ.jet(2, LH.lock_ham_scaled(F(kappa), OMEGA_R, CENTRE, form))
    wH = _m.exp(2 * _m.pi * float(dom["rhoH"])) * (1 + 1e-9)
    bs, fail = LB.balls(J["prog"], 2, wH, [dom["c1"], dom["c2"]], [dom["r1"], dom["r2"]])
    if bs is None:
        return None
    return {k: v for k, v in LB.bound_sums(J, bs).items() if not isinstance(v, list)}


def scan(out, rhos=("1/280", "1/140", "1/100", "1/70", "1/50"), mus=("1/4000", "1/2000", "1/1000", "1/500"),
         kappas=("1/2", "1", "2", "4"), form="design"):
    """Refined thresholds over (rho, mu, kappa): frame at kappa = 1 (bT scales with kappa, the torsion inverse
    with 1/kappa), disc-pass claims on the domain rhoH = rho + Im U + mu, radii = deviation + mu."""
    T = load_torus()
    res = []
    for r in rhos:
        rho = F(r)
        fr = frame(T, float(rho), 1.0)
        print("rho", r, json.dumps({k: v for k, v in fr.items() if k != "Tavg"}), flush=True)
        for m in mus:
            mu = F(m)
            dom = dict(rhoH=rho + F(fr["Im_U"]).limit_denominator(10 ** 7) + mu + F(1, 10 ** 6),
                       c1=F(fr["P0"]).limit_denominator(10 ** 7), r1=F(fr["P_dev"]).limit_denominator(10 ** 7) + mu + F(1, 10 ** 6),
                       c2=F(fr["J0"]).limit_denominator(10 ** 7), r2=F(fr["J_dev"]).limit_denominator(10 ** 7) + mu + F(1, 10 ** 6))
            bc = ball_claims({k: float(v) for k, v in dom.items()}, 1, form)
            if bc is None:
                print("  mu", m, "disc pass fails", flush=True)
                continue
            for kp in kappas:
                k = F(kp)
                up = lambda x: F(_up(x * 1.01))
                R = dict(dh=up(bc["dh"] * k), dx=up(bc["dx"] * k), d2x=up(bc["d2x"] * k), d2h=up(bc["d2h"] * k),
                         bL=up(fr["bL"]), bN=up(fr["bN"]), bNt=up(fr["bNt"]), bT=up(fr["bT"] * k))
                p = lock_package(rho, k, up(fr["DK"]) + mu, up(fr["Ginv"]) + mu, up(1.0101 / float(k)) + mu,
                                 up(bc["M"] * k), mu=mu)
                th = threshold(p, R)
                row = dict(rho=r, mu=m, kappa=kp, claims={a: float(b) for a, b in R.items()}, M=float(p["M"]),
                           sK=float(p["sK"]), sB=float(p["sB"]), sT=float(p["sT"]), rhoH=float(dom["rhoH"]),
                           r1=float(dom["r1"]), **th, log10_thr_over_kappa=th["log10_thr"] - math.log10(float(k)))
                res.append(row)
                print("  mu %s kappa %s: thr 10^%.2f (thr/kappa 10^%.2f) disp coef 10^%.2f binding %s d2x %.3g" % (
                    m, kp, th["log10_thr"], row["log10_thr_over_kappa"], th["log10_disp_coef"], th["binding"],
                    float(R["d2x"])), flush=True)
                json.dump(res, open(out, "w"), indent=1)
    return res


def _up(x, sig=4):
    e = math.floor(math.log10(x)) - sig + 1
    return math.ceil(x / 10.0 ** e * (1 + 1e-12)) * F(10) ** e


# ------------------------------------------------------------------------------------------- thresholds
def lock_package(rho, kappa, sK, sB, sT, M, mu=F(1, 160), rhoInf=None, N=65):
    """CertParams of a lock package in v2_r2.package's shape.  The lock frequency (omega, 1), omega = 1/(N + g),
    is the upper rotational frequency (nu_+ - 1, 1) of the N-th barrier, so `box_of(p, 'upper')`, the site constants
    and the landed Diophantine fact (gamma = kappa/(N + 2)) are those of the upper torus.  s = 1 + 1e-6, sigma_omega
    = 2, nu = 1e-6 as in R2; c = kappa s (the time scale; v2_r2 takes kappa = c/s)."""
    import v2_r2 as D
    s = 1 + F(1, 10 ** 6)
    return D.package(N, rho=F(rho), M=F(M), sK=F(sK), sB=F(sB), sT=F(sT), c=F(kappa) * s, rhoInf=rhoInf, mu=mu)


def threshold(p, R, kp=3, th=F(1, 8), J=20, classical=frozenset({("d", 2)})):
    """log10 of the refined threshold e* and the displacement coefficient (configuration d01b by default)."""
    import v2_r2 as D
    import v2_q as V
    import v2_sketch as S
    box = D.box_of(p, "upper")
    st = S.sites_for(p, "upper", kp, set(classical))
    Xs = D.max_Xs("refined", p, box, kp, th, J, R, st, lo=-60, hi=10, steps=40)
    ok, why, w = D.okB_at("refined", p, box, kp, th, J, Xs, R, st, detail=True)
    _, why_up, _ = D.okB_at("refined", p, box, kp, th, J, Xs * F(11, 10), R, st, detail=True)
    d0 = min(F(1), (p["rho"] - p["rhoInf"]) / 6)
    e = Xs * p["gamma"] ** 4 * d0 ** 4
    Q = V.refined_num(w, 2, p, box)
    C = V.disp_coefs(Q, 2, p, Xs, False)[0]
    return dict(log10_thr=D.lg(e), Xs=str(Xs), log10_disp_coef=D.lg(C / (p["gamma"] ** 2 * p["rho"] ** 2)),
                binding=why_up, ok=ok)


if __name__ == "__main__" and sys.argv[1] == "scan":
    scan(sys.argv[2])
    sys.exit(0)

if __name__ == "__main__" and sys.argv[1] == "claims":
    t0 = time.time()
    T = load_torus()
    print("I range", T["I_range"], "load %.1fs" % (time.time() - t0), flush=True)
    rho = float(F(sys.argv[2])) if len(sys.argv) > 2 else 1 / 140
    kappa = float(F(sys.argv[3])) if len(sys.argv) > 3 else 1.0
    dom = domain_of(T, rho)
    print("domain", {k: float(v) for k, v in dom.items()}, flush=True)
    fr = frame(T, rho, kappa)
    print("frame", json.dumps({k: v for k, v in fr.items()}), flush=True)
    print("ham claims (sampled)", ham_claims(dom, kappa), "%.1fs" % (time.time() - t0), flush=True)


def final_check(row, err):
    """The exact refinedCore test (v2_q mirror) of a scan row at the error err, with disp at its minimum
    (rounded up) and X* = 2 err/(gamma^4 delta0^4) rounded up (2x room, as in v2_pkg65.py)."""
    import v2_r2 as D
    import v2_q as V
    import v2_sketch as S
    k, mu, rho = F(row["kappa"]), F(row["mu"]), F(row["rho"])
    R = {a: F(str(b)) for a, b in row["claims"].items()}
    p = lock_package(rho, k, F(str(row["sK"])), F(str(row["sB"])), F(str(row["sT"])), F(str(row["M"])), mu=mu)
    box = D.box_of(p, "upper")
    st = S.sites_for(p, "upper", 3, {("d", 2)})
    d0 = min(F(1), (p["rho"] - p["rhoInf"]) / 6)
    Xs = V.up(float(2 * err / (p["gamma"] ** 4 * d0 ** 4)), 3)
    ok, why, w = D.okB_at("refined", p, box, 3, F(1, 8), 20, Xs, R, st, detail=True)
    Q = V.refined_num(w, 2, p, box)
    C = V.disp_coefs(Q, 2, p, Xs, False)[0]
    disp = V.up(float(C * err / (p["gamma"] ** 2 * p["rho"] ** 2)) * 1.001, 3)
    fin = V.refinedCore(2, dict(p, err=err, disp=disp), box, dict(w), detail=True)
    return dict(err=str(err), Xs=str(Xs), disp=str(disp), disp_float=float(disp), okB=ok, refinedCore=fin,
                sites={"%s%d" % kk: float(v) for kk, v in st.items()})
