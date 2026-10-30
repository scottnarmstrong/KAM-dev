#!/usr/bin/env python3
"""The certified first step (hybrid) on R1: design numbers in the norms of the enclosures (package SHARP2-HYBRID).

Untrusted design tooling, double precision.  Design document docs/campaign/design/APOST-SHARP-V2-HYBRID.md (section 4),
blueprint blueprint/parts/p2s2-hybrid-cert.tex.  The hybrid theorem restarts the proved v2 theorem at the torus
K1 = K + DK of the first Newton step and transfers its conclusion back to K.  The certificate encloses:
  - the linearised new error  E_lin~ = E + DX_h(K) DK - D(DK) omega  on T_{rho1}   (weighted l^1 of its model),
  - the Taylor remainder (M2/2)|DK|^2                                                   (the certified M2 of h),
  - |DK|, |D(DK)|, |D(DK)^T| on T_{rho1}, on the real torus and on T_{rho_inf}            (weighted l^1, exact),
  - the transferred caps of K1 (Lemmas bp:p2s2hc:frames, bp:p2s2hc:torsion: explicit formulas below).
The new error is e1 = |E_lin~|_{l1,rho1} + (M2/2)|DK|_{l1,rho1}^2.  The restarted theorem (route A with L8', route B
with the levers) is evaluated by thresholds_v2.py at the strip rho1 with the transferred caps and the margin mu1.

Two measurements:
  --shape   R1's own residual shape (the L = 88 candidate, residual 4e-79; step0_actual.py), every step object
            normalised by e = sup_{T_rho}|E|.  Since E_lin~ is quadratic in the residual at leading order
            (E_lin~ = P E_lin, E_lin = E_red xi + Omega0 E_sym d_omega xi), the hybrid threshold of this SHAPE is the
            largest e with A(rho1) e^2 <= e1*(rho1), A = |P E_lin^|_{l1} + (M2/2)|DK^|_{l1}^2.  A property of the
            residual's shape (its spectrum), not of the theorem: re-measured per candidate.
  --trunc   truncated candidates: v cut at 10^-L (the graph torus of r1_norms.py, exactly energy-normalised), the
            residual E_L in closed form, the isoenergetic step DK (R1's <T> is singular), E_lin~ = E + A DK - d_omega DK and the actual new
            error E1 = X_h(K + DK) - D(K + DK) omega computed DIRECTLY (no leading-order approximation).  For each L: does
            the plain theorem certify K_L, does the hybrid?

Norms: max norm on vectors, maximum absolute row sum on matrices (the frozen convention); "l1" is the weighted l^1
norm sum_k |f_k| exp(2 pi r |k|_1) of the Fourier coefficients (a bound for the sup on T_r, what the kernel computes
from a model's polynomial part), read off from the shifted grids at the corners (r, r) and (r, -r) (quadrant
k <= 0 from the matching corner, the rest by realness).  "sup" is the sampled sup on the corners (lower bound).

Usage:  python3 -I scripts/apost_sharp/hybrid_cert_r1.py [--shape] [--trunc [--L 7,8,9]] [--sizes] [--quick]
        [--json OUT]
  (default: both; about 10-20 min with nice; --quick: fewer strips and candidates)
"""
import json, math, os, sys, time
import numpy as np
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import step0_actual as S0                      # noqa: E402  residual of R1, grids, the iso step
import r1_norms                                # noqa: E402  the graph torus and its frame
import thresholds_v2 as T2                     # noqa: E402  the restarted theorem (routes A', B)
import model                                   # noqa: E402  (scripts/spin_orbit, via S0's path)

TWO_PI = 2 * math.pi
C_TIME = S0.C_TIME
OM = r1_norms.OM
JX = r1_norms.JX
SLACK = 1.10       # the model remainders (truncation of DK and of the model of E) take at most 10% of E_lin~


# ============================================================================================ norms on shifted grids
def _masks(G):
    k, l = G.kk, G.ll
    return (k <= 0) & (l <= 0), (k <= 0) & (l > 0), (k == 0) & (l <= 0), (k == 0) & (l > 0)


def l1w(G, f_pp, f_pm):
    """Weighted l^1 norm per component (trailing axes kept) of a real-on-reals function from its values at the
    corners (r, r) and (r, -r): the shifted coefficients there are f_k exp(2 pi r |k|_1) on the quadrants
    {k <= 0, l <= 0} and {k <= 0, l > 0}; the half k > 0 by realness (|f_-k| = |f_k|)."""
    m1, m2, z1, z2 = _masks(G)
    c1 = np.abs(G.coef_at(f_pp)); c2 = np.abs(G.coef_at(f_pm))
    sel = lambda c, m: (c * m.reshape(m.shape + (1,) * (c.ndim - 2))).sum(axis=(0, 1))
    return 2 * (sel(c1, m1) + sel(c2, m2)) - (sel(c1, z1) + sel(c2, z2))


def l1w_real(G, f0):
    """Plain l^1 norm (r = 0) per component from the values on the real grid."""
    return np.abs(G.coef_at(f0)).sum(axis=(0, 1))


def vec_norm(a):
    return float(np.max(a))


def mat_norm(a):
    """row-sum norm of a matrix of entrywise norms (rows = axis -2)."""
    return float(np.max(np.sum(a, axis=-1)))


def sup_vec(*vs):
    return max(float(np.abs(v).max()) for v in vs)


def sup_mat(*ms):
    return max(float(np.abs(m).sum(-1).max()) for m in ms)


def deriv(G, f):
    """D f on the same shifted grid: (..., d) -> (..., d, 2), columns d/dpsi, d/dphi."""
    C = G.coef_at(f)
    tk = (2j * math.pi * G.kk).reshape(G.kk.shape + (1,) * (f.ndim - 2))
    tl = (2j * math.pi * G.ll).reshape(G.ll.shape + (1,) * (f.ndim - 2))
    ev = lambda X: np.fft.ifft2(X, axes=(0, 1)) * (G.N1 * G.N2)
    return np.stack([ev(C * tk), ev(C * tl)], axis=-1)


# ============================================================================================ 1. R1's residual shape
def shape_measure(strips, N1=1024, N2=256, log=print):
    """Normalised step objects of R1's own residual (iso step of step0_actual; xi^w ~ 1e-25, so it is the fixed step)
    on T_{rho1} for each rho1 in strips, on the real torus and on T_{rho_inf}."""
    t0 = time.time()
    res = S0.residual_coefficients(log=lambda *a: None)
    G = S0.Grid(N1, N2)
    Cs = S0.residual_grid(G, res)
    e_act = 0.0
    for y in ((S0.RHO, S0.RHO), (S0.RHO, -S0.RHO)):
        e_act = max(e_act, S0.vmax(np.stack([G.eval(C, y) for C in Cs], axis=-1)))
    eta_w = -C_TIME * res["diag"]["energy_unscaled"] / e_act
    _, consts, _, _, _, _ = S0.step_at(G, Cs, e_act, (0.0, 0.0), eta_w=eta_w)
    keep = ("dK", "PElin", "Ebar", "Q2", "Ev", "DE", "OmK")
    out = dict(e_act=e_act, grid=[N1, N2], strips={})
    for r1 in strips:
        kp = S0.step_at(G, Cs, e_act, (r1, r1), consts=consts, eta_w=eta_w, keep=keep)[5]
        km = S0.step_at(G, Cs, e_act, (r1, -r1), consts=consts, eta_w=eta_w, keep=keep)[5]
        dKp, dKm = kp["dK"], km["dK"]
        DdKp, DdKm = deriv(G, dKp), deriv(G, dKm)
        o = dict(
            dK_l1=vec_norm(l1w(G, dKp, dKm)), dK_sup=sup_vec(dKp, dKm),
            DdK_l1=mat_norm(l1w(G, DdKp, DdKm)), DdK_sup=sup_mat(DdKp, DdKm),
            DdKT_l1=mat_norm(np.swapaxes(l1w(G, DdKp, DdKm), -1, -2)),
            Elin_l1=vec_norm(l1w(G, kp["PElin"], km["PElin"])), Elin_sup=sup_vec(kp["PElin"], km["PElin"]),
            Ebar_sup=sup_vec(kp["Ebar"], km["Ebar"]), D2X_sup=sup_vec(kp["Q2"], km["Q2"]),
            E_l1=vec_norm(l1w(G, kp["Ev"], km["Ev"])), DE_l1=mat_norm(l1w(G, kp["DE"], km["DE"])),
            OmK_l1=mat_norm(l1w(G, kp["OmK"], km["OmK"])))
        out["strips"]["%.10g" % r1] = o
        del kp, km
        log("  shape: rho1 = rho - %.3f delta0 done (%.0fs)" % ((S0.RHO - r1) / S0.DELTA0, time.time() - t0))
    k0 = S0.step_at(G, Cs, e_act, (0.0, 0.0), consts=consts, eta_w=eta_w, keep=keep)[5]
    D0 = deriv(G, k0["dK"])
    out["real"] = dict(dK_l1=vec_norm(l1w_real(G, k0["dK"])), DdK_l1=mat_norm(l1w_real(G, D0)),
                       DdKT_l1=mat_norm(np.swapaxes(l1w_real(G, D0), -1, -2)),
                       DE_l1=mat_norm(l1w_real(G, k0["DE"])), OmK_l1=mat_norm(l1w_real(G, k0["OmK"])))
    ri = S0.RHOINF
    kp = S0.step_at(G, Cs, e_act, (ri, ri), consts=consts, eta_w=eta_w, keep=keep)[5]
    km = S0.step_at(G, Cs, e_act, (ri, -ri), consts=consts, eta_w=eta_w, keep=keep)[5]
    out["rhoinf"] = dict(dK_l1=vec_norm(l1w(G, kp["dK"], km["dK"])))
    out["time"] = time.time() - t0
    return out


# ============================================================================================ 2. truncated candidates
class TGrid(S0.Grid):
    """S0's grid with the candidate v cut at |b_k| > cut (graph torus of r1_norms.Cand.geometry)."""

    def __init__(self, N1, N2, cut):
        super().__init__(N1, N2)
        self.cand.co = r1_norms.load("lower", cut)
        self.nterms = len(self.cand.co)


def torus_at(G, y):
    """K, the frame objects, E (closed form: E = (0, 0, -c R, -c (1 - p) R), R = D_t p + V_q), A = DX_H(K) at the
    shifted grid y.  The graph torus has H(K) = 0 identically (P2 = p + J, J = -p^2/2 - V)."""
    o = r1_norms.objects(G.cand, y[0], y[1], C_TIME)
    g = o["g"]
    s = G.cand.nu - 1
    R = s * g["ps"] + g["pf"] + g["Vq"]
    E = np.zeros(g["p"].shape + (4,), complex)
    E[..., 2] = -C_TIME * R
    E[..., 3] = -C_TIME * (1 - g["p"]) * R
    _, _, Hs = r1_norms.frame_objects(g, C_TIME)
    A = np.einsum("ab,...bc->...ac", JX, Hs)
    return o, g, E, A


def dXH(g, dK):
    """X_H(K + dK) - X_H(K), H = c (P1^2/2 - P1 + P2 + V(Q1 + Q2, Q2)), by difference formulas (no cancellation)."""
    dq = dK[..., 0] + dK[..., 1]; df = dK[..., 1]
    dVq = 0; dVf = 0
    for m in model.M_MODES:
        a = S0.EPSA_F[m]
        X = TWO_PI * (2 * g["q"] - m * g["ph"])
        d = TWO_PI * (2 * dq - m * df)
        ds = 2 * np.cos(X + d / 2) * np.sin(d / 2)                       # sin(X + d) - sin X
        dVq = dVq + a * 4 * math.pi * ds                                  # V_q = sum a 4 pi sin X
        dVf = dVf - a * 2 * math.pi * m * ds                              # V_phi = -sum a 2 pi m sin X
    out = np.zeros(dK.shape, complex)
    out[..., 0] = C_TIME * dK[..., 2]
    out[..., 2] = -C_TIME * dVq
    out[..., 3] = -C_TIME * (dVq + dVf)
    return out


def step_iso(G, y, consts=None):
    """The isoenergetic additive step (route-A form; HL19 Lemma 6.1, blueprint-I Lemma border-solve, the signs of
    step0_actual.step_at) of the graph torus at the shifted grid y: eta^L = -B L^T E, eta^N = L^T Omega0 E,
    xi^N = xi0 - R eta^N, g^L = T xi^N + omega xi^w - eta^L, xi^L = R g^L, DK = L xi^L + N xi^N, the new frequency
    omega1 = omega - xi^w omega (the sign that makes the new error quadratic; checked on the grid), with (xi0, xi^w)
    from the bordered system [[<T>, omega], [<Y>, 0]] (xi0, xi^w) = (<eta^L> + <T R eta^N>, eta^w + <Y R eta^N>),
    eta^w = 0 (the graph torus has H(K) = E0 = 0).  R1's <T> is singular (H is linear in P2: <T> = diag(1.96, 0)),
    so only the bordered (isoenergetic) step exists; this is the step of the iso hybrid."""
    o, g, E, A = torus_at(G, y)
    L, B, N, T, Y = o["L"], o["B"], o["N"], o["T"], o["Y"]
    LT = np.swapaxes(L, -1, -2)
    etaL = -S0.mv(S0.mm(B, LT), E)
    etaN = S0.mv(LT, S0.mv(OM, E))
    uN, _ = G.solve(etaN)
    if consts is None:
        TT = np.zeros((3, 3), complex)
        TT[:2, :2] = G.coef_at(T)[0, 0]; TT[:2, 2] = G.omega; TT[2, :2] = G.coef_at(Y)[0, 0]
        rhs = np.concatenate([G.coef_at(etaL)[0, 0] + G.coef_at(S0.mv(T, uN))[0, 0],
                              [G.coef_at(np.einsum("...j,...j->...", Y, uN)[..., None])[0, 0, 0]]])
        sol = np.linalg.solve(TT, rhs)
        consts = (sol[:2], sol[2])
    xi0, xiw = consts
    xiN = xi0 - uN
    gL = S0.mv(T, xiN) + G.omega * xiw - etaL
    xiL, _ = G.solve(gL)
    dK = S0.mv(L, xiL) + S0.mv(N, xiN)
    dwdK = G.domega(dK)
    dwK1 = G.domega(dK) + np.stack([C_TIME * (G.cand.nu - 1 + g["us"] * (G.cand.nu - 1) + g["uf"]),
                                    C_TIME + 0 * g["p"], C_TIME * (g["ps"] * (G.cand.nu - 1) + g["pf"]),
                                    C_TIME * ((G.cand.nu - 1) * (g["ps"] + g["Js"]) + g["pf"] + g["Jf"])], axis=-1)
    Elin = E + S0.mv(A, dK) - dwdK + xiw * dwK1        # E_lin~ at omega1 = omega - xi^w omega (Lemma bpI:p2s2hc:error)
    E1 = E + dXH(g, dK) - dwdK + xiw * dwK1            # the actual new error at omega1
    L1 = L + deriv(G, dK)
    OmK = S0.mm(LT, S0.mm(OM, L))                                      # Lagrangian defects of K and K1
    OmK1 = S0.mm(np.swapaxes(L1, -1, -2), S0.mm(OM, L1))
    return dict(E=E, dK=dK, Elin=Elin, E1=E1, DE=deriv(G, E), T=T, consts=consts, xiw=complex(xiw), OmK=OmK,
                OmK1=OmK1)


def trunc_measure(L_digits, strips, N1=512, N2=128, log=print):
    out = {}
    for Ld in L_digits:
        t0 = time.time()
        G = TGrid(N1, N2, 10.0 ** (-Ld))
        z0 = step_iso(G, (0.0, 0.0))
        xi0 = z0["consts"]
        r = dict(L=Ld, nterms=G.nterms, strips={}, xiw=abs(z0["xiw"]))
        a = step_iso(G, (S0.RHO, S0.RHO), xi0); b = step_iso(G, (S0.RHO, -S0.RHO), xi0)
        r["e_sup"] = sup_vec(a["E"], b["E"]); r["e_l1"] = vec_norm(l1w(G, a["E"], b["E"]))
        for r1 in strips:
            a = step_iso(G, (r1, r1), xi0); b = step_iso(G, (r1, -r1), xi0)
            Da, Db = deriv(G, a["dK"]), deriv(G, b["dK"])
            r["strips"]["%.10g" % r1] = dict(
                dK_l1=vec_norm(l1w(G, a["dK"], b["dK"])), dK_sup=sup_vec(a["dK"], b["dK"]),
                DdK_l1=mat_norm(l1w(G, Da, Db)), DdKT_l1=mat_norm(np.swapaxes(l1w(G, Da, Db), -1, -2)),
                Elin_l1=vec_norm(l1w(G, a["Elin"], b["Elin"])), Elin_sup=sup_vec(a["Elin"], b["Elin"]),
                E1_sup=sup_vec(a["E1"], b["E1"]), E1_l1=vec_norm(l1w(G, a["E1"], b["E1"])),
                R2_sup=sup_vec(a["E1"] - a["Elin"], b["E1"] - b["Elin"]),
                DE_l1=mat_norm(l1w(G, a["DE"], b["DE"])), OmK_l1=mat_norm(l1w(G, a["OmK"], b["OmK"])),
                OmK1_l1=mat_norm(l1w(G, a["OmK1"], b["OmK1"])))
        z = step_iso(G, (0.0, 0.0), xi0)
        D0 = deriv(G, z["dK"])
        r["real"] = dict(dK_l1=vec_norm(l1w_real(G, z["dK"])), DdK_l1=mat_norm(l1w_real(G, D0)),
                         DdKT_l1=mat_norm(np.swapaxes(l1w_real(G, D0), -1, -2)),
                         DE_l1=mat_norm(l1w_real(G, z["DE"])), E_l1=vec_norm(l1w_real(G, z["E"])),
                         OmK_l1=mat_norm(l1w_real(G, z["OmK"])), OmK1_l1=mat_norm(l1w_real(G, z["OmK1"])))
        ri = S0.RHOINF
        a = step_iso(G, (ri, ri), xi0); b = step_iso(G, (ri, -ri), xi0)
        r["rhoinf"] = dict(dK_l1=vec_norm(l1w(G, a["dK"], b["dK"])))
        out[Ld] = r
        log("  trunc L = %d (%d terms): e_l1 = %.3e (%.0fs)" % (Ld, G.nterms, r["e_l1"], time.time() - t0))
    return out


def sizes_measure(L_digits=(8, 9, 15, 17), tols=(2e-12, 2e-13), N1=512, N2=128, log=print):
    """Model sizes (kernel cost proxy, design section 3.3): the number of Fourier terms (full lattice) a model needs so
    that its dropped weighted l^1 mass on T_rho is <= tol, for E_L, the character exp(2 pi i 2q) of the composition of
    H with the torus, and the step DK."""
    def weighted(G, fpp, fpm):
        m1, m2, z1, z2 = _masks(G)
        c1 = np.abs(G.coef_at(fpp)); c2 = np.abs(G.coef_at(fpm))
        if c1.ndim > 2:
            c1 = c1.max(axis=tuple(range(2, c1.ndim))); c2 = c2.max(axis=tuple(range(2, c2.ndim)))
        half = np.concatenate([c1[m1 & ~z1], c2[m2 & ~z2]])
        return np.concatenate([half, half, c1[z1], c2[z2]])

    def nterms(w, tol):
        cs = np.cumsum(np.sort(w))
        return int(len(w) - np.searchsorted(cs, tol, side="right"))
    rho = S0.RHO
    out = {}
    for Ld in L_digits:
        G = TGrid(N1, N2, 10.0 ** (-Ld))
        z = step_iso(G, (0.0, 0.0))
        a = step_iso(G, (rho, rho), z["consts"]); b = step_iso(G, (rho, -rho), z["consts"])
        qa = torus_at(G, (rho, rho))[1]["q"]; qb = torus_at(G, (rho, -rho))[1]["q"]
        ca, cb = np.exp(2j * math.pi * 2 * qa), np.exp(2j * math.pi * 2 * qb)
        r = dict(v_terms=G.nterms)
        for tol in tols:
            r["%.0e" % tol] = dict(E=nterms(weighted(G, a["E"], b["E"]), tol), chi=nterms(weighted(G, ca, cb), tol),
                                  dK=nterms(weighted(G, a["dK"], b["dK"]), tol))
        out[Ld] = r
        log("  sizes L = %d: %s" % (Ld, r))
    return out


# ============================================================================================ 3. the restarted theorem
def transfer(D, m, rho0, e_K=None):
    """Caps of K1 from those of K and the step increments m (Lemmas bp:p2s2hc:frames, bp:p2s2hc:torsion); returns the
    restart data D1 (strip rho1 = m['rho1'], margin mu1) and the increments.  Frame values of K: the package caps
    (sigma - mu = 1.05 x sampled sup)."""
    mu = D["mu"]; n = D["n"]
    rho1 = m["rho1"]
    d0, d1, d1t = m["dK_l1"], m["DdK_l1"], m["DdKT_l1"]
    d0R, d1R, d1tR = m["real"]["dK_l1"], m["real"]["DdK_l1"], m["real"]["DdKT_l1"]
    ell, ellt, beta = float(D["sK"] - mu), float(D["sLt"] - mu), float(D["sB"] - mu)
    nN, nNt, Ts, tinv = float(D["sN"] - mu), float(D["sNt"] - mu), float(D["Tsup"]), float(D["sT"] - mu)
    cTh, M2, M1 = float(D["cTh"]), float(D["M2"]), float(D["M1"])

    def frames(d0_, d1_, d1t_):
        g = ellt * d1_ + d1t_ * ell + d1t_ * d1_
        assert beta * g < 1
        b1 = beta / (1 - beta * g); db = beta ** 2 * g / (1 - beta * g)
        nD = d1_ * b1 + ell * db; nDt = b1 * d1t_ + db * ellt
        dab = nDt * cTh * (nN + nD) + nNt * 2 * M2 * d0_ * (nN + nD) + nNt * cTh * nD      # |T_ab(K1) - T_ab(K)|
        return dict(g=g, b1=b1, db=db, nD=nD, nDt=nDt, dab=dab)
    fs, fr = frames(d0, d1, d1t), frames(d0R, d1R, d1tR)
    lam = 3
    dl1 = min(1.0, (rho1 - float(D["rhoinf"])) / (2 * lam))
    e1 = m["e1"]
    dE1 = n * e1 / dl1                                                    # Cauchy: |DE1| on T_{rho1 - delta0'}
    # |Omega_K1|: measured (the certificate computes DK1^T Omega0 DK1 exactly from the two polynomials), else a
    # generous geometry-lemma-type value
    oK1 = m.get("OmK1", 10 * n * e1 / (float(D["gamma"]) * dl1 ** 2))
    oK1R = m["real"].get("OmK1", oK1)
    wB = lambda l_, lt_, dE: lt_ * (4 * n * M1) * l_ + dE * (2 * n * l_ + lt_)   # |W| (Lemma bp:p2s2hc:torsion)
    w1 = wB(ell + d1, ellt + d1t, dE1)
    loc1 = (nNt + fs["nDt"]) * fs["b1"] * dE1 + fs["b1"] ** 3 * w1 * oK1
    loc1R = (nNt + fr["nDt"]) * fr["b1"] * dE1 + fr["b1"] ** 3 * w1 * oK1R
    # local part of K's torsion (torsion polynomial): sigma_Nt sigma_B |DE| + sigma_B^3 w |Omega_K|
    w0 = lambda dE: wB(ell, ellt, dE)
    dEK, dEKR = m.get("DE_K", 0.0), m["real"].get("DE_K", 0.0)
    loc0 = nNt * beta * dEK + beta ** 3 * w0(dEK) * m.get("OmK", 0.0)
    loc0R = nNt * beta * dEKR + beta ** 3 * w0(dEKR) * m["real"].get("OmK", 0.0)
    T1 = Ts + fs["dab"] + loc1 + loc0                                    # Delta form
    T1_direct = (nNt + fs["nDt"]) * cTh * (nN + fs["nD"]) + loc1
    T1 = min(T1, T1_direct)
    tA = fr["dab"] + loc1R + loc0R                                        # |<T1> - <T>| (real torus)
    assert tinv * tA < 1
    tinv1 = tinv / (1 - tinv * tA)
    mu1 = F(mu) - Frup(2 * max(d0, d1))
    assert mu1 > 0
    D1 = dict(D)
    D1.update(rho=Frup(rho1, down=True), mu=mu1,
              sK=D["sK"] - mu / 2 + mu1 / 2,
              sB=Frup(beta + fs["db"]) + mu1, sT=Frup(tinv1) + mu1,
              sLt=Frup(ellt + d1t) + mu1, sN=Frup(nN + fs["nD"]) + mu1, sNt=Frup(nNt + fs["nDt"]) + mu1,
              Tsup=Frup(T1))
    for k_, base in (("B", D1["sB"]), ("Tinv", D1["sT"]), ("Lt", D1["sLt"]), ("N", D1["sN"]), ("Nt", D1["sNt"]),
                     ("Tsup", D1["Tsup"])):
        D1["bud_" + k_] = base / 10
    inc = dict(d0=d0, d1=d1, d1t=d1t, mu1=float(mu1), dB=fs["db"], dN=fs["nD"], dNt=fs["nDt"], T1=T1,
               T1_direct=T1_direct, tA=tA, tinv1=tinv1, dE1=dE1, loc1=loc1, loc0=loc0)
    return D1, inc


def Frup(x, down=False, digits=12):
    """a rational upper (lower if down) bound of x with `digits` significant digits."""
    x = float(x)
    if x == 0:
        return F(0)
    e = math.floor(math.log10(abs(x))) - digits
    q = F(math.floor(x / 10.0 ** e) if down else math.ceil(x / 10.0 ** e)) * F(10) ** e
    return q


def restart_threshold(D1, route, iso):
    """log10 e1* of the restarted theorem on the data D1 (route A' = A7 with L8', k = 5; route B = B6 with the
    levers of B7 at ratio 2, decay bound 1/2 (the B7 best on R1))."""
    if route == "A":
        name, o, cw, k = T2.routeA_variants(D1)[-1]
        Dv = T2.with_caps(D1, F(1, 20))
        o = dict(o); o["torsion_cap"] = Dv["Tsup_cap"]; o["torsion_real"] = o["torsion_cap"]
        st, ct = T2.c_stages(Dv, cw, max(k, 1))
        le, _, why = T2.thresholdA(Dv, o, iso, k=k, c_stage=st, c_tail=ct)
    else:
        Dv = T2.with_caps(D1, F(1, 20))
        o = dict(L1=True, keep_delta=True, avg_full_bite=True, cTh=Dv["cTh"], theta=F(1, 16), free_budgets=True,
                 aniso=True)
        st, ct = T2.c_stages(Dv, "freq", 5)
        le, _, why = T2.thresholdB(Dv, o, iso, 5, st, ct)
    return le, why


# ============================================================================================ 4. assembling
def shape_hybrid(sh, routes=("A", "B"), forms=(False, True), log=print):
    """Hybrid threshold of R1's residual shape at each restart strip: the largest e with A e^2 <= e1*(rho1, increments
    at e).  The increments are linear in e; mu1 = mu - 2 max(d0, d1) > 0 caps e (the frozen |DK| and ball budgets).
    Guarded fixed-point iteration: e <- min(sqrt(e1*/A), cap), halving when the transfer fails."""
    D = T2.package("R1")
    rows = []
    for key, st in sh["strips"].items():
        rho1 = float(key)
        A = SLACK * st["Elin_l1"] + float(D["M2"]) / 2 * st["dK_l1"] ** 2
        cap = 0.999 * float(D["mu"]) / (2 * max(st["dK_l1"], st["DdK_l1"]))

        def m_at(e):
            return dict(rho1=rho1, dK_l1=st["dK_l1"] * e, DdK_l1=st["DdK_l1"] * e, DdKT_l1=st["DdKT_l1"] * e,
                        e1=A * e * e, DE_K=st["DE_l1"] * e, OmK=st["OmK_l1"] * e,
                        real=dict(dK_l1=sh["real"]["dK_l1"] * e, DdK_l1=sh["real"]["DdK_l1"] * e,
                                  DdKT_l1=sh["real"]["DdKT_l1"] * e, DE_K=sh["real"]["DE_l1"] * e,
                                  OmK=sh["real"]["OmK_l1"] * e))
        for route in routes:
            for iso in forms:
                e = min(cap, 1e-4)
                best = None
                for _ in range(8):
                    try:
                        D1, inc = transfer(D, m_at(e), float(D["rho"]))
                        le1, why = restart_threshold(D1, route, iso)
                    except AssertionError:
                        e *= 0.5
                        continue
                    if A * e * e <= 10 ** le1 and (best is None or e > best[0]):
                        best = (e, le1, why, inc)
                    e_new = min(math.sqrt(10 ** le1 / A), cap)
                    if abs(math.log10(e_new / e)) < 0.005:
                        break
                    e = e_new if e_new > e else max(e_new, 0.5 * e)
                if best is None:
                    log("| %.3f | %s | %s | %.3e | -- | -- | no admissible e |" % (
                        (float(D["rho"]) - rho1) / float(S0.DELTA0), route, "iso" if iso else "fixed", A))
                    continue
                e, le1, why, inc = best
                bind = list(why) + (["mu1 -> 0 (|DK| and ball budgets)"] if e > 0.9 * cap else [])
                rows.append(dict(rho1=rho1, strip_loss_delta0=(float(D["rho"]) - rho1) / float(S0.DELTA0), route=route,
                                 form="iso" if iso else "fixed", A=A, Elin_l1=st["Elin_l1"],
                                 Taylor=float(D["M2"]) / 2 * st["dK_l1"] ** 2, cap=cap, log10_e1star=le1,
                                 log10_hybrid=math.log10(e), binding=bind, increments=inc,
                                 closeness_rhoinf=sh["rhoinf"]["dK_l1"] * e))
                log("| %.2f | %s | %s | %.3e | %.2f | %.2f | %s |" % (
                    rows[-1]["strip_loss_delta0"], route, rows[-1]["form"], A, le1, math.log10(e), ", ".join(bind)))
    return rows


def trunc_hybrid(tr, routes=("A",), forms=(False,), plain=None, log=print):
    """For each truncated candidate: the plain margin log10(e*/e_L) and the best hybrid margin log10(e1*/e1)."""
    D = T2.package("R1")
    rows = []
    for Ld, r in sorted(tr.items()):
        for route in routes:
            for iso in forms:
                best = None
                for key, st in r["strips"].items():
                    rho1 = float(key)
                    e1 = SLACK * st["Elin_l1"] + float(D["M2"]) / 2 * st["dK_l1"] ** 2
                    m = dict(rho1=rho1, dK_l1=st["dK_l1"], DdK_l1=st["DdK_l1"], DdKT_l1=st["DdKT_l1"], e1=e1,
                             DE_K=st["DE_l1"], OmK=st["OmK_l1"], OmK1=st["OmK1_l1"],
                             real=dict(dK_l1=r["real"]["dK_l1"], DdK_l1=r["real"]["DdK_l1"],
                                       DdKT_l1=r["real"]["DdKT_l1"], DE_K=r["real"]["DE_l1"],
                                       OmK=r["real"]["OmK_l1"], OmK1=r["real"]["OmK1_l1"]))
                    try:
                        D1, inc = transfer(D, m, float(D["rho"]))
                    except AssertionError:
                        continue
                    le1, why = restart_threshold(D1, route, iso)
                    marg = le1 - math.log10(e1)
                    if best is None or marg > best["margin"]:
                        best = dict(rho1=rho1, strip_loss_delta0=(float(D["rho"]) - rho1) / float(S0.DELTA0),
                                    e1=e1, E1_sup=st["E1_sup"], log10_e1star=le1, margin=marg, binding=why,
                                    increments=inc)
                pl = plain[(route, iso)]
                row = dict(L=Ld, nterms=r["nterms"], route=route, form="iso" if iso else "fixed", e_sup=r["e_sup"],
                           e_l1=r["e_l1"], plain_margin=pl - math.log10(r["e_l1"]), hybrid=best,
                           disp_rhoinf=r["rhoinf"]["dK_l1"])
                rows.append(row)
                if best is None:
                    log("| %d | %d | %.2e | %+.2f | -- | -- | -- |" % (Ld, r["nterms"], r["e_l1"], row["plain_margin"]))
                else:
                    log("| %d | %d | %.2e | %+.2f | %.2e (direct sup %.2e) | %.2f | %+.2f |" % (
                        Ld, r["nterms"], r["e_l1"], row["plain_margin"], best["e1"], best["E1_sup"],
                        best["strip_loss_delta0"], best["margin"]))
    return rows


def main():
    args = sys.argv[1:]
    quick = "--quick" in args
    if "--sizes" in args:
        out = dict(sizes=sizes_measure())
        if "--json" in args:
            json.dump(out, open(args[args.index("--json") + 1], "w"), indent=1, default=str)
        return
    do_shape = "--shape" in args or "--trunc" not in args
    do_trunc = "--trunc" in args or "--shape" not in args
    rho, d0 = S0.RHO, S0.DELTA0
    losses = (0, 0.5, 1, 2, 3) if quick else (0, 0.25, 0.5, 1, 1.5, 2, 3)
    strips = [rho - t * d0 for t in losses]
    out = dict(params=dict(rho=rho, rhoinf=S0.RHOINF, delta0=d0, c=C_TIME, slack=SLACK, strip_losses=losses))
    D = T2.package("R1")
    plain = {}
    for route in ("A", "B"):
        for iso in (False, True):
            plain[(route, iso)] = restart_threshold(D, route, iso)[0]
    out["plain"] = {"%s %s" % (r, "iso" if i else "fixed"): v for (r, i), v in plain.items()}
    print("plain v2 on R1 (log10 e*): " + ", ".join("%s %s %.2f" % (r, "iso" if i else "fixed", v)
                                                    for (r, i), v in plain.items()))
    if do_shape:
        print("\n== R1's residual shape (normalised by e = sup_{T_rho}|E|), grid 1024 x 256")
        sh = shape_measure(strips)
        out["shape"] = sh
        if "--json" in args:
            json.dump(out, open(args[args.index("--json") + 1], "w"), indent=1, default=str)
        print("| strip loss / delta0 | |DK^|_l1 | |D DK^|_l1 | |P E_lin^|_l1 (sup) | leading |Ebar^| sup |")
        print("|---:|---:|---:|---:|---:|")
        for key, st in sh["strips"].items():
            print("| %.2f | %.3e | %.3e | %.3e (%.3e) | %.3e |" % ((rho - float(key)) / d0, st["dK_l1"], st["DdK_l1"],
                                                                st["Elin_l1"], st["Elin_sup"], st["Ebar_sup"]))
        print("real torus: |DK^|_l1 %.3e, |D DK^|_l1 %.3e;  T_rho_inf: |DK^|_l1 %.3e" % (
            sh["real"]["dK_l1"], sh["real"]["DdK_l1"], sh["rhoinf"]["dK_l1"]))
        print("\n| strip loss / delta0 | route | form | A | log10 e1* | log10 hybrid e* | binding |")
        print("|---:|---|---|---:|---:|---:|---|")
        out["shape_rows"] = shape_hybrid(sh)
    if do_trunc:
        Ls = (6, 8, 10, 12) if quick else (5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15)
        if "--L" in args:
            Ls = tuple(int(x) for x in args[args.index("--L") + 1].split(","))
        print("\n== truncated candidates (v cut at 10^-L), grid 512 x 128")
        tr = trunc_measure(Ls, strips)
        out["trunc"] = {str(k): v for k, v in tr.items()}
        for route, iso in (("A", False), ("B", False), ("A", True), ("B", True)):
            print("\n%s, %s: | L | terms | e_L (l1, T_rho) | plain margin | e1 (l1 bound) | best strip loss | hybrid margin |"
                  % (route, "iso" if iso else "fixed"))
            print("|---:|---:|---:|---:|---:|---:|---:|")
            out.setdefault("trunc_rows", []).extend(trunc_hybrid(tr, routes=(route,), forms=(iso,), plain=plain))
    if "--json" in args:
        json.dump(out, open(args[args.index("--json") + 1], "w"), indent=1, default=str)


if __name__ == "__main__":
    main()
