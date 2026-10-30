#!/usr/bin/env python3
"""SJS-LG00: norms of the LG00 torus in the certificate's chart, thresholds of the three theorems, digits and support.

Untrusted design tooling (double precision).  Chart of the certificate (period-1 angles, scaled actions, time scale):
    theta = phi / 2 pi,   I = I0 + ell a,   h~(theta, a) = c h(2 pi theta, I0 + ell a) / (2 pi ell)
(conformally symplectic with factor 2 pi ell, so h~ has the time-c flow of h); torus
    K~(theta) = (theta + u(2 pi theta)/(2 pi),  v(2 pi theta)/ell),   omega~ = c omega / (2 pi).
Identity angle frame only (unimodular frames are not explored here).

Objects (as in scripts/certifier/lunar_oracle.py and v2_adapter.py):
  sK, sB          sup over the distinguished boundary of T_rho (sampled, 'sup') and weighted l1 ('l1') of the row
                  sums of DK~ and (DK~^T DK~)^{-1}, + mu;
  torsion         fixed: |<T~>^{-1}| row sums; iso: the extended 3 x 3 [[T~, omega~], [Y, 0]] (lunar_oracle.frame);
  M and parts     majorant on D = T_{rho_H} x polydisc: rho_H = rho + sup|Im u~| + mu, radius sup|v~| + mu; every
                  (m, k) term of h (LG00's form (15)) bounded by |C| e^{2 pi rho_H |k|_1} |2I|^{m/2-d} (extreme
                  point of the disc) times the derivative factors -- the shape of the landed ball arithmetic;
  Lt, N, Nt, Tsup sampled sups for the v2 mirror (v2_adapter.extras);
  gamma           inf |k|_1 |k . (r, 1)| = 0.2251 (convergents of r, mpmath; certified only by the CF argument),
                  gamma~ = gamma_dir |omega~_2|.
Theorems: v0 = sealed iso KAM.Iso.Apost.g1_explicit (thresholds.current_iso) and fixed KAM.Apost
(thresholds.current_fixed); v1 = sharp (thresholds.sharp, iso and fixed); route A = route_a_lean_mirror (`routeAOk`,
classical and frequency-specific stage constants, fixed and iso).
Digits/support: the truncation keeps k with |c_k| e^{2 pi rho |k|_1} >= 10^-L (any component of K~, relative to the
largest coefficient); e(L) = sum over the dropped k of (|DX h~| + 2 pi |k . omega~|) |c_k| e^{2 pi rho |k|_1}
(first-order effect of the truncation), measured for L <= 12 and extrapolated (log-linear); S(L) the kept count
(full lattice), fitted S = a L^2 + b L + c.
"""
import os, sys, math, json, argparse
import numpy as np
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
ROOT = os.path.abspath(os.path.join(HERE, "..", "..", ".."))
sys.path.insert(0, os.path.join(ROOT, "scripts", "apost_sharp"))
sys.path.insert(0, os.path.join(ROOT, "scripts", "certifier"))
import lg00_torus as TT               # noqa: E402
import lg00_model as MM               # noqa: E402
import thresholds as TH               # noqa: E402  (read-only use)
import thresholds_v2 as T2            # noqa: E402
import route_a_lean_mirror as RA      # noqa: E402

TP = 2 * math.pi
J4 = TT.J4
OM4 = -J4
GAMMA_DIR = 0.2250971845208865        # inf |k|_1 |k.(r, 1)|, Gamma' (lg00_freq in the doc; mpmath convergents)


def q(x):
    return F(x).limit_denominator(10 ** 15) if not isinstance(x, F) else x


class Oracle:
    def __init__(self, npz):
        d = np.load(npz)
        self.u, self.v, self.I0, self.om = d["u"], d["v"], d["I0"], d["om"]
        self.N = self.u.shape[0]
        Q, lam = MM.normal_modes()
        self.form = TT.action_angle_form(Q)
        self.H = TT.AAHam(self.form)
        N = self.N
        k = np.fft.fftfreq(N, 1 / N)
        self.k1, self.k2 = np.meshgrid(k, k, indexing="ij")
        self.U = np.fft.fft2(self.u, axes=(0, 1)) / N ** 2
        self.V = np.fft.fft2(self.v, axes=(0, 1)) / N ** 2
        # noise floor: drop coefficients below 1e-16 of the largest (FFT round-off must not meet strip weights)
        for A in (self.U, self.V):
            m = np.abs(A) < 1e-16 * np.abs(A).max()
            A[m] = 0

    # ---------------------------------------------------------------- torus objects at an imaginary shift y
    def _eval(self, C, y):
        """grid values of the series with coefficients C (N, N, ...) at theta + i y (period-1 units)."""
        w = np.exp(-TP * (self.k1 * y[0] + self.k2 * y[1]))
        return np.fft.ifft2(C * w[(...,) + (None,) * (C.ndim - 2)], axes=(0, 1)) * self.N ** 2

    def chart(self, y, ell):
        """phi, I (complex grids) of K at theta + i y, and DK~ (N, N, 4, 2) in the scaled chart."""
        N = self.N
        th = np.arange(N) / N
        t1, t2 = np.meshgrid(th, th, indexing="ij")
        u = self._eval(self.U, y); v = self._eval(self.V, y)
        phi = np.stack([TP * (t1 + 1j * y[0]), TP * (t2 + 1j * y[1])], -1) + u
        I = self.I0 + v
        L = np.zeros((N, N, 4, 2), complex)
        for j in range(2):
            mult = 1j * (self.k1 if j == 0 else self.k2)      # d/dphi_j; d/dtheta_j = 2 pi d/dphi_j
            du = self._eval(self.U * mult[..., None], y)
            dv = self._eval(self.V * mult[..., None], y)
            L[..., 0:2, j] = du                                 # d/dtheta (u/2pi) = du/dphi
            L[..., j, j] += 1.0
            L[..., 2:4, j] = TP * dv / ell
        return phi, I, L, u, v

    def hderivs(self, phi, I, c, ell, order=2):
        """scaled derivatives of h~ in (theta, a): factors (2 pi)^{|alpha|} ell^{|beta|} c/(2 pi ell)."""
        out = self.H.derivs(phi, I, order=order)
        sc = np.array([TP, TP, ell, ell])
        pre = c / (TP * ell)
        h = out[0] * pre
        g = out[1] * sc * pre
        Hs = out[2] * np.einsum("i,j->ij", sc, sc) * pre
        res = [h, g, Hs]
        if order >= 3:
            res.append(out[3] * np.einsum("i,j,k->ijk", sc, sc, sc) * pre)
        return res

    # ---------------------------------------------------------------- geometry and torsion
    def geometry(self, rho, ell):
        corners = [(rho, rho), (rho, -rho)]
        sK = sB = 0.0; Lt = Nn = Nt = 0.0; imu = 0.0; dv = 0.0
        for y in corners:
            phi, I, L, u, v = self.chart(y, ell)
            G = np.einsum("...ki,...kj->...ij", L, L)
            B = np.linalg.inv(G)
            Nm = np.einsum("ab,...bk,...kj->...aj", J4, L, B)
            sK = max(sK, float(np.abs(L).sum(-1).max()))
            sB = max(sB, float(np.abs(B).sum(-1).max()))
            Lt = max(Lt, float(np.abs(L).sum(-2).max()))
            Nn = max(Nn, float(np.abs(Nm).sum(-1).max()))
            Nt = max(Nt, float(np.abs(Nm).sum(-2).max()))
            imu = max(imu, float(np.abs((u / TP).imag).max()))
            dv = max(dv, float(np.abs(v / ell).max()))
        # weighted l1 (the landed checker's construction): DK~ entries and the Gram inverse by its own FFT
        w = np.exp(TP * rho * (np.abs(self.k1) + np.abs(self.k2)))
        rows = np.zeros(4)
        for j in range(2):
            mult = np.abs(self.k1 if j == 0 else self.k2)
            rows[0:2] += (np.abs(self.U) * mult[..., None] * w[..., None]).sum(axis=(0, 1))
            rows[2:4] += (TP * np.abs(self.V) * mult[..., None] * w[..., None]).sum(axis=(0, 1)) / ell
        rows[0] += 1; rows[1] += 1
        sK_l1 = float(rows.max())
        return dict(sK=sK, sB=sB, Lt=Lt, N=Nn, Nt=Nt, iota=imu, vdev=dv, sK_l1=sK_l1)

    def torsion(self, c, ell):
        N = self.N
        phi, I, L, u, v = self.chart((0.0, 0.0), ell)
        phi, I, L = phi.real, I.real, L.real
        h, g, Hs = [x.real for x in self.hderivs(phi, I, c, ell)]
        B = np.linalg.inv(np.einsum("...ki,...kj->...ij", L, L))
        Nm = np.einsum("ab,...bk,...kj->...aj", J4, L, B)
        DX = np.einsum("ab,...bc->...ac", J4, Hs)
        omt = c * self.om / TP
        mult = TP * 1j * (omt[0] * self.k1 + omt[1] * self.k2)
        DN = np.fft.ifft2(np.fft.fft2(Nm, axes=(0, 1)) * mult[..., None, None], axes=(0, 1)).real
        T = np.einsum("...ai,ab,...bj->...ij", Nm, OM4, np.einsum("...ab,...bj->...aj", DX, Nm) - DN)
        Y = np.einsum("...a,...aj->...j", g, Nm)
        ext = np.zeros((N, N, 3, 3))
        ext[..., :2, :2] = T; ext[..., :2, 2] = omt; ext[..., 2, :2] = Y
        Tav = T.mean(axis=(0, 1)); Eav = ext.mean(axis=(0, 1))
        return dict(tinv_fixed=float(np.abs(np.linalg.inv(Tav)).sum(1).max()),
                    tinv_iso=float(np.abs(np.linalg.inv(Eav)).sum(1).max()),
                    Tsup=float(np.abs(T).sum(-1).max()), Tav=Tav, energy=float(h.mean()), omt=omt)

    # ---------------------------------------------------------------- H majorant on D
    def majorant(self, c, ell, rhoH, R):
        """bounds G1[i], G2[i,j], G3[i,j,k] of |d h~| on T_{rhoH} x polydisc(I0, ell R) by the term-wise construction."""
        ks = np.arange(-TT.KM, TT.KM + 1)
        sc = np.array([TP, TP, ell, ell]); pre = c / (TP * ell)
        G1 = np.zeros(4); G2 = np.zeros((4, 4)); G3 = np.zeros((4, 4, 4))
        lo = 2 * (self.I0 - ell * np.asarray(R)); hi = 2 * (self.I0 + ell * np.asarray(R))
        if (lo <= 0).any():
            return None
        def rad(m, d, j):
            e = m / 2; coef = 1.0
            for t in range(d):
                coef *= 2 * (e - t)
            ee = e - d
            return abs(coef) * (hi[j] ** ee if ee >= 0 else lo[j] ** ee)
        K1, K2 = np.meshgrid(np.abs(ks), np.abs(ks), indexing="ij")
        wgt = np.exp(TP * rhoH * (K1 + K2))
        import itertools
        idx3 = [ix for d in (1, 2, 3) for ix in itertools.product(range(4), repeat=d)]
        for (m1, m2), C in self.form.items():
            base = np.abs(C) * wgt * pre
            Sm = {(n1, n2): float((base * K1 ** n1 * K2 ** n2).sum()) for n1 in range(4) for n2 in range(4 - n1)}
            for ix in idx3:
                cnt = [ix.count(i) for i in range(4)]
                f = Sm[(cnt[0], cnt[1])] * rad(m1, cnt[2], 0) * rad(m2, cnt[3], 1)
                for i in ix:
                    f *= sc[i]
                if len(ix) == 1:
                    G1[ix[0]] += f
                elif len(ix) == 2:
                    G2[ix[0], ix[1]] += f
                else:
                    G3[ix[0], ix[1], ix[2]] += f
        perm = [2, 3, 0, 1]                                     # X_i = +-d_{perm i} h
        dH = G1.sum(); XH = G1.max()
        DXH = max(G2[perm[i]].sum() for i in range(4))
        D2XH = max(G3[perm[i]].sum() for i in range(4))
        D2H = G2.sum()
        parts = dict(dH=dH, XH=XH, DXH=DXH, D2XH=D2XH, D2H=D2H)
        return max(parts.values()), parts

    # ---------------------------------------------------------------- truncation: digits, support, error
    def truncation(self, rho, c, ell, DXH, Ls=range(2, 14), nsect=36):
        """Kept set at L digits: measured for L <= 13; S(L) beyond from per-direction decay rates (sectors of the
        k-plane, upper envelope of log10 of the weighted amplitude against |k|_2, area 1/2 R^2 dalpha); e(L)
        log-linear."""
        w = np.exp(TP * rho * (np.abs(self.k1) + np.abs(self.k2)))
        comps = [self.U[..., 0] / TP, self.U[..., 1] / TP, self.V[..., 0] / ell, self.V[..., 1] / ell]
        A = np.max([np.abs(x) for x in comps], axis=0) * w
        ref = A.max()
        omt = c * self.om / TP
        kw = DXH + TP * np.abs(omt[0] * self.k1 + omt[1] * self.k2)
        tot = sum(np.abs(x) for x in comps) * w * kw
        rows = []
        for L in Ls:
            keep = A >= 10.0 ** (-L) * ref
            rows.append((L, int(keep.sum()), float(tot[~keep].sum())))
        Larr = np.array([r[0] for r in rows], float)
        e = np.array([r[2] for r in rows], float)
        oke = (e > 0) & (Larr >= 6)
        ce = np.polyfit(Larr[oke], np.log10(e[oke]), 1)
        # per-direction decay of log10(A/ref) against r = |k|_2 (unweighted size above 1e-13: clear of the floor)
        A0 = np.max([np.abs(x) / np.abs(x).max() for x in comps], axis=0)      # unweighted, per component
        nz = (A0 > 1e-13) & ((self.k1 != 0) | (self.k2 != 0))                  # well above the FFT floor
        r = np.hypot(self.k1, self.k2)[nz]; al = np.arctan2(self.k2, self.k1)[nz]
        lv = np.log10(A[nz] / ref)
        sect = []
        for j in range(nsect):
            lo_, hi_ = -np.pi + 2 * np.pi * j / nsect, -np.pi + 2 * np.pi * (j + 1) / nsect
            m = (al >= lo_) & (al < hi_)
            if m.sum() < 4:
                sect.append(None); continue
            rr, ll = r[m], lv[m]
            # upper envelope per unit radius bin, then a line through the envelope beyond r >= 4
            bins = np.floor(rr).astype(int)
            env = {}
            for bb, x in zip(bins, ll):
                env[bb] = max(env.get(bb, -99), x)
            xs = np.array(sorted(k for k in env if k >= 4)); ys = np.array([env[k] for k in xs])
            if len(xs) < 3:
                sect.append(None); continue
            sl, ic = np.polyfit(xs, ys, 1)
            sect.append((sl, ic))
        good = [x for x in sect if x is not None and x[0] < 0]
        sl_min = max(x[0] for x in good)                          # slowest decay (least negative slope)
        def S_of(L):
            area = 0.0
            for x in sect:
                sl, ic = x if (x is not None and x[0] < 0) else (sl_min, 0.0)
                R = max(0.0, (L + ic) / (-sl))
                area += 0.5 * R * R * (2 * np.pi / nsect)
            return area / 2                                         # only k1 + k2 even occurs (LG00's class P)
        return dict(rows=rows, loge_fit=ce.tolist(), ref=float(ref), S_of=S_of,
                    slopes=[(None if x is None else x[0]) for x in sect], slowest=sl_min,
                    S_check=[(L, n, S_of(L)) for L, n, _ in rows[-4:]])


def gamma_tilde(om_t):
    return GAMMA_DIR * abs(om_t[1])


def thresholds(geo, tor, Mp, rho, mu, c, ell, om_t, s1=1e-6, which=("v0", "v0fixed", "v1", "v1fixed", "A", "Aiso")):
    M, parts = Mp
    gam = gamma_tilde(om_t)
    s = 1 + s1
    nrm = float(np.abs(om_t).max())
    rhoinf = rho * 1e-3
    pk = dict(M=M, sK=geo["sK"] * 1.01 + mu, sB=geo["sB"] * 1.01 + mu, nu=s1 * nrm * (1 - 1e-9) / s, mu=mu)
    out = {}
    base = dict(n=2, tau=1, mu=q(mu), rho=q(rho), rhoinf=q(rhoinf), gbar=q(gam))
    def lg(k):
        C1n = max(k["gbar"] ** 4, k["c_star"] / k["delta0"] ** int(2 * k["a"]))
        return 4 * math.log10(gam) - math.log10(float(C1n))
    for t in which:
        if t in ("v0", "v1"):
            sT = tor["tinv_iso"] * 1.0005 + mu
        else:
            sT = tor["tinv_fixed"] * 1.0005 + mu
        args = dict(M=q(M), sK=q(pk["sK"]), sB=q(pk["sB"]), sT=q(sT))
        try:
            if t == "v0":
                out[t] = lg(TH.current_iso(nu=q(pk["nu"]), **args, **base))
            elif t == "v0fixed":
                out[t] = lg(TH.current_fixed(**args, **base))
            elif t in ("v1", "v1fixed"):
                cR = TH.cohConstR_lean(2, 1)
                out[t] = lg(TH.sharp(kappa=1, cR=cR, nu=q(pk["nu"]), iso=(t == "v1"), **args, **base))
            elif t in ("A", "Aiso", "Afreq", "Aisofreq"):
                iso = t.startswith("Aiso")
                D = dict(n=2, tau=1, kappa=1, rho=q(rho), rhoinf=q(rhoinf), gamma=q(gam), gbar=q(gam), mu=q(mu),
                         nu=q(pk["nu"]), M=q(M), sK=q(pk["sK"]), sB=q(pk["sB"]), sT=q(sT),
                         M0=q(parts["XH"]), M1=q(parts["DXH"]), M2=q(parts["D2XH"]), Mh1=q(parts["dH"]),
                         Mh2=q(parts["D2H"]), sLt=q(geo["Lt"] * 1.01 + mu), sN=q(geo["N"] * 1.01 + mu),
                         sNt=q(geo["Nt"] * 1.01 + mu), Tsup=q(tor["Tsup"] * 1.01),
                         omega_star=tuple(float(x) for x in om_t / s))
                D["Theta_omega"] = q(2.0) * q(nrm)
                for k_, b in (("B", D["sB"]), ("Tinv", D["sT"]), ("Lt", D["sLt"]), ("N", D["sN"]), ("Nt", D["sNt"]),
                              ("Tsup", D["Tsup"])):
                    D["bud_" + k_] = b / 10
                Dv = T2.with_caps(D, F(1, 20))
                st, ct = T2.c_stages(Dv, "freq" if t.endswith("freq") else "classical")
                out[t] = RA.threshold(RA.num_from(Dv, st, ct, iso=iso))
        except Exception as ex:                                   # noqa: BLE001  (record, continue)
            out[t] = float("nan")
            out[t + "_err"] = repr(ex)[:200]
    return out


_GEO, _TOR = {}, {}


def evaluate(O, rho, mu, c, ell, which, log=None):
    if (rho, ell) not in _GEO:
        _GEO[(rho, ell)] = O.geometry(rho, ell)
    if (c, ell) not in _TOR:
        _TOR[(c, ell)] = O.torsion(c, ell)
    geo, tor = _GEO[(rho, ell)], _TOR[(c, ell)]
    rhoH = rho + geo["iota"] + mu
    R = [geo["vdev"] + mu] * 2
    Mp = O.majorant(c, ell, rhoH, R)
    if Mp is None:
        return None
    omt = c * O.om / TP
    th = thresholds(geo, tor, Mp, rho, mu, c, ell, omt, which=which)
    tr = O.truncation(rho, c, ell, Mp[1]["DXH"])
    return dict(rho=rho, mu=mu, c=c, ell=ell, geo=geo, tinv_fixed=tor["tinv_fixed"], tinv_iso=tor["tinv_iso"],
                Tsup=tor["Tsup"], M=Mp[0], parts=Mp[1], th=th, trunc=tr, gamma=gamma_tilde(omt))


def digits_needed(res, theorem, head=1.0):
    """L with e(L) <= T 10^-head from the log-linear fit, and S(L) from the quadratic fit."""
    T = res["th"].get(theorem)
    if T is None or not np.isfinite(T):
        return None
    a, b = res["trunc"]["loge_fit"]
    L = (T - head - b) / a
    S = float(res["trunc"]["S_of"](L))
    return L, S


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--torus", default=os.path.join(HERE, "results", "lg00_torus_N128.npz"))
    ap.add_argument("--json")
    ap.add_argument("--quick", action="store_true")
    ap.add_argument("--which", default="v0,v0fixed,v1,v1fixed,A,Aiso")
    ap.add_argument("--gamma-dir", type=float, default=None,
                    help="Diophantine constant of the direction (default: Gamma', 0.2251)")
    a = ap.parse_args()
    if a.gamma_dir is not None:
        global GAMMA_DIR
        GAMMA_DIR = a.gamma_dir
    O = Oracle(a.torus)
    which = tuple(a.which.split(","))
    rhos = (0.005, 0.01, 0.02) if a.quick else (0.002, 0.005, 0.01, 0.02, 0.04)
    cs = (1e4, 1e5) if a.quick else (1e2, 1e3, 1e4, 1e5, 1e6, 1e7)
    ells = (1e-5, 1e-4) if a.quick else (1e-5, 1e-4, 1e-3)
    mus = (1e-4, 1e-3) if a.quick else (1e-5, 1e-4, 1e-3, 1e-2)
    allres = []
    for rho in rhos:
        for c in cs:
            for ell in ells:
                for mu in mus:
                    r = evaluate(O, rho, mu, c, ell, which)
                    if r is not None:
                        allres.append(r)
    # local refinement per theorem: coordinate steps x 3^{+-1/2} (rho, mu, c, ell) while S(L) decreases
    def score(r, t):
        x = digits_needed(r, t) if r is not None else None
        return math.inf if x is None else x[1]
    for t in which:
        cand = [r for r in allres if digits_needed(r, t) is not None]
        if not cand:
            continue
        cur = min(cand, key=lambda r: score(r, t))
        p = dict(rho=cur["rho"], mu=cur["mu"], c=cur["c"], ell=cur["ell"])
        best_s = score(cur, t)
        improved = True
        while improved:
            improved = False
            for key in ("rho", "mu", "c", "ell"):
                for fac in (3 ** 0.5, 3 ** -0.5):
                    q_ = dict(p); q_[key] = p[key] * fac
                    r = evaluate(O, q_["rho"], q_["mu"], q_["c"], q_["ell"], (t,))
                    sc = score(r, t)
                    if sc < best_s * 0.995:
                        best_s, p, cur, improved = sc, q_, r, True
        cur_all = evaluate(O, p["rho"], p["mu"], p["c"], p["ell"], which)
        allres.append(cur_all)
    print("theorem | best margin log10(T/e(L)) is not the criterion: L needed and S(L) at the best (rho, mu, c, ell)")
    best = {}
    for t in which:
        cand = [(digits_needed(r, t), r) for r in allres]
        cand = [(x, r) for x, r in cand if x is not None]
        if not cand:
            continue
        (L, S), r = min(cand, key=lambda z: z[0][1])
        best[t] = dict(L=L, S=S, T=r["th"][t], rho=r["rho"], mu=r["mu"], c=r["c"], ell=r["ell"], M=r["M"],
                       sK=r["geo"]["sK"], sB=r["geo"]["sB"], tinv_iso=r["tinv_iso"], tinv_fixed=r["tinv_fixed"],
                       gamma=r["gamma"], loge_fit=r["trunc"]["loge_fit"], slowest=r["trunc"]["slowest"],
                       S_check=r["trunc"]["S_check"], th_all=r["th"], parts=r["parts"])
        print("%-9s T 1e%.2f  L %.1f  S %.3g  | rho %.3f mu %.0e c %.0e ell %.0e  M %.3g sK %.4f sB %.4f "
              "tinv(iso %.3g fixed %.3g) gamma %.3g" % (t, r["th"][t], L, S, r["rho"], r["mu"], r["c"], r["ell"], r["M"],
                                                       r["geo"]["sK"], r["geo"]["sB"], r["tinv_iso"],
                                                       r["tinv_fixed"], r["gamma"]))
    # frequency-specific route A at the best route-A points
    for t, tf in (("A", "Afreq"), ("Aiso", "Aisofreq")):
        if t not in best or a.which != "v0,v0fixed,v1,v1fixed,A,Aiso":
            continue
        b = best[t]
        r = evaluate(O, b["rho"], b["mu"], b["c"], b["ell"], (tf,))
        L, S = digits_needed(r, tf)
        best[tf] = dict(b, L=L, S=S, T=r["th"][tf])
        print("%-9s T 1e%.2f  L %.1f  S %.3g  (at the %s point)" % (tf, r["th"][tf], L, S, t))
    if a.json:
        for b in best.values():
            b.pop("S_check", None)
        json.dump(dict(best=best, n=len(allres)), open(a.json, "w"), indent=1, default=float)


if __name__ == "__main__":
    main()
