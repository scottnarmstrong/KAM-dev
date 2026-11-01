#!/usr/bin/env python3
"""MAG-PILOT: v2 route thresholds for the eps = 3/2500 magnetic torus (untrusted design tooling, sampled bounds).

    python3 -B mag_threshold.py DOUBLE_NPZ [--n 256] [--rho 3/1000 ...]

Builds the 4-component embedding K = (theta1 + u, theta2, p, J), J = -(h(p) + V(q, phi)) (energy zero), of the
mag_producer double solution, samples on the four corners of the distinguished boundary of the strip (and the
mu-ball, mu = 1/500, at two corners) with scripts/apps_scout/kamlib.py: the package majorants M, sK, sB, sT
(kamlib.package, slack 1.05) and the RefClaim sums dh, dx, d2x, d2h, bL, bN, bNt, bT (v2_frame.py conventions,
x 1.01).  Parameters as plan-magnetic-barrier §3.3: s0 = 500001/500000, omega* = (alpha, 1)/s0, som = 2,
nu = 1e-6, gamma = (1/10)/s0, tau = 1, rhoInf = rho/1000.  Thresholds from scripts/certifier/route_select.py
`thresholds` (exact mirrors at these sampled inputs; not certified enclosures).
"""
import os, sys, json, math, argparse
from fractions import Fraction as F
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "apps_scout"))
sys.path.insert(0, os.path.join(HERE, "..", "certifier"))
import kamlib as kl          # noqa: E402
import models as md          # noqa: E402
import route_select as RS    # noqa: E402
import mag_producer as MP    # noqa: E402

TP = 2 * math.pi
S0 = F(500001, 500000)
MU = F(1, 500)


def ham(eps):
    c1, c2, ka = float(MP.C1), float(MP.C2), float(MP.KAPPA)
    def H(z):
        q, ph, p, J = z
        h = p - (p * p) * 0.75 + (p * p * p) * (1 / 3) - (p * p * p * p) * (1 / 16)
        Ca = md.jcos(TP * (2 * q - ph)); Cb = md.jcos(TP * (3 * q - 2 * ph))
        A = Ca * c1 - Cb * c2
        return J + h + (Ca + Cb) * eps + (A * A) * (ka * eps * eps)
    return H


def torus(uh, n):
    g0 = MP.Grid(*uh.shape)
    u, ut, p = g0.state(uh)
    eps = float(MP.EPS)
    a = TP * (2 * (g0.th + u) - g0.ph); b = TP * (3 * (g0.th + u) - 2 * g0.ph)
    A = float(MP.C1) * np.cos(a) - float(MP.C2) * np.cos(b)
    V = eps * (np.cos(a) + np.cos(b)) + float(MP.KAPPA) * eps * eps * A * A
    J = -(p - 0.75 * p ** 2 + p ** 3 / 3 - p ** 4 / 16 + V)
    gb = kl.Grid(*uh.shape, frac=1.0)
    tb = kl.Torus(gb, None, np.array([u, 0 * u]), np.array([p, J]))
    return tb.resample(kl.Grid(n, n, frac=1.0)) if n != uh.shape[0] else tb


def frame_sums(H, tor, rho, om):
    """bL, bN, bNt, bT sampled on the four strip corners (v2_frame.py conventions)."""
    g = tor.g
    best = dict(bL=0.0, bN=0.0, bNt=0.0, bT=0.0)
    arrs = [tor.u[0], tor.u[1], tor.y[0], tor.y[1]]
    for sg in kl.SIGNS:
        wgt = np.exp(-TP * rho * (sg[0] * g.k1 + sg[1] * g.k2)) * g.mask
        z = [g.t1 + 1j * rho * sg[0] + g.strip(tor.u[0], rho, sg), g.t2 + 1j * rho * sg[1] + g.strip(tor.u[1], rho, sg),
             g.strip(tor.y[0], rho, sg), g.strip(tor.y[1], rho, sg)]
        L = np.zeros((4, 2, g.N1, g.N2), dtype=complex)
        for i in range(4):
            for j in range(2):
                k = g.k1 if j == 0 else g.k2
                L[i, j] = g.i(g.f(arrs[i]) * (2j * np.pi * k) * wgt)
        L[0, 0] += 1; L[1, 1] += 1
        _, he = kl.derivs(H, z, 2)
        DX = np.einsum("ij,jk...->ik...", kl.Ja, he)
        B = kl.inv2(kl.mm(kl.tr(L), L))
        N = np.einsum("ij,jk...->ik...", kl.Ja, kl.mm(L, B))
        lam = 2j * np.pi * (g.k1 * om[0] + g.k2 * om[1])
        dN = np.array([[g.i(g.f(N[i, j]) * lam) for j in range(2)] for i in range(4)])
        T = -kl.mm(kl.tr(N), np.einsum("ij,jk...->ik...", kl.Om, kl.mm(DX, N) - dN))
        best["bL"] = max(best["bL"], float(np.abs(L).sum(axis=0).max()))
        best["bN"] = max(best["bN"], float(np.abs(N).sum(axis=1).max()))
        best["bNt"] = max(best["bNt"], float(np.abs(N).sum(axis=0).max()))
        best["bT"] = max(best["bT"], float(np.abs(T).sum(axis=1).max()))
    return best


def up(x, d=1000):
    return F(math.ceil(x * 1.01 * d), d)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("npz"); ap.add_argument("--n", type=int, default=256)
    ap.add_argument("--rho", nargs="*", default=["3/1000"])
    ap.add_argument("--json", default=None)
    a = ap.parse_args()
    uh = np.load(a.npz)["uh"]
    H = ham(float(MP.EPS))
    tor = torus(uh, a.n)
    alpha = MP.ALPHA
    om_star = (alpha / float(S0), 1 / float(S0))
    gam_num = kl.dio_gamma(om_star, kmax=4000)
    out = dict(eps=str(MP.EPS), alpha="(7913-sqrt5)/13618", s0=str(S0), mu=str(MU), dio_numeric=gam_num[0],
               dio_argmin=gam_num[1], rho={})
    for rs in a.rho:
        rho = F(rs)
        sd = kl.strip_data(H, tor, float(rho), float(MU))
        pk = kl.package(sd, H, tor, om_star, float(S0), mu=float(MU))
        raw = pk["raw"]
        fs = frame_sums(H, tor, float(rho), (alpha, 1.0))
        R = dict(dh=up(raw["DH"]), dx=up(raw["DX"]), d2x=up(raw["D2X"]), d2h=up(raw["D2H"]),
                 bL=up(fs["bL"]), bN=up(fs["bN"]), bNt=up(fs["bNt"]), bT=up(fs["bT"]))
        gamma = F(1, 10) / S0
        params = dict(tau=1, rho=rho, rhoInf=rho / 1000, M=up(pk["M"]), sK=up(pk["sK"]), sB=up(pk["sB"]),
                      sT=up(pk["sT"]), mu=MU, gbar=gamma, som=F(2), nu=F(1, 10 ** 6), gamma=gamma, s=S0,
                      err=F(0), E0=F(0), disp=F(0))
        box = [(F(alpha).limit_denominator(10 ** 15) / S0, F(1, 10 ** 12)), (1 / S0, F(0))]
        prof = dict(name="magnetic", params=params, box=box, R=R, rho_fixed=True, site_l_rule=dict(delta="2.4", b="1.8"),
                    site_l_max=12, remeasured=None, A_meas=None)
        print("rho %s: M %s sK %s sB %s sT %s R %s" % (rs, params["M"], params["sK"], params["sB"], params["sT"],
                                                      {k: str(v) for k, v in R.items()}), flush=True)
        th = RS.thresholds(prof, rs, with_B=True)
        out["rho"][rs] = dict(params={k: str(v) for k, v in params.items()}, R={k: str(v) for k, v in R.items()},
                              raw={k: v for k, v in raw.items() if k != "Tavg"}, Tavg=raw["Tavg"],
                              thresholds={k: (dict(log10=RS.lg(v["estar"]), kind=v["kind"]) if "estar" in v
                                              else dict(error=v.get("error"))) for k, v in th.items()})
    if a.json:
        json.dump(out, open(a.json, "w"), indent=1)
    print(json.dumps({r: {k: v.get("log10", v.get("error")) for k, v in d["thresholds"].items()}
                      for r, d in out["rho"].items()}, indent=1))


if __name__ == "__main__":
    main()
