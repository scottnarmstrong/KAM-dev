#!/usr/bin/env python3
"""SO-V2PKG: v2 thresholds at N = 65 (R2), 80, 100, by site configuration, with the exact final test.

    python3 v2_sketch.py OUT.json

Packages: N = 65 is lunarR2 exactly.  N = 80, 100 keep R2's c, rho, rhoInf, mu, nu, s, sigma_omega, M, sigma_T and
take gamma = kappa/(N + 2), sigma_K = ||DK|| + mu, sigma_B = ||G^-1|| (l1, checkGram form) + mu from the SO-GEN3
emit logs (kam-data/so-gen3/g3/N<N>/emit_rot_lower.log, enclosed on the L = 32 / 26 models).  The refined claims:
frame sums from v2_frame.py (sampled x 1.01), Ham sums scaled from the N = 65 sofx forms (x 1.01).  Untrusted
tooling; the N = 80, 100 rows are a sketch (majorants not re-enclosed at the v2 truncation).

Site configurations (kp = 3 unless named; each certified site is one balanced small-divisor bite in the kernel):
  all      every delta_s and b_s certified (largest bite l = 13 at rho = 1/140)
  d01b     delta_0, delta_1 and every b_s certified, delta_2 classical (largest bite l = 12)
  d0b      delta_0 and every b_s certified (largest bite l = 11)
  kp2      kp = 2, all certified (largest bite l = 12)
  classical every site classical (no bite)
"""
import sys, os, json, math
from fractions import Fraction as F
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import v2_r2 as D   # noqa: E402
import v2_q as V    # noqa: E402

PKG = {
    65: dict(sK=F(1873, 1000), sB=F(2689, 500)),
    80: dict(sK=F(2283, 1000), sB=F(1207, 100)),
    100: dict(sK=F(2881, 1000), sB=F(4056, 100)),
}
CLAIM = {
    65: D.R65["lower"],
    80: dict(dh=F(2099, 1000), dx=F(2020, 1000), d2x=F(1536, 1000), d2h=F(2143, 1000),
             bL=F(2203, 1000), bN=F(3346, 1000), bNt=F(3407, 1000), bT=F(22916, 1000)),
    100: dict(dh=F(2100, 1000), dx=F(2020, 1000), d2x=F(1577, 1000), d2h=F(2145, 1000),
              bL=F(2740, 1000), bN=F(6063, 1000), bNt=F(6188, 1000), bT=F(75215, 1000)),
}
CONFIGS = {"all": (3, None), "d01b": (3, {("d", 2)}), "d0b": (3, {("d", 1), ("d", 2)}), "kp2": (2, None),
           "classical": (3, "all")}


def sites_for(p, which, kp, classical):
    d0 = min(F(1), (p["rho"] - p["rhoInf"]) / 6)
    st = D.site_constants(p, which, kp)
    for s in range(kp):
        for tag, b in (("d", F(1, 2) ** s * d0), ("b", min(p["rho"] - 6 * d0 * (1 - F(1, 2) ** s), F(1)))):
            if classical == "all" or (classical and (tag, s) in classical):
                st[(tag, s)] = V.classical_c(2, 1, 20, b)
    return st


def run(N, which="lower", configs=CONFIGS, th=F(1, 8), J=20):
    p = D.package(N, sK=PKG[N]["sK"], sB=PKG[N]["sB"])
    box = D.box_of(p, which)
    R = CLAIM[N]
    d0 = min(F(1), (p["rho"] - p["rhoInf"]) / 6)
    sc = p["gamma"] ** 4 * d0 ** 4
    g2 = p["gamma"] ** 2 * p["rho"] ** 2
    import sharp_q as SQ
    out = dict(N=N, sharp=D.lg(SQ.sharp(p)["threshold"]))
    Xf = D.max_Xs("frozen", p, box, 5, th, J)
    out["frozen"] = D.lg(Xf * sc)
    for name, (kp, cl) in configs.items():
        st = sites_for(p, which, kp, cl)
        X = D.max_Xs("refined", p, box, kp, th, J, R, st, lo=-30, hi=15, steps=28)
        ok, why, w = D.okB_at("refined", p, box, kp, th, J, X, R, st, detail=True)
        Q = V.refined_num(w, 2, p, box)
        C = V.disp_coefs(Q, 2, p, X, False)[0]
        e = X * sc
        pe = dict(p, err=V.up(float(e) * 0.999, 6))
        pe["disp"] = V.up(float(C * pe["err"] / g2) * 1.001, 3)
        fin = V.refinedCore(2, pe, box, dict(w), detail=True)
        _, why_up, _ = D.okB_at("refined", p, box, kp, th, J, X * F(11, 10), R, st, detail=True)
        out[name] = dict(kp=kp, Xs=str(X), log10_thr=D.lg(e), log10_disp_coef=D.lg(C / g2), exact_pass=fin[0],
                         binding=why_up, sites={"%s%d" % k: float(v) for k, v in st.items()},
                         caps={k: float(w[k]) for k in ("sB", "sT", "sLt", "sN", "sNt", "t")},
                         ctail=float(w["ctail"]))
        print(N, name, round(D.lg(e), 3), "disp coef 10^%.2f" % D.lg(C / g2), fin[0], why_up, flush=True)
    return out


if __name__ == "__main__":
    res = [run(N) for N in (65, 80, 100)]
    json.dump(res, open(sys.argv[1], "w"), indent=1, default=str)
