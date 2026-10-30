#!/usr/bin/env python3
"""SO-V2PKG: the recommended SO-DATA3 witness at N = 65 / lunarR2 and its exact refinedCore check.

    python3 v2_pkg65.py OUT.json [errL errU]

Configuration "d01b": routeARefined (witness Sum.inr (Sum.inr w)), kp = 3, th = 1/8, J = 20, certified sites
delta_0, delta_1, b_0, b_1, b_2 (float c_freq x 1.01: the kernel witness must be re-derived with the balanced
checker, scripts/certifier/smalldiv.py / SHARP2-C6), delta_2 and the tail classical.  X* is the smallest 3-digit
value with err < X* gamma^4 delta0^4 times a factor 2 of room; caps tight (v2_r2.solve_caps); disp is the
exact minimum max(c2Q, c3Q) err/(gamma^2 rho^2) rounded UP to 3 digits.  Defaults: the err of the L = 20 sofx runs
(checker rows x 1.001, 3 digits).  Untrusted tooling.
"""
import sys, os, json
from fractions import Fraction as F
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import v2_r2 as D       # noqa: E402
import v2_q as V        # noqa: E402
import v2_sketch as S   # noqa: E402


def witness(which, err, kp=3, th=F(1, 8), J=20):
    p = D.package(65)
    box = D.box_of(p, which)
    R = D.R65[which]
    d0 = min(F(1), (p["rho"] - p["rhoInf"]) / 6)
    sc = p["gamma"] ** 4 * d0 ** 4
    g2 = p["gamma"] ** 2 * p["rho"] ** 2
    st = S.sites_for(p, which, kp, {("d", 2)})
    Xs = V.up(float(2 * err / sc), 3)
    ok, why, w = D.okB_at("refined", p, box, kp, th, J, Xs, R, st, detail=True)
    Q = V.refined_num(w, 2, p, box)
    C = V.disp_coefs(Q, 2, p, Xs, False)[0]
    disp = D.V.up(float(C * err / g2) * (1 + 1e-9), 3)
    while C * err > disp * g2:                       # never rounded down
        disp = V.up(float(disp) * 1.001, 3)
    pe = dict(p, err=err, disp=disp)
    fin = V.refinedCore(2, pe, box, dict(w), detail=True)
    Xmax = D.max_Xs("refined", p, box, kp, th, J, R, st, lo=-30, hi=15, steps=26)
    return dict(which=which, err=str(err), disp=str(disp), disp_float=float(disp), Xs=str(Xs),
                log10_err_over_thr=D.lg(err / (Xmax * sc)), log10_thr=D.lg(Xmax * sc), okB=ok, refinedCore=fin,
                graph_limit_disp=float(F(1353683, 10 ** 7) * p["rhoInf"]),
                witness=dict(kp=kp, th=str(th), J=J, c=[str(x) for x in w["c"]], cbar=[str(x) for x in w["cbar"]],
                             ctail=str(w["ctail"]), sB=str(w["sB"]), sT=str(w["sT"]), sLt=str(w["sLt"]),
                             sN=str(w["sN"]), sNt=str(w["sNt"]), t=str(w["t"]), R={k: str(v) for k, v in R.items()},
                             kappa=str(p["kappa"])))


if __name__ == "__main__":
    errs = [F(sys.argv[2]), F(sys.argv[3])] if len(sys.argv) > 3 else [F(160, 10 ** 18), F(183, 10 ** 18)]
    out = [witness(w, e) for w, e in zip(("lower", "upper"), errs)]
    for o in out:
        print(o["which"], "err", o["err"], "disp", o["disp_float"], "err/thr 10^%.2f" % o["log10_err_over_thr"],
              "refinedCore", o["refinedCore"])
    json.dump(out, open(sys.argv[1], "w"), indent=1, default=str)
