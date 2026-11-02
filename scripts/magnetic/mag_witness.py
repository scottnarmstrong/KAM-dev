#!/usr/bin/env python3
"""MAG-2b: the routeARefined witness of the magnetic torus from exact mirrors (untrusted tooling); the analogue of
scripts/spin_orbit/sodata3_witness.py with CLASSICAL sites only (no certified bites).

    SO_CLIENT=sofx_mag SO_DATA_DIR=... SO_PREC=128 python3 mag_witness.py GENDIR OUT.json

The refined claim R (Ham sums of hamClaimOk, frame row maxima of checkFrameMajorants) is computed exactly
(sodata3_v2checks) and rounded UP to 4 significant digits, then re-checked; X* = 2 err/(γ⁴ δ₀⁴) rounded up, the caps
of v2_r2.okB_at, disp the exact minimum C err/(γ² ρ²) rounded UP to 3 digits; refinedCore exact.
"""
import json
import os
import sys
from fractions import Fraction as F

sys.set_int_max_str_digits(0)
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "spin_orbit"))
import sodata3_witness as W    # noqa: E402  (claims, load, up_sig; its BITES are lunar and unused here)
import v2_r2 as D              # noqa: E402
import v2_q as V               # noqa: E402
import sofx_mag as SM          # noqa: E402

KP, TH, J = 3, F(1, 8), 20


def witness(which, c, d):
    p = dict(SM.magParams(0, 0), kappa=SM.KAPPA)
    box = [(F(a), F(b)) for a, b in d["freqBox"]]
    assert box[1] == (p["kappa"], 0), "clock coordinate must be exactly (kappa, 0)"
    err = F(d["params"]["err"])
    R, bOm, okH, okF, parts, exact = W.claims(c)
    d0 = min(F(1), (p["rho"] - p["rhoInf"]) / 6)
    st = {}
    for s in range(KP):
        st[("d", s)] = V.classical_c(2, 1, J, F(1, 2) ** s * d0)
        st[("b", s)] = V.classical_c(2, 1, J, min(p["rho"] - 6 * d0 * (1 - F(1, 2) ** s), F(1)))
    sc = p["gamma"] ** 4 * d0 ** 4
    g2 = p["gamma"] ** 2 * p["rho"] ** 2
    Xs = V.up(float(2 * err / sc), 3)
    ok, why, w = D.okB_at("refined", p, box, KP, TH, J, Xs, R, st, detail=True)
    Q = V.refined_num(w, 2, p, box)
    C = V.disp_coefs(Q, 2, p, Xs, False)[0]
    disp = V.up(float(C * err / g2) * (1 + 1e-9), 3)
    while C * err > disp * g2:
        disp = V.up(float(disp) * 1.001, 3)
    dj = F(d["params"]["disp"])        # the certificate's disp (sofx_gen, SO_DISP_COEF): kept when admissible
    if C * err <= dj * g2:
        disp = dj
    pe = dict(p, err=err, disp=disp)
    fin = V.refinedCore(2, pe, box, dict(w), detail=True)
    Xmax = D.max_Xs("refined", p, box, KP, TH, J, R, st, lo=-30, hi=15, steps=26)
    return dict(which=which, err=str(err), disp=str(disp), disp_min=str(C * err / g2), Xs=str(Xs),
                log10_err_over_thr=D.lg(err / (Xmax * sc)), log10_thr=D.lg(Xmax * sc), okB=ok, why=why,
                refinedCore=fin, hamClaim=okH, frameMajorants=okF, frame_parts=parts, bOm=str(bOm),
                exact=exact, bites={},
                witness=dict(kp=KP, th=str(TH), J=J, Xs=str(Xs), c=[str(w["c"][s]) for s in range(KP)],
                             cbar=[str(w["cbar"][s]) for s in range(KP)], ctail=str(w["ctail"]), sB=str(w["sB"]),
                             sT=str(w["sT"]), sLt=str(w["sLt"]), sN=str(w["sN"]), sNt=str(w["sNt"]),
                             t=str(w["t"]), R={k: str(v) for k, v in R.items()}, kappa=str(p["kappa"])))


if __name__ == "__main__":
    gdir, outp = sys.argv[1], sys.argv[2]
    c, d = W.load(gdir, "mag")
    o = witness("mag", c, d)
    print("err", o["err"], "disp", o["disp"], "err/thr 10^%.2f" % o["log10_err_over_thr"], "okB", o["okB"],
          "ham", o["hamClaim"], "frame", o["frameMajorants"], o["frame_parts"], "refinedCore", o["refinedCore"],
          "R", o["witness"]["R"], flush=True)
    json.dump([o], open(outp, "w"), indent=1, default=str)
