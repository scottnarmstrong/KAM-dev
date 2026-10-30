#!/usr/bin/env python3
"""SO-DATA3: the routeARefined witness of the N = 65 tori, from exact mirrors (untrusted tooling).

    python3 sodata3_witness.py GENDIR OUT.json

GENDIR holds sofx_gen's <which>_cert.json / <which>_advice.json (sodata3_gen.sh).  For each torus:
  * the refined claim R: the four Ham sums of hamClaimOk and the frame row maxima of checkFrameMajorants are
    computed exactly (sodata3_v2checks), rounded UP to 4 significant digits, and re-checked by the verdict
    functions;
  * the certified sites (d01b: delta_0, delta_1, b_0, b_1, b_2): the bite witness (E1, l, J = 8, B) with B the
    exact balBound of the Lean checker rounded up (BITES below, from `#eval` of `balBound`, sodata3 Lean probes),
    and c the smallest 4-digit decimal with B kappa^-2 (gamma b)^2 <= (3.1415 c)^2; delta_2 and the tail classical;
  * X*, the caps (v2_r2.okB_at, tight caps), disp = the exact minimum rounded UP to 3 digits; refinedCore exact.
"""
import json
import os
import sys
from fractions import Fraction as F

sys.set_int_max_str_digits(0)
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import sofx_negative as NG      # noqa: E402
import sofx_packed as PK        # noqa: E402
import sodata3_v2checks as VC   # noqa: E402
import v2_r2 as D               # noqa: E402
import v2_q as V                # noqa: E402

KP, TH, J = 3, F(1, 8), 20
# (tag, s) -> (l, E1, balBound rounded up to 1e-3); E1 = 1/expLow (J = 8) rounded up to 6 decimals.  Both boxes
# give the same values at this resolution (Lean #eval on the data boxes of g1, both tori).
BITES = {("d", 0): (11, F(492587, 500000), F(108441309, 1000)),
         ("d", 1): (12, F(12407, 12500), F(422706841, 1000)),
         ("b", 0): (8, F(914193, 1000000), F(11913318, 1000)),
         ("b", 1): (9, F(239023, 250000), F(18325573, 1000)),
         ("b", 2): (10, F(244439, 250000), F(50668688, 1000))}


def up_sig(x, sig):
    """the smallest decimal with `sig` significant digits that is >= x (exact)."""
    x = F(x)
    e = 0
    while F(10) ** (e + sig) <= x:
        e += 1
    while F(10) ** (e + sig - 1) > x:
        e -= 1
    q = F(10) ** e
    m = -((-x) // q)
    return m * q


def site_c(p, b, B):
    """the smallest 4-digit decimal c with B kappa^-2 (gamma b)^2 <= (3.1415 c)^2 (biteOk's last test)."""
    lhs = B / p["kappa"] ** 2 * (p["gamma"] * b) ** 2
    ok = lambda c: lhs <= (F(31415, 10000) * c) ** 2
    c = up_sig(F(float(lhs) ** 0.5 / 3.1415) * F(999, 1000), 4)
    while not ok(c):
        c = up_sig(c + c / 10 ** 4, 4)
    return c


def sites(p):
    d0 = min(F(1), (p["rho"] - p["rhoInf"]) / 6)
    st = {}
    for s in range(KP):
        for tag, b in (("d", F(1, 2) ** s * d0), ("b", min(p["rho"] - 6 * d0 * (1 - F(1, 2) ** s), F(1)))):
            if (tag, s) in BITES:
                st[(tag, s)] = site_c(p, b, BITES[(tag, s)][2])
            else:
                st[(tag, s)] = V.classical_c(2, 1, J, b)
    return st


def load(gdir, which):
    d = json.load(open(os.path.join(gdir, "%s_cert.json" % which)))
    books = NG.load_books(os.path.join(gdir, "%s_advice.json" % which))
    c = NG.cert(which, d, books, PK.PackedEngine({}))
    return c, d


def claims(c):
    hv = VC.ham_values(c)
    rows = VC.frame_rows(c.B, c)
    fv = VC.frame_values(c.B, c, rows)
    R = {k: up_sig(hv[k], 4) for k in ("dh", "dx", "d2x", "d2h")}
    R.update(bL=up_sig(max(fv["L"]), 4), bN=up_sig(max(fv["N"]), 4), bNt=up_sig(max(fv["Nt"]), 4),
             bT=up_sig(max(fv["T"]), 4))
    bOm = up_sig(fv["Om"][0], 8)
    okH = VC.checkHamClaim(c, R, hv)
    okF, parts = VC.checkFrameMajorants(c.B, c, dict(R, bOm=bOm), rows)
    exact = dict(ham={k: str(v) for k, v in hv.items()}, frame={k: [str(x) for x in v] for k, v in fv.items()})
    return R, bOm, okH, okF, parts, exact


def witness(which, c, d):
    p = D.package(65)
    box = [(F(a), F(b)) for a, b in d["freqBox"]]      # the certificate's own box (the kernel reads this one)
    assert box[1] == (p["kappa"], 0), "clock coordinate must be exactly (kappa, 0)"
    err = F(d["params"]["err"])
    R, bOm, okH, okF, parts, exact = claims(c)
    st = sites(p)
    d0 = min(F(1), (p["rho"] - p["rhoInf"]) / 6)
    sc = p["gamma"] ** 4 * d0 ** 4
    g2 = p["gamma"] ** 2 * p["rho"] ** 2
    Xs = V.up(float(2 * err / sc), 3)
    ok, why, w = D.okB_at("refined", p, box, KP, TH, J, Xs, R, st, detail=True)
    Q = V.refined_num(w, 2, p, box)
    C = V.disp_coefs(Q, 2, p, Xs, False)[0]
    disp = V.up(float(C * err / g2) * (1 + 1e-9), 3)
    while C * err > disp * g2:                       # never rounded down
        disp = V.up(float(disp) * 1.001, 3)
    pe = dict(p, err=err, disp=disp)
    fin = V.refinedCore(2, pe, box, dict(w), detail=True)
    Xmax = D.max_Xs("refined", p, box, KP, TH, J, R, st, lo=-30, hi=15, steps=26)
    bites = {"%s%d" % k: dict(l=v[0], E1=str(v[1]), J=8, B=str(v[2])) for k, v in BITES.items()}
    return dict(which=which, err=str(err), disp=str(disp), disp_min=str(C * err / g2), Xs=str(Xs),
                log10_err_over_thr=D.lg(err / (Xmax * sc)), log10_thr=D.lg(Xmax * sc), okB=ok,
                refinedCore=fin, hamClaim=okH, frameMajorants=okF, frame_parts=parts, bOm=str(bOm),
                exact=exact, bites=bites,
                witness=dict(kp=KP, th=str(TH), J=J, Xs=str(Xs), c=[str(w["c"][s]) for s in range(KP)],
                             cbar=[str(w["cbar"][s]) for s in range(KP)], ctail=str(w["ctail"]), sB=str(w["sB"]),
                             sT=str(w["sT"]), sLt=str(w["sLt"]), sN=str(w["sN"]), sNt=str(w["sNt"]),
                             t=str(w["t"]), R={k: str(v) for k, v in R.items()}, kappa=str(p["kappa"])))


if __name__ == "__main__":
    gdir, outp = sys.argv[1], sys.argv[2]
    out = []
    for which in ("lower", "upper"):
        c, d = load(gdir, which)
        o = witness(which, c, d)
        print(which, "err", o["err"], "disp", o["disp"], "err/thr 10^%.2f" % o["log10_err_over_thr"],
              "ham", o["hamClaim"], "frame", o["frameMajorants"], o["frame_parts"], "refinedCore", o["refinedCore"],
              "R", o["witness"]["R"], flush=True)
        out.append(o)
    json.dump(out, open(outp, "w"), indent=1, default=str)
