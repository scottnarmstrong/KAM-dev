#!/usr/bin/env python3
"""V2-PUBLIC #3: named route and failure diagnostics of the forced-toy producer (untrusted tooling).

The producer tools call these only on a failure path, so a successful run prints exactly what it printed before.
Every line has the form

    FAIL route=<route> check=<check>: <the compared numbers>, <by how much>
    PASS route=<route> check=<check>: <the compared numbers>        (context, printed next to a failure)

with the route names of route_select.py (`landed-base` is the common part of every route of `routeV2All`:
`landedBase.check`, KAM/CertificateSharp/V2/Engine.lean) and the check names of the Lean checker or of its exact
mirror (sofx_check.py, sharp_q.py, v2_q.py, route_b_lean_mirror.py).  "By how much" is a margin (bound - value,
negative on failure) or, for a smallness test err < e*, log10(err / e*) decades.  Nothing here decides anything;
the kernel does.
"""
import math
import os
import sys
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(1, os.path.join(HERE, "..", "..", "spin_orbit"))
sys.path.insert(2, os.path.join(HERE, "..", "..", "apost_sharp"))

BASE = ("checkStatic", "checkHamBounds", "checkEmbedding", "checkInvariance", "checkEnergy", "checkGram",
        "checkTorsion")


def g(x):
    return "%.3g" % float(x)


def decades(a, b):
    """log10(a / b) for positive a, b (exact enough for a report)."""
    return math.log10(float(F(a))) - math.log10(float(F(b)))


def emit(lines, out=None):
    """print to stderr (after flushing stdout, so the tool's own lines come first in a combined log)."""
    out = out or sys.stderr
    sys.stdout.flush()
    for ln in lines:
        print(ln, file=out)
    out.flush()


# ---------------------------------------------------------------------------------------------- landed base
def base_lines(report):
    """the landed sub-checks of the mirror's report (forced_cert.generate), failing ones with their margins."""
    out = []
    checks = report.get("checks", {})
    for name in list(BASE) + sorted(k for k in checks if k not in BASE):
        v = checks.get(name)
        if v is None:
            continue
        info = v.get("info") or {}
        nums = []
        for k, x in info.items():
            if isinstance(x, (int, float, F)) and not isinstance(x, bool):
                nums.append("%s %s" % (k, g(x)))
            elif isinstance(x, bool) and not x:
                nums.append("%s false" % k)
        if not v["ok"] and "err" in info and "margin" in info:
            val = F(info["err"]) - F(info["margin"])
            if val > 0 and F(info["err"]) > 0:
                nums.append("value/err 10^%.2f" % decades(val, info["err"]))
        out.append("%s route=landed-base check=%s: %s" % ("PASS" if v["ok"] else "FAIL", name,
                                                          ", ".join(nums) or "no margin recorded"))
    return out


# ---------------------------------------------------------------------------------------------- the routes
def sharp_lines(p):
    """`sharpTest` (sharp_q.py, the mirror of KAM.CertificateSharp.sharpTest): smallness C1 err < γ⁴ρ^{4τ} and
    displacement max(C2, C3) err <= disp γ²ρ^{2τ}."""
    import sharp_q as SQ
    r = SQ.sharp(dict(p))
    tau, rho, gam = p["tau"], p["rho"], p["gamma"]
    out = []
    small = r["C1"] * p["err"] < gam ** 4 * rho ** (4 * tau)
    out.append("%s route=sharp check=sharpTest.smallness: err %s, threshold e* %s, log10(err/e*) %+.2f" % (
        "PASS" if small else "FAIL", g(p["err"]), g(r["threshold"]), decades(p["err"], r["threshold"])))
    need = r["disp_coef"] * p["err"]
    disp_ok = max(r["C2"], r["C3"]) * p["err"] <= p["disp"] * gam ** 2 * rho ** (2 * tau)
    out.append("%s route=sharp check=sharpTest.displacement: disp %s, needed %s (= %s err)" % (
        "PASS" if disp_ok else "FAIL", g(p["disp"]), g(need), g(r["disp_coef"])))
    return small and disp_ok, out


def frozenA_lines(c, kp=5, th=F(1, 8), J=20):
    """route A frozen as forced_witness.frozen_A chooses it: the largest X* passing okB, then `frozenCore`
    (v2_q.frozenCore: Xs, wf, okB, torsion, classical, final) at the certificate's numbers."""
    import v2_q as V
    import v2_r2 as R2
    p, box = dict(c.params), c.freqBox
    Xs = R2.max_Xs("frozen", p, box, kp, th, J, lo=-30.0, hi=8.0, steps=40)
    ok, why, w = R2.okB_at("frozen", p, box, kp, th, J, Xs, detail=True)
    if not ok:
        return False, ["FAIL route=A.frozen check=okB: no X* passes the run (binding: %s)" % ", ".join(
            map(str, why[:4]))]
    full, parts = V.frozenCore(2, p, box, w, detail=True)
    d0 = min(F(1), (p["rho"] - p["rhoInf"]) / 6)
    estar = Xs * p["gamma"] ** 4 * d0 ** 4
    bad = [k for k, v in parts.items() if not v]
    line = "%s route=A.frozen check=frozenCore%s: X* %s, err %s, threshold e* %s, log10(err/e*) %+.2f" % (
        "PASS" if full else "FAIL", "" if full else "." + "/".join(bad), g(Xs), g(p["err"]), g(estar),
        decades(p["err"], estar))
    return full, [line]


def frozenB_lines(c, B, frozen=True):
    """route B (forced_witness.route_B): B is its result, None when no X* passed `routeBOk`; the smallness
    clause of finalB is c1B err < γ⁴ρ⁴, i.e. err < e* = γ⁴ρ⁴ / c1B."""
    name = "B.frozen" if frozen else "B.refined"
    p = dict(c.params)
    if B is None:
        return False, ["FAIL route=%s check=routeBOk: no X* in [1e-30, 1e8] passes (the caps diverge or a "
                       "stage clause fails at every X*)" % name]
    ok = p["err"] < B["estar"]
    return ok, ["%s route=%s check=finalB.smallness: X* %s, err %s, threshold e* %s, log10(err/e*) %+.2f" % (
        "PASS" if ok else "FAIL", name, g(B["Xs"]), g(p["err"]), g(B["estar"]), decades(p["err"], B["estar"]))]


def refinedA_lines(W, lean_ok):
    """route A refined: the mirror's refinedCore parts (W['mirror']) and the compiled-Lean verdicts
    [refinedCore, checkHamClaim] of forced_witness.check_in_lean."""
    full, parts = W["mirror"]
    bad = [k for k, v in parts.items() if not v]
    out = ["%s route=A.refined check=refinedCore (mirror)%s: X* %s, err %s, threshold e* %s, log10(err/e*) %+.2f"
           % ("PASS" if full else "FAIL", "" if full else ": " + "/".join(bad), g(W["Xs"]), g(W["err"]),
              g(W["estar"]), decades(W["err"], W["estar"]))]
    for nm, v in zip(("refinedCore", "checkHamClaim"), lean_ok):
        out.append("%s route=A.refined check=%s (compiled Lean): %s" % ("PASS" if v else "FAIL", nm,
                                                                       "true" if v else "false"))
    return out
