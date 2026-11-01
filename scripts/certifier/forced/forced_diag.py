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
    out = ["FAIL route=A.frozen check=frozenCore.%s: false at X* %s" % (k, g(Xs))
           for k, v in parts.items() if not v and k != "final"]
    # the three clauses of `finalOk` (v2_q.finalOk; FrozenCore's final comparisons), each with its numbers
    Q = V.frozen_num(w, 2, p, box)
    tau = p["tau"]
    estar = Xs * p["gamma"] ** 4 * Q.d0 ** (4 * tau)
    small = p["err"] < estar
    out.append("%s route=A.frozen check=frozenCore.final.smallness: X* %s, err %s, threshold e* %s, "
               "log10(err/e*) %+.2f" % ("PASS" if small else "FAIL", g(Xs), g(p["err"]), g(estar),
                                        decades(p["err"], estar)))
    out += _disp_sigma_lines("A.frozen", "frozenCore.final", p, box, [
        ("max(c2Q, c3Q, C2#, C3#)", V.disp_coefs(Q, 2, p, Xs, True)[0])])
    return full, out


def _disp_sigma_lines(route, prefix, p, box, coefs):
    """the displacement comparisons C err <= disp γ²ρ^{2τ} (one per constant C) and the ray clause
    disp < (σω - s) |box|_lo, shared by FrozenCore's finalOk and route B's finalB."""
    import v2_q as V
    tau = p["tau"]
    rhs = p["gamma"] ** 2 * p["rho"] ** (2 * tau)
    out = []
    for i, (nm, C) in enumerate(coefs):
        ok = C * p["err"] <= p["disp"] * rhs
        out.append("%s route=%s check=%s.%s: %s err <= disp γ²ρ^2τ: disp %s, needed %s" % (
            "PASS" if ok else "FAIL", route, prefix, "displacement" if i == 0 else "displacement_sharp", nm,
            g(p["disp"]), g(C * p["err"] / rhs)))
    bound = (p["som"] - p["s"]) * V.freqNormLo(box)
    ok = p["disp"] < bound
    out.append("%s route=%s check=%s.sigma_omega: disp %s < (σω - s) |box|_lo %s" % (
        "PASS" if ok else "FAIL", route, prefix, g(p["disp"]), g(bound)))
    return out


def c3B(N, I, Xs):
    """`NumBQ.c3Q` (RouteBQWf.lean) with `freqSum` (RouteBQ.lean), over the mirror's NumB: route_b_lean_mirror
    has c1B and c2B (ballSum) but not this one."""
    import route_b_lean_mirror as RB
    x = N.xS(Xs, N.kp)
    t = lambda s: N.k(s)["sCnu"] * (N.γb * RB.ipow(N.δ(s), N.τ + 1)) * x[s]
    fs = sum(t(s) for s in range(N.kp)) + t(N.kp) / (1 - N.ybar)
    return (RB.ipow(N.ρ, 2 * N.τ) * max(I["iLt"], RB.pN(N, I) * N.γb * RB.ipow(N.δ0(), N.τ)) * fs
            / (Xs * RB.ipow(N.δ0(), 2 * N.τ + 1)))


def routeB_parts(c, B, frozen=True):
    """every clause of `frozenBCore` (frozen; its final comparisons are `finalBF`) or of `refinedBCore`
    (RouteBCore.lean) in the exact mirror, as [(check, ok, numbers)].  B is forced_witness.route_B's result.  The
    certified sites of the refined route (`biteOk`) are left to the compiled Lean (`check_B_in_lean`); classical
    sites and the tail are `classicalOk` (v2_q.classicalOk)."""
    import forced_witness as FW
    import route_b_lean_mirror as RB
    import sharp_q as SQ
    import v2_q as V
    p, box = dict(c.params), c.freqBox
    I, Xs, kp, J = B["I"], B["Xs"], B["kp"], B["J"]
    N = FW.numB(p, box, None if frozen else B["R"], B["consts"], B["caps"], kp, frozen)
    tau = p["tau"]
    parts = [("Xs", Xs > 0, "X* %s" % g(Xs))]
    if frozen:
        parts += [("mu_lt_sK", p["mu"] < p["sK"], "μ %s, σK %s" % (g(p["mu"]), g(p["sK"]))),
                  ("mu_lt_sB", p["mu"] < p["sB"], "μ %s, σB %s" % (g(p["mu"]), g(p["sB"]))),
                  ("sB_cap", p["sB"] - p["mu"] < B["caps"]["sB"], "σB - μ %s, cap %s" % (
                      g(p["sB"] - p["mu"]), g(B["caps"]["sB"])))]
    wf = RB.wf_fails(N, I, p["sT"], p["mu"])
    parts.append(("wfOk/fitsOk/initOk", not wf, "failing: %s" % ", ".join(wf) if wf else "all hold"))
    try:
        ob = RB.routeBOk(N, RB.capB(N, p["sT"], p["mu"], p["nu"]), RB.initB(I, p["sK"], p["sB"], p["mu"]),
                         p["mu"] / 2, Xs)
    except ZeroDivisionError:
        ob = ["division by zero"]
    parts.append(("okB", not ob, "failing: %s" % ", ".join(map(str, ob)) if ob else "J1-J4 hold"))
    bad_sites = []
    for s in range(kp):
        site = B["sites"][s] if s < len(B["sites"]) else (None, None, None)
        for (bite, cst), wit in zip(((N.δ(s), N.c(s)), (N.split() * N.δ(s), N.c_(s)), (N.bfull(s), N.cbar(s))),
                                    site):
            if wit is None and not V.classicalOk(2, tau, J, bite, cst):
                bad_sites.append("s=%d bite %s" % (s, g(bite)))
    parts.append(("sitesOk", not bad_sites, "classical sites below their constant: %s" % bad_sites if bad_sites
                  else "classical sites hold%s" % ("" if frozen else "; certified sites: compiled Lean")))
    tail = V.classicalOk(2, tau, J, N.δ(kp), N.ctail) and V.classicalOk(2, tau, J, N.bfull(kp), N.cbtail)
    parts.append(("tailOk", tail, "classical constants at δ_kp and min(r_kp, 1)"))
    estar = p["gamma"] ** 4 * p["rho"] ** (4 * tau) / RB.c1B(N, I, Xs)
    parts.append(("finalB.smallness", p["err"] < estar, "X* %s, err %s, threshold e* %s, log10(err/e*) %+.2f" % (
        g(Xs), g(p["err"]), g(estar), decades(p["err"], estar))))
    rhs = p["gamma"] ** 2 * p["rho"] ** (2 * tau)
    coefs = [("max(c2Q, c3Q)", max(RB.c2B(N, I, Xs), c3B(N, I, Xs)), "finalB.displacement")]
    if frozen:
        r = SQ.sharp(p)
        coefs.append(("max(C2#, C3#)", max(r["C2"], r["C3"]), "finalBF.sharp_displacement"))
    for nm, C, chk in coefs:
        parts.append((chk, C * p["err"] <= p["disp"] * rhs, "%s err <= disp γ²ρ^2τ: disp %s, needed %s" % (
            nm, g(p["disp"]), g(C * p["err"] / rhs))))
    bound = (p["som"] - p["s"]) * V.freqNormLo(box)
    parts.append(("finalB.sigma_omega", p["disp"] < bound, "disp %s < (σω - s) |box|_lo %s" % (
        g(p["disp"]), g(bound))))
    return parts


def frozenB_lines(c, B, frozen=True):
    """route B (forced_witness.route_B): B is its result, None when no X* passed `routeBOk`; otherwise every clause
    of `frozenBCore` / `refinedBCore` in the mirror (routeB_parts)."""
    name = "B.frozen" if frozen else "B.refined"
    if B is None:
        return False, ["FAIL route=%s check=routeBOk: no X* in [1e-30, 1e8] passes (the caps diverge or a "
                       "stage clause fails at every X*)" % name]
    parts = routeB_parts(c, B, frozen)
    return all(ok for _, ok, _ in parts), ["%s route=%s check=%s: %s" % ("PASS" if ok else "FAIL", name, chk, txt)
                                           for chk, ok, txt in parts]


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


# ---------------------------------------------------------------------------------------------- cross-language
class _Cert:
    def __init__(self, params, box):
        self.params, self.freqBox = params, box


def xlang_routeB(tag, log=print):
    """the route-B mirror above (routeB_parts, c3B) against the compiled Lean checker, on the frozen-B witness of
    <TAG>Routes.lean (built): c1Q, c2Q, c3Q exactly, frozenBCore, and finalBF and finalB two-sided in disp (the
    certificate's disp; one between the thresholds of finalB.displacement and finalBF.sharp_displacement; one below
    both), so each displacement clause is seen to pass and to fail on both sides.
    Returns True iff every comparison agrees."""
    import forced_lean as FL
    import forced_witness as FW
    import route_b_lean_mirror as RB
    import sharp_q as SQ
    c = FW.load(tag)
    B = FW.route_B(c, tag, None, frozen=True, log=lambda *a: None)
    p, box = dict(c.params), c.freqBox
    N = FW.numB(p, box, None, B["consts"], B["caps"], B["kp"], True)
    I, Xs = B["I"], B["Xs"]
    T = "KAM.CertificateSharp.V2.Forced.%s" % tag
    Q = "(%s.frozenBWit.num %s.cert.params %s.cert.freqBox %s.cert.params.M %s.cert.params.M %s.cert.params.M)" % (
        (T,) * 6)
    Iq = "(KAM.CertificateSharp.V2.defaultIB 2 %s.cert.params)" % T
    args = "%s.1 %s.2.2 %s.frozenBWit.Xs" % (Iq, Iq, T)
    c2, c3 = RB.c2B(N, I, Xs), c3B(N, I, Xs)
    rows = [("c1Q", RB.c1B(N, I, Xs), "%s.c1Q %s" % (Q, args)), ("c2Q", c2, "%s.c2Q 2 %s" % (Q, args)),
            ("c3Q", c3, "%s.c3Q 2 %s" % (Q, args)),
            ("frozenBCore", frozenB_lines(c, B)[0],
             "KAM.CertificateSharp.V2.frozenBCore 2 %s.cert.params %s.cert.freqBox %s.frozenBWit" % (T, T, T))]
    rhs = p["gamma"] ** 2 * p["rho"] ** (2 * p["tau"])
    r = SQ.sharp(p)
    need = sorted([max(c2, c3) * p["err"] / rhs, max(r["C2"], r["C3"]) * p["err"] / rhs])
    for lab, d in (("certificate's disp", p["disp"]), ("disp between the two thresholds", (need[0] + need[1]) / 2),
                   ("disp below both thresholds", need[0] / 2)):
        d = F(d).limit_denominator(10 ** 40) if d != p["disp"] else d
        parts = routeB_parts(_Cert(dict(p, disp=d), box), B)
        for fn, pre in (("finalBF", "final"), ("finalB", "finalB.")):
            verdict = all(ok for chk, ok, _ in parts if chk.startswith(pre))
            rows.append(("%s at %s (%s)" % (fn, lab, g(d)), verdict,
                         "KAM.CertificateSharp.V2.%s %s 2 { %s.cert.params with disp := %s } %s.cert.freqBox %s" % (
                             fn, Q, T, FL.lq(d), T, args)))
    outs = FL.lean_eval([MODS + tag + "Routes"], [], [e for _, _, e in rows])
    ok_all = True
    for (lab, py, _), o in zip(rows, outs):
        lean = FL.parse_bool(o) if o.strip() in ("true", "false") else FL.parse_q(o)
        ok_all &= lean == py
        log("%-6s %s %-52s python=%-24s lean=%s" % ("OK" if lean == py else "DIFFER", tag, lab, str(py)[:24],
                                                    o.strip()[:24]))
    log("route-B mirror against Lean: %s (%d comparisons)" % ("ALL AGREE" if ok_all else "DISAGREEMENT", len(rows)))
    return ok_all


MODS = "KAM.CertificateSharp.V2.Tests.Forced."


if __name__ == "__main__":
    import argparse
    ap = argparse.ArgumentParser(description="cross-language check of the route-B diagnostics mirror")
    ap.add_argument("--xlang", metavar="TAG", required=True, help="a tag whose <TAG>Routes.lean is built (Micro)")
    a = ap.parse_args()
    sys.exit(0 if xlang_routeB(a.xlang) else 1)
