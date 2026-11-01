#!/usr/bin/env python3
"""V2-TOOLS #3: producer-side route and parameter selection by predicted total kernel cost (untrusted tooling).

    python3 -I scripts/certifier/route_select.py PROFILE [--margin M] [--beta B] [--pi P] [--l1-design] [--json OUT]
    python3 -I scripts/certifier/route_select.py --validate [--write-fixtures]   # lunar65 and lg00 vs hand choices

`routeV2All` is unchanged: the trusted interface dispatches whatever witness the producer emits.  This tool decides
which witness to emit.  For a model and candidate torus family (a PROFILE: scripts/certifier/fixtures/route-select/
<name>.json, written by route_profiles.py) it evaluates, at every strip ρ of the profile's grid:

  route                 threshold e* from                                   kind
  sharp (baseline)      sharp_q.sharp (the landed sharp engine)              exact mirror
  A.frozen              v2_r2.max_Xs('frozen')                               exact mirror
  A.refined.classical   v2_r2.max_Xs('refined'), classical sites            exact mirror
  A.refined.cert[kp]    the same, certified sites (c = c_freq × 1.01) where   exact mirror (sites: float c; the
                        the clock test applies and the cut-off l <= l_max    Lean balCheck is the check)
  A.refined.cert[d01b]  certified δ₀, δ₁ and every b site (SO-V2PKG's d01b)  exact mirror
  B.frozen, B.refined   forced_witness.solve_B (route_b_lean_mirror)         exact mirror
  A.L8'                 refined e*/2 (the forced toy's passing X* ratio)      estimate
  l1-entry              refined e* × 10^0.288 (the forced toy's kernel-      estimate (default); with
                        checked gain); --l1-design: × 10^0.75 (R1 design)    --l1-design: design estimate
  hybrid                sqrt(e1*/A_meas), e1* the refined e* at ρ - 3δ₀       design estimate (needs A_meas)

Where the profile carries re-measured thresholds (lunar: SO-V2PKG §4.6, the d01b row re-measured per ρ with
σK, σB and the frame claims re-enclosed), the d01b route takes the re-measured value and every other route at that ρ
the same shift (kind "+remeasured" / "+shifted"); otherwise σK, σB and the claim are held at the package's values.

It then scans the truncation L and the precision P: predicted err(L, ρ, P) from the profile's table (log-linear in
L; each candidate says whether its err is measured, interpolated or extrapolated), the ρ factor, a precision floor
10^4 · 2^-P (unmeasured model); the profile's precision rule (LG00: 2^-P <= 10^-(L+12), LG00-CERT.md:204; lunar:
2^-P <= 10^-4 err, one data point of SO-V2PKG §4.1) removes the too-coarse precisions.  The predicted cost is

    C = C_ref (S(L)/S_ref)^β (P/P_ref)^π · (1 + extra_route) + direct_route + Σ_sites c(l),
    c(l) = c_8 · 2^{1.29 (l - 8)} s,

C_ref the measured cost of the hand choice (lunar: SO-CSPLIT-GATE; LG00: the run20e ledger).  **π is not measured**
(no ledger holds two precisions at one support): the default π = 1 is an assumption, and β is fitted on LG00's L = 8
pilot (CertFixed 96) against its L = 20 ledger (CertFixed 128) with the precision ratio (128/96)^π divided out
(β = 0.775 at π = 1; 0.933 at π = 0); both pairs are reported.  extra_route is 0 for sharp/frozen/refined (frames,
claim and core are 0.7 % of LG00's run once the stages are shared) and for L8' (measured on the forced toy, within
the noise); for the l1 entry and the hybrid it is MEASURED on the forced toy `Tiny` (V2-CONSOL: kernel CPU of the
route's additional checks over the refined-A test, as a fraction of the landed checks plus the refined-A test, sites
excluded, stages memoized and shared; fixtures/route-select/forced_costs.json, written by
scripts/certifier/forced/forced_costs.py), replacing V2-TOOLS's unmeasured guesses 0.5 and 1.0.  direct_route is the
hybrid's direct products (the Lagrange matrices of hybOmegaOk and the products DX_H ΔK, which use the direct product
whatever the advice): their CPU measured at the toy's support, scaled as (S/S_toy)^2 (P/96)^π times 2, an ESTIMATE.
A toy measurement extrapolates to an application only as far as the operations measured; `cost_terms()` labels every
term measured or estimated with its source, and the run prints them.  A candidate is admissible when its unrounded
margin log10(e*/err) exceeds the requested margin strictly, its certified sites have l <= l_max, and its precision obeys
the rule.  The tool returns the cheapest admissible candidate (exact mirrors preferred at equal cost) and the
cheapest admissible sharp candidate as the baseline fallback; that fallback's err is a prediction (for LG00 at
L >= 24 from LG00-PREP's table, whose sharp margin was never observed).  Certified sites at a strip other than the
package's are flagged "not balCheck-verified".
"""
import argparse
import json
import math
import os
import sys
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))
FIX = os.path.join(HERE, "fixtures", "route-select")
sys.path.insert(0, os.path.join(ROOT, "scripts", "spin_orbit"))
sys.path.insert(1, os.path.join(ROOT, "scripts", "apost_sharp"))
sys.path.insert(2, os.path.join(HERE, "forced"))

import sharp_q as SQ                 # noqa: E402
import v2_q as V                     # noqa: E402
import v2_r2 as R2                   # noqa: E402
import smalldiv as SD                # noqa: E402
import route_b_lean_mirror as RB     # noqa: E402
import forced_witness as FW          # noqa: E402

TH, J, KP_FROZEN = F(1, 8), 20, 5
FORCED_FIX = os.path.join(HERE, "fixtures", "forced-toy")


def l1_delta_toy():
    """The l1 entry's kernel-checked threshold gain on the forced toy `Tiny` (V2-CONSOL), in decades: log10 of the
    l1 run's e* (strip rho' = 1/10, X* = 1830, its own certified sites; kernel-tests/CertificateSharp/V2/
    ForcedL1Hybrid.lean, `l1_torus`) over the best refined route's e* (refined A at rho = 1/8, X* = 382, certified
    sites; ForcedRoutes.lean), from fixtures/forced-toy/Tiny_l1.json and Tiny_witness.json: +0.288.  On the toy the
    ray budget binds, not the entry.  The conservative default (orchestrator ruling, V2-CONSOL-FIX)."""
    with open(os.path.join(FORCED_FIX, "Tiny_l1.json")) as fh:
        a = F(json.load(fh)["estar"])
    with open(os.path.join(FORCED_FIX, "Tiny_witness.json")) as fh:
        b = F(json.load(fh)["refinedA"]["estar"])
    return math.log10(a / b)


L1_MODELS = {
    "toy": dict(delta=l1_delta_toy(), kind="estimate",
                source="kernel-checked gain on the forced toy Tiny, log10(e*_l1 / e*_refinedA) "
                       "(fixtures/forced-toy/Tiny_l1.json, Tiny_witness.json); the default"),
    "design": dict(delta=0.75, kind="design",
                   source="thresholds_v2 --l1 at R1 (iso): A7 -10.95, A7 + l1 entry -10.20; a design estimate, "
                          "selected by --l1-design"),
}
L1 = dict(L1_MODELS["toy"])     # the l1-entry threshold model in use (main() switches it on --l1-design)
L8_FACTOR = F(1, 2)      # forced toy Tiny: L8' was found passing at X* = 191 against refined A's 382 (both
#                          kernel-checked, kernel-tests/.../ForcedRoutes.lean); the ratio of the maxima is not checked
COSTS = os.path.join(FIX, "forced_costs.json")      # the forced toy's measured route costs (forced_costs.py)


def cost_terms():
    """Every term of the predicted kernel cost, with its kind ('measured' or 'estimated') and its source.  The route
    extras are fractions of the base cost C (the landed checks plus the refined-A test, sites excluded):
    C_route = C (1 + extra) + direct (+ the sites).  The l1-entry and hybrid extras are measured on the forced toy
    `Tiny` (support 5 u half-terms, CertFixed 96, direct products): a toy figure extrapolates to an application only
    as far as the operations measured.  The l1 entry adds l1Up sums of memoized models (linear in their terms) and a
    rational core (support-free), scaled here with the base; the hybrid adds, besides such checks, the Lagrange
    matrices `Mᵀ Ω₀ M` and the products `DX_H ΔK` with the direct product (`Hybrid.directCfg`, no packed advice),
    quadratic in the support while the packed base grows as S^β: that part (`direct`) is scaled quadratically from
    the toy, an estimate."""
    with open(COSTS) as fh:
        m = json.load(fh)
    r, toy = m["ratios"], m["toy"]
    src = "forced toy Tiny, scripts/certifier/fixtures/route-select/forced_costs.json (forced_costs.py; " \
          "kernel-tests/CertificateSharp/V2/ForcedL1Hybrid.lean)"
    return {
        "C_ref": dict(kind="measured", source="the profile's cost_ref (lunar: SO-CSPLIT-GATE; LG00: run20e ledger)"),
        "beta": dict(kind="measured (fit)", source="LG00's L = 8 pilot against its L = 20 ledger, precision ratio "
                     "(128/96)^pi divided out (fit_beta)"),
        "pi": dict(value=1.0, kind="estimated", source="assumption: no ledger holds two precisions at one support"),
        "extra[sharp, A.frozen, A.refined.*, B.*]": dict(value=0.0, kind="measured", source="ledger_fit.json: "
                                                         "frames, claim and core 0.7 % of LG00's run20e"),
        "extra[A.L8']": dict(value=0.0, kind="measured", source=src + ": (refinedCoreR - refinedCore)/C = %+.4f, "
                             "within the noise; set to 0" % r["extra_L8"]),
        "extra[l1-entry]": dict(value=r["extra_l1"], kind="measured", source=src + ": (L1 - Rcore)/C, the guards, "
                                "the residuals of checkL1L/N/T/E on memoized stages and l1Core, less refinedCore; "
                                "C = %.1f s (toy)" % r["D_s"], previous="0.5, an unmeasured guess (V2-TOOLS)"),
        "extra[hybrid]": dict(value=r["extra_hyb"], kind="measured", source=src + ": (hyb - omega - Rcore)/C, "
                              "transferOk, the step norms, the Cauchy bound, hybCompOk's residual on the memoized "
                              "compositions, refinedCoreR at the restart, less refinedCore",
                              previous="1.0, an unmeasured guess (V2-TOOLS), the whole extra"),
        "direct[hybrid]": dict(value_s=r["omega_s"], factor=2.0, S_toy=toy["support_u_half_terms"], P_toy=toy["P"],
                               exponent=2.0, kind="estimated",
                               source=src + ": hybOmegaOk's CPU at the toy (%d direct coefficient pairs) is measured; "
                               "the quadratic scaling in the support and the factor 2 (the products DX_H ΔK at a step "
                               "of the torus's support, about as many pairs as the Lagrange matrices) are assumptions"
                               % toy["omega_direct_pairs"]),
        "c(l)": dict(kind="measured / estimated", source="the profile's site_cost_s (SHARP2-C6: l = 8..12, measured); "
                     "other l: 2.4 · 2^(1.29 (l - 8)) s (estimated)"),
        "err floor": dict(kind="estimated", source="1e4 · 2^-P, calibrated on the forced toy's P = 40 point only"),
    }


TERMS = cost_terms()
EXTRA = {"l1-entry": TERMS["extra[l1-entry]"]["value"], "hybrid": TERMS["extra[hybrid]"]["value"]}
DIRECT = {"hybrid": TERMS["direct[hybrid]"]}


def lg(x):
    return math.log10(float(x)) if x and x > 0 else float("-inf")


# ---------------------------------------------------------------------------------------------- profiles
def load_profile(name):
    with open(os.path.join(FIX, "%s.json" % name)) as fh:
        d = json.load(fh)
    d["params"] = {k: (int(v) if k == "tau" else F(v)) for k, v in d["params"].items()}
    d["box"] = [(F(a), F(b)) for a, b in d["box"]]
    d["R"] = {k: F(v) for k, v in d["R"].items()}
    return d


def params_at(prof, rho):
    p = dict(prof["params"])
    if not prof["rho_fixed"]:
        ratio = p["rhoInf"] / p["rho"]
        p["rho"], p["rhoInf"] = F(rho), F(rho) * ratio
    return p


# ---------------------------------------------------------------------------------------------- sites
def clock_ok(box):
    """the certified-site test (SmallDivQ.clockOk) needs n = 2 and an exact positive last coordinate."""
    return len(box) == 2 and box[1][1] == 0 and box[1][0] > 0


def site(prof, p, box, bite, kind):
    """(c, l, certified) at one bite: the certified constant (c_freq × 1.01) and its cut-off l, or the classical."""
    rule = F(prof["site_l_rule"]["delta" if kind == "d" else "b"])
    l = max(3, math.ceil(math.log2(float(rule / bite))))
    if clock_ok(box) and l <= prof["site_l_max"]:
        om = (float(box[0][0]), float(box[1][0]))
        c = V.up(SD.c_freq(om, float(p["gamma"]), 1, float(bite))[0] * 1.01, 4)
        return c, l, True
    return V.classical_c(2, 1, J, bite), l, False


def site_cost(prof, l):
    tab = {int(k): v for k, v in prof["site_cost_s"].items()}
    return tab.get(l, 2.4 * 2 ** (1.29 * (l - 8)))


# ---------------------------------------------------------------------------------------------- thresholds
def route_A(prof, p, box, branch, kp, certify, policy=None):
    """(e*, Xs, binding at 1.1 X*, displacement coefficient C/(γ²ρ²), site list [(kind, s, l, certified)])."""
    R = prof["R"]
    Q0 = V.Num(n=2, tau=1, rho=p["rho"], rhoInf=p["rhoInf"], kp=kp)
    sites, slist = None, []
    if branch == "refined":
        sites = {}
        for s in range(kp):
            for kind, bite in (("d", Q0.delta(s)), ("b", Q0.b(s))):
                if certify and not (policy == "d01b" and kind == "d" and s >= 2):
                    c, l, cert = site(prof, p, box, bite, kind)
                else:
                    c, l, cert = V.classical_c(2, 1, J, bite), 0, False
                sites[(kind, s)] = c
                slist.append(dict(kind=kind, s=s, bite=float(bite), l=l, certified=cert, c=float(c)))
    try:
        Xs = R2.max_Xs(branch, p, box, kp, TH, J, R if branch == "refined" else None, sites, lo=-40.0, hi=8.0,
                       steps=34)
    except Exception as e:                     # noqa: BLE001  (a mirror failure is reported, not chosen)
        return dict(error=repr(e)[:200])
    ok, why, w = R2.okB_at(branch, p, box, kp, TH, J, Xs, R if branch == "refined" else None, sites, detail=True)
    _, why_up, _ = R2.okB_at(branch, p, box, kp, TH, J, Xs * F(11, 10), R if branch == "refined" else None, sites,
                             detail=True)
    Q = V.frozen_num(w, 2, p, box) if branch == "frozen" else V.refined_num(dict(w, R=R), 2, p, box)
    C, *_ = V.disp_coefs(Q, 2, p, Xs, branch == "frozen")
    d0 = Q0.d0
    return dict(estar=Xs * p["gamma"] ** 4 * d0 ** 4, Xs=Xs, binding=why_up[:3], disp_coef=C / (p["gamma"] ** 2 *
                p["rho"] ** 2), sites=slist, ok=ok)


def route_B(prof, p, box, frozen, kp=2):
    R = prof["R"]
    d0, dl, sp, bfull = FW.b_bites(p, kp)
    consts = ([V.classical_c(2, 1, J, dl(s)) for s in range(kp)], [V.classical_c(2, 1, J, sp(s)) for s in range(kp)],
              [V.classical_c(2, 1, J, bfull(s)) for s in range(kp)], V.classical_c(2, 1, J, dl(kp)),
              V.classical_c(2, 1, J, bfull(kp)))
    I = FW.default_IB(p) if frozen else dict(iLt=R["bL"], iN=R["bN"], iNt=R["bNt"])
    lo, hi, best = -30.0, 8.0, None
    for _ in range(26):
        mid = (lo + hi) / 2
        Xs = FW.up_rel(F(10 ** mid), F(0), 3)
        try:
            N, caps, fails = FW.solve_B(p, box, R, I, consts, kp, Xs, frozen, iters=60)
        except (ZeroDivisionError, OverflowError):
            fails = ["arith"]
        if not fails:
            lo, best = mid, (Xs, N)
        else:
            hi = mid
    if best is None:
        return dict(error="no passing X*")
    Xs, N = best
    c1 = RB.c1B(N, I, Xs)
    return dict(estar=p["gamma"] ** 4 * p["rho"] ** 4 / c1, Xs=Xs, binding=[], disp_coef=None, sites=[], ok=True)


def thresholds(prof, rho, kps=(1, 2, 3), with_B=True, log=print):
    p = params_at(prof, rho)
    box = prof["box"]
    out = {}
    sh = SQ.sharp(dict(p))
    out["sharp"] = dict(estar=sh["threshold"], kind="exact", disp_coef=sh.get("disp_coef"), binding=[],
                        sites=[])
    out["A.frozen"] = dict(route_A(prof, p, box, "frozen", KP_FROZEN, False), kind="exact")
    out["A.refined.classical"] = dict(route_A(prof, p, box, "refined", 3, False), kind="exact")
    for kp in kps:
        if clock_ok(box):
            out["A.refined.cert[kp=%d]" % kp] = dict(route_A(prof, p, box, "refined", kp, True), kind="exact")
    rm = prof.get("remeasured")
    if rm and clock_ok(box):
        out["A.refined.cert[d01b]"] = dict(route_A(prof, p, box, "refined", 3, True, policy=rm["policy"]),
                                           kind="exact")
    if with_B:
        out["B.frozen"] = dict(route_B(prof, p, box, True), kind="exact")
        out["B.refined.classical"] = dict(route_B(prof, p, box, False), kind="exact")
    refs = [v for k, v in out.items() if k.startswith("A.refined") and "estar" in v]
    if not refs:        # V2-PUBLIC #3: the estimates scale the best refined threshold; say why they are missing
        log("  rho %-7s no A.refined route produced a threshold (errors below): A.L8' and l1-entry skipped" % rho)
    else:
        best_ref = max(refs, key=lambda v: v["estar"])
        out["A.L8'"] = dict(estar=best_ref["estar"] * L8_FACTOR, kind="estimate", sites=best_ref.get("sites", []),
                            binding=[], disp_coef=None)
        out["l1-entry"] = dict(estar=best_ref["estar"] * F(10 ** L1["delta"]).limit_denominator(10 ** 6),
                               kind=L1["kind"], sites=best_ref.get("sites", []), binding=[], disp_coef=None)
    if prof.get("A_meas"):
        d0 = min(F(1), (p["rho"] - p["rhoInf"]) / 6)
        p1 = dict(p, rho=p["rho"] - 3 * d0)
        e1 = route_A(prof, p1, box, "refined", 3, clock_ok(box))
        if "estar" in e1:
            out["hybrid"] = dict(estar=F(math.sqrt(float(e1["estar"]) / float(F(prof["A_meas"])))),
                                 kind="design", sites=e1["sites"], binding=[], disp_coef=None)
    if rm and rho in rm["log10_estar"] and "estar" in out.get("A.refined.cert[d01b]", {}):
        # SO-V2PKG §4.6 re-measured the package at this strip (σK, σB, frame claims): the d01b route takes the
        # re-measured threshold, every other route the same shift (the re-measurement acts on shared data)
        delta = float(rm["log10_estar"][rho]) - lg(out["A.refined.cert[d01b]"]["estar"])
        for k, v in out.items():
            if "estar" in v:
                v["estar"] = v["estar"] * F(10 ** delta).limit_denominator(10 ** 12)
                v["remeasure_shift"] = round(delta, 3)
                v["kind"] = v["kind"] + "+remeasured" if k == "A.refined.cert[d01b]" else v["kind"] + "+shifted"
    for k, v in out.items():
        if "estar" in v:
            log("  rho %-7s %-24s log10 e* %7.2f  %s" % (rho, k, lg(v["estar"]), v["kind"]))
        else:
            log("  rho %-7s %-24s %s" % (rho, k, v.get("error")))
    return out


# ---------------------------------------------------------------------------------------------- err, support, cost
def interp_log(table, x):
    pts = sorted((float(k), math.log(float(v))) for k, v in table.items())
    if x <= pts[0][0]:
        (x0, y0), (x1, y1) = pts[0], pts[1]
    elif x >= pts[-1][0]:
        (x0, y0), (x1, y1) = pts[-2], pts[-1]
    else:
        for (x0, y0), (x1, y1) in zip(pts, pts[1:]):
            if x0 <= x <= x1:
                break
    return math.exp(y0 + (y1 - y0) * (x - x0) / (x1 - x0))


def err_at(prof, L, rho, P):
    """predicted err: log-linear in L from the measured/predicted table, the ρ factor, and a precision floor
    1e4 · 2^-P (an unmeasured model, calibrated on the forced toy's P = 40 point only)."""
    e = interp_log(prof["err_L"], L)
    if not prof["rho_fixed"]:
        e *= float(F(prof["err_rho_factor"][rho]))
    return max(e, 1e4 * 2.0 ** -P)


def err_source(prof, L, rho):
    meas = set(prof.get("err_L_measured", []))
    pkg = prof["rho_fixed"] or rho == prof["hand"]["rho"]
    if str(L) in meas and pkg:
        return "measured"
    lo, hi = min(int(k) for k in meas), max(int(k) for k in meas)
    return "interpolated" if lo <= L <= hi else "extrapolated"


def precision_ok(prof, L, e, P):
    """the profile's precision rule: LG00 2^-P <= 10^-(L+12) (LG00-CERT.md:204); lunar 2^-P <= 1e-4 err (one data
    point, SO-V2PKG §4.1)."""
    r = prof.get("precision_rule")
    if r is None:
        return True
    if r["kind"] == "abs_budget":
        return 2.0 ** -P <= 10.0 ** -(L + r["offset"])
    return 2.0 ** -P <= float(F(r["factor"])) * e


def support_at(prof, L):
    return interp_log(prof["support_L"], L)


def cost_h(prof, route, L, P, sites, beta, pi):
    S_ref = support_at(prof, prof["cost_ref"]["L"])
    base = float(F(prof["cost_ref"]["cpu_h"])) * (support_at(prof, L) / S_ref) ** beta * (P / prof["P_ref"]) ** pi
    base *= 1 + EXTRA.get(route, 0.0)
    d = DIRECT.get(route)
    if d:                     # the hybrid's direct products: the toy's CPU, scaled quadratically (estimated)
        base += d["value_s"] * d["factor"] * (support_at(prof, L) / d["S_toy"]) ** d["exponent"] * \
            (P / d["P_toy"]) ** pi / 3600
    return base + sum(site_cost(prof, s["l"]) for s in sites if s.get("certified")) / 3600


# ---------------------------------------------------------------------------------------------- selection
def candidates(prof, th_by_rho, beta=2.0, pi=1.0):
    Ls = sorted({int(k) for k in prof["err_L"]} | set(range(min(int(k) for k in prof["err_L"]),
                                                         max(int(k) for k in prof["err_L"]) + 1)))
    out = []
    for rho, th in th_by_rho.items():
        for route, r in th.items():
            if "estar" not in r:
                continue
            feasible_sites = all(s["l"] <= prof["site_l_max"] for s in r.get("sites", []) if s.get("certified"))
            for L in Ls:
                for P in prof["P_grid"]:
                    e = err_at(prof, L, rho, P)
                    m = lg(r["estar"]) - math.log10(e)
                    out.append(dict(route=route, kind=r["kind"], rho=rho, L=L, P=P, log10_estar=round(lg(r["estar"]),
                                    2), log10_err=round(math.log10(e), 2), margin=round(m, 2), margin_exact=m,
                                    err_source=err_source(prof, L, rho), precision_ok=precision_ok(prof, L, e, P),
                                    sites_verified=(rho == prof["hand"]["rho"]),
                                    support=round(support_at(prof, L)), cost_h=round(cost_h(prof, route, L, P,
                                    r.get("sites", []), beta, pi), 3), sites_ok=feasible_sites,
                                    sites=[s["l"] for s in r.get("sites", []) if s.get("certified")],
                                    binding=r.get("binding", []), displacement=(float(r["disp_coef"]) * e
                                                                                if r.get("disp_coef") else None)))
    return out


def select(cands, margin, exact_only=False):
    ok = [c for c in cands if c["margin_exact"] > margin and c["sites_ok"] and c["precision_ok"] and
          (c["kind"].startswith("exact") or not exact_only)]
    rank = lambda c: (c["cost_h"], 0 if c["kind"].startswith("exact") else 1, -c["margin_exact"])
    best = min(ok, key=rank) if ok else None
    base = [c for c in ok if c["route"] == "sharp"]
    fallback = min(base, key=rank) if base else None
    return best, fallback


def hand_candidate(prof, cands):
    h = prof["hand"]
    want = h["route"]
    pool = [c for c in cands if c["L"] == h["L"] and c["rho"] == h["rho"] and c["P"] == h["P"]]
    pool = [c for c in pool if c["route"] == want or (want == "A.refined.certified" and
                                                      c["route"] == "A.refined.cert[kp=%d]" % h["kp"])]
    return pool[0] if pool else None


def fit_beta(pi):
    """the support exponent of the packed kernel cost, from LG00's L = 8 pilot (CertFixed 96) against its L = 20
    ledger (CertFixed 128), torsion stages and Gram, with the precision ratio (128/96)^pi divided out:
    beta = mean of [log(cost ratio) - pi log(128/96)] / log(support ratio).  pi itself is not measured (no ledger
    holds two precisions at one support), so beta and pi are reported as a pair."""
    prof = load_profile("lg00")
    pl, led = prof["pilot_L8"], prof["ledger"]
    sr = math.log(prof["support_L"]["20"] / pl["support"])
    pr = pi * math.log(prof["cost_ref"]["P"] / pl["P"])
    bt = (math.log(led["Torsion"]["cpu_h"] * 3600 / pl["torsion_s"]) - pr) / sr
    bg = (math.log(led["Gram"]["cpu_h"] * 3600 / pl["gram_s"]) - pr) / sr
    return (bt + bg) / 2, dict(torsion=round(bt, 3), gram=round(bg, 3), pi=pi)


def run_profile(name, margin=None, beta=None, pi=1.0, with_B=True, log=print):
    prof = load_profile(name)
    if beta is None:
        beta, parts = fit_beta(pi)
        log("beta fitted on the LG00 ledger (packed products), precision ratio divided out at pi = %.1f "
            "(unmeasured): %.3f %s" % (pi, beta, parts))
    margin = prof["margin_rule"] if margin is None else margin
    log("profile %s: %s" % (name, prof["title"]))
    th = {rho: thresholds(prof, rho, with_B=with_B, log=log) for rho in prof["rho_grid"]}
    cands = candidates(prof, th, beta, pi)
    best, fb = select(cands, margin)
    best_exact, _ = select(cands, margin, exact_only=True)
    hand = hand_candidate(prof, cands)
    sens = {}
    for pv in (0.0, 1.0):
        bv, _ = fit_beta(pv)
        for b in sorted({round(bv, 3), 1.5, 2.0}):
            c2 = candidates(prof, th, b, pv)
            bb, _ = select(c2, margin, exact_only=True)
            hh = hand_candidate(prof, c2)
            sens["pi=%.0f beta=%.3f" % (pv, b)] = dict(choice=pick(bb), hand_cost_h=hh and hh["cost_h"],
                                                     ratio=(bb["cost_h"] / hh["cost_h"]) if (bb and hh) else None)
    h = prof["hand"]
    same_pkg = [c for c in cands if c["rho"] == h["rho"] and c["P"] == h["P"]]
    cons1, _ = select(same_pkg, margin, exact_only=True)
    cons2, _ = select(same_pkg, h["margin"] - 0.02, exact_only=True)
    constrained = {"hand's ρ and P, margin %.1f" % margin: dict(choice=pick(cons1), verdict=verdict(cons1, hand)),
                   "hand's ρ and P, the hand's realized margin %.2f" % h["margin"]: dict(choice=pick(cons2),
                                                                                        verdict=verdict(cons2, hand))}
    rep = dict(profile=name, margin_rule=margin, beta=beta, pi=pi, best=best, best_exact=best_exact,
               constrained=constrained,
               baseline_fallback=fb, hand=hand,
               verdict=verdict(best_exact, hand), sensitivity=sens,
               thresholds={rho: {k: dict(log10_estar=round(lg(v["estar"]), 2) if "estar" in v else None,
                                         kind=v.get("kind"), binding=v.get("binding"),
                                         sites=[(s["kind"], s["s"], s["l"], s["certified"]) for s in v.get("sites",
                                                                                                         [])],
                                         error=v.get("error")) for k, v in t.items()} for rho, t in th.items()},
               candidates=cands)
    return rep


def pick(c):
    keys = ("route", "rho", "L", "P", "margin", "cost_h", "kind", "err_source", "sites_verified")
    return None if c is None else {k: c[k] for k in keys if k in c}


def verdict(best, hand):
    if best is None or hand is None:
        return "no comparison (best %s, hand %s)" % (pick(best), pick(hand))
    same = all(best[k] == hand[k] for k in ("route", "rho", "L", "P"))
    if same:
        return "reproduces the hand choice"
    # the same configuration under another name (at ρ = 1/140, kp = 3 and d01b certify the same five sites)
    if all(best[k] == hand[k] for k in ("rho", "L", "P", "log10_estar", "sites")):
        return "reproduces the hand choice (route %s, the same sites and threshold as %s)" % (best["route"],
                                                                                           hand["route"])
    r = best["cost_h"] / hand["cost_h"] if hand["cost_h"] else None
    return "differs: predicted cost %.3f CPU-h against the hand choice's %.3f (ratio %.2f)" % (
        best["cost_h"], hand["cost_h"], r)


def why_none(rep, site_l_max, only=None):
    """V2-PUBLIC #3: why no exact-mirror candidate (or, with only=["sharp"], no baseline fallback) is admissible,
    route by route (printed only in that case): the threshold the mirror could not compute, else the first
    admissibility test that every candidate of the route fails (margin > margin_rule, certified sites
    l <= site_l_max, the profile's precision rule)."""
    m = rep["margin_rule"]
    out = ["no admissible %s (margin > %.1f decades, certified sites l <= %d, precision rule):" % (
        "exact candidate" if only is None else "candidate of route " + ", ".join(only), m, site_l_max)]
    for rho, t in rep["thresholds"].items():
        for route, v in t.items():
            if v.get("error") and (only is None or route in only):
                out.append("FAIL route=%s check=threshold: the mirror failed at rho %s: %s" % (route, rho,
                                                                                             v["error"]))
    by = {}
    for c in rep["candidates"]:
        if c["kind"].startswith("exact") and (only is None or c["route"] in only):
            by.setdefault(c["route"], []).append(c)
    for route in sorted(by):
        cs = by[route]
        ok_m = [c for c in cs if c["margin_exact"] > m]
        ok_s = [c for c in ok_m if c["sites_ok"]]
        if not ok_m:
            b = max(cs, key=lambda c: c["margin_exact"])
            out.append("FAIL route=%s check=margin: best log10(e*/err) %.2f at rho %s, L %d, P %d (%s err), short "
                       "of %.1f by %.2f decades" % (route, b["margin_exact"], b["rho"], b["L"], b["P"],
                                                    b["err_source"], m, m - b["margin_exact"]))
        elif not ok_s:
            out.append("FAIL route=%s check=sites: every candidate with the margin needs a certified site with "
                       "l > %d (l = %s)" % (route, site_l_max, sorted({x for c in ok_m for x in c["sites"]})))
        else:
            b = min(ok_s, key=lambda c: c["P"])
            out.append("FAIL route=%s check=precision: every candidate with the margin fails the profile's "
                       "precision rule (e.g. L %d, P %d, log10 err %.2f)" % (route, b["L"], b["P"], b["log10_err"]))
    return out


def table(rep, top=12):
    rows = sorted([c for c in rep["candidates"] if c["margin_exact"] > rep["margin_rule"] and c["sites_ok"] and
                   c["precision_ok"]], key=lambda c: c["cost_h"])[:top]
    out = ["| route | kind | ρ | L | P | log10 e* | log10 err (source) | margin | support | cost (CPU-h) | sites l |",
           "|---|---|---|---:|---:|---:|---|---:|---:|---:|---|"]
    for c in rows:
        out.append("| %s | %s | %s | %d | %d | %.2f | %.2f (%s) | %.3f | %d | %.3f | %s%s |" % (
            c["route"], c["kind"], c["rho"], c["L"], c["P"], c["log10_estar"], c["log10_err"], c["err_source"],
            c["margin_exact"], c["support"], c["cost_h"], ",".join(map(str, c["sites"])) or "-",
            "" if c["sites_verified"] or not c["sites"] else " (not balCheck-verified)"))
    return "\n".join(out)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("profile", nargs="?")
    ap.add_argument("--margin", type=float, default=None)
    ap.add_argument("--beta", type=float, default=None, help="default: fitted on the LG00 ledger")
    ap.add_argument("--pi", type=float, default=1.0)
    ap.add_argument("--no-B", action="store_true")
    ap.add_argument("--validate", action="store_true")
    ap.add_argument("--json", default=None, help="write the report here (nothing is written otherwise)")
    ap.add_argument("--write-fixtures", action="store_true",
                    help="with --validate: overwrite scripts/certifier/fixtures/route-select/validation.json")
    ap.add_argument("--l1-design", action="store_true",
                    help="l1-entry threshold: the R1 design estimate (+0.75 decades over the best refined route) "
                         "instead of the forced toy's kernel-checked gain (+0.288, the default)")
    a = ap.parse_args()
    L1.update(L1_MODELS["design" if a.l1_design else "toy"])
    TERMS["threshold[l1-entry]"] = dict(value=round(L1["delta"], 4), kind=L1["kind"], source=L1["source"])
    names = ["lunar65", "lg00"] if a.validate else [a.profile]
    print("cost terms (kind, source):")
    for k, v in TERMS.items():
        val = v.get("value", v.get("value_s"))
        print("  %-42s %-10s %-20s %s" % (k, "" if val is None else val, v["kind"], v["source"]))
    reps = []
    for nm in names:
        rep = run_profile(nm, a.margin, a.beta, a.pi, with_B=not a.no_B)
        reps.append(rep)
        print("\n## %s (margin >= %.1f decades, beta %.2f)\n" % (nm, rep["margin_rule"], rep["beta"]))
        print(table(rep))
        print("\nbest (exact mirrors): %s" % pick(rep["best_exact"]))
        print("best (incl. estimates): %s" % pick(rep["best"]))
        print("baseline fallback (landed sharp; err %s, not observed): %s" % (
            rep["baseline_fallback"] and rep["baseline_fallback"]["err_source"], pick(rep["baseline_fallback"])))
        print("hand choice: %s" % pick(rep["hand"]))
        print("verdict: %s" % rep["verdict"])
        if rep["best_exact"] is None or rep["baseline_fallback"] is None:
            print("\n".join(why_none(rep, load_profile(nm)["site_l_max"],
                                      None if rep["best_exact"] is None else ["sharp"])))
        for k, v in rep["constrained"].items():
            print("constrained (%s): %s -> %s" % (k, v["choice"], v["verdict"]))
        for k, v in rep["sensitivity"].items():
            print("sensitivity %s: %s ratio %s" % (k, v["choice"] and (v["choice"]["route"], v["choice"]["rho"],
                                                                    v["choice"]["L"], v["choice"]["P"]),
                                                 v["ratio"] and round(v["ratio"], 3)))
    out = a.json or (os.path.join(FIX, "validation.json") if (a.validate and a.write_fixtures) else None)
    if out is None:
        return
    for rep in reps:          # keep the feasible candidates, cheapest first (the full scan is recomputed in seconds)
        rep["candidates"] = sorted([c for c in rep["candidates"] if c["margin_exact"] > rep["margin_rule"] and
                                    c["sites_ok"] and c["precision_ok"]], key=lambda c: c["cost_h"])[:40]
    with open(out, "w") as fh:
        json.dump(reps, fh, indent=1, default=str)


if __name__ == "__main__":
    main()
