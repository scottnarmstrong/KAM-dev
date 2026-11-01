#!/usr/bin/env python3
"""V2-TOOLS #6: the v2 witnesses of a forced-toy certificate (routes of `routeV2All`).  Untrusted tooling.

    python3 -I scripts/certifier/forced/forced_witness.py TAG [--routes refinedA,refinedR,...]

Inputs: the pickle of forced_build.py (the mirror objects of TAG).  For each requested route the witness is
chosen from the certificate's own numbers:
  * the refined claim R: the four Hamiltonian sums of the disc pass (sodata3_v2checks.ham_values) and the frame
    row maxima (sodata3_v2checks.frame_values; the torsion rows from the same stages the kernel memoizes), rounded
    up by a relative 10^-4;
  * certified small-divisor sites: for every bite the cut-off 2^l and degree J are searched with the compiled
    Lean `balCheck`/`balBound` (forced_lean.lean_eval), the constant c is the least 4-digit rational with
    `B κ^-2 (γ b)^2 <= (3.1415 c)^2`;
  * the run numbers (caps, X*) from the exact mirror of the route core (v2_q.py / v2_r2.py), X* the largest
    3-digit value passing, then re-checked by the compiled Lean core.
Writes certificates/forced-toy/<TAG>_witness.json and returns the witnesses as Lean terms (forced_routes.py).
"""
import json
import math
import os
import pickle
import sys
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(1, os.path.join(HERE, "..", "..", "spin_orbit"))
sys.path.insert(2, os.path.join(HERE, "..", "..", "apost_sharp"))

import forced_lean as FL            # noqa: E402
import sodata3_v2checks as V2C      # noqa: E402
import v2_q as V                    # noqa: E402
import v2_r2 as R2                  # noqa: E402

MOD = "KAM.CertificateSharp.V2.Tests.Forced."


def up_rel(x, rel=F(1, 10 ** 4), sig=4):
    x = F(x) * (1 + rel)
    if x <= 0:
        return F(1, 10 ** 6)
    e = math.floor(math.log10(float(x))) - (sig - 1)
    D = F(10) ** e
    return math.ceil(x / D) * D


def load(tag, work=None):
    wd = work or os.environ.get("FORCED_WORK") or "/tmp"
    with open(os.path.join(wd, "forced_%s.pkl" % tag), "rb") as fh:
        return pickle.load(fh)


# ---------------------------------------------------------------------------------------------- the claim R
def refined_claim(c):
    B = c.B
    hv = V2C.ham_values(c)
    fv = V2C.frame_values(B, c)
    R = dict(dh=up_rel(hv["dh"]), dx=up_rel(hv["dx"]), d2x=up_rel(hv["d2x"]), d2h=up_rel(hv["d2h"]),
             bL=up_rel(max(fv["L"])), bN=up_rel(max(fv["N"])), bNt=up_rel(max(fv["Nt"])), bT=up_rel(max(fv["T"])))
    ok, parts = V2C.checkFrameMajorants(B, c, dict(R, bOm=fv["Om"][0]))
    assert V2C.checkHamClaim(c, R) and parts["L"] and parts["N"] and parts["T"], (R, parts)
    return R, dict(ham=hv, frame=fv)


# ---------------------------------------------------------------------------------------------- sites
def e1_of(b):
    """a short rational >= exp(-4 pi b)."""
    return up_rel(F(math.exp(-4 * math.pi * float(b))), F(2, 10 ** 3), 6)


def site_search(tag, bites, kappa, gamma, ls=range(3, 10), Js=(8, 12, 16, 20, 28)):
    """{b: (l, J, E1, B)} with balCheck true, minimizing the resulting constant, then l."""
    exprs, keys = [], []
    for b in bites:
        E1 = e1_of(b)
        for l in ls:
            for J in Js:
                w = "(⟨%s, %d, %d, 0⟩ : KAM.CertificateSharp.V2.BiteWit)" % (FL.lq(E1), l, J)
                d = "(KAM.CertificateSharp.V2.biteData %s.box %s %s %s %s)" % (
                    tag, FL.lq(kappa), FL.lq(gamma), FL.lq(b), w)
                exprs.append("(KAM.Sharp2.Examples.balCheck %s %d, KAM.Sharp2.Examples.balBound %s %d)" % (
                    d, l, d, l))
                keys.append((b, l, J, E1))
    outs = FL.lean_eval([MOD + tag + "Data", "KAM.CertificateSharp.V2.SmallDivQ"],
                        ["KAM.CertificateSharp.V2.Forced"], exprs)
    best = {}
    for (b, l, J, E1), o in zip(keys, outs):
        ok_s, bound_s = o.strip("()").split(", ")
        if not FL.parse_bool(ok_s):
            continue
        Bq = FL.parse_q(bound_s)
        cst = site_c(Bq, kappa, gamma, b)
        cand = (cst, l, J)
        if b not in best or cand < best[b][0]:
            best[b] = (cand, dict(l=l, J=J, E1=E1, B=up_rel(Bq, F(1, 10 ** 6), 6)))
    return {b: dict(v[1], c=site_c(v[1]["B"], kappa, gamma, b)) for b, v in best.items()}


def site_c(Bq, kappa, gamma, b):
    """the least 4-digit c with B kappa^-2 (gamma b)^2 <= (31415/10000 c)^2."""
    x = math.sqrt(float(Bq / kappa ** 2 * (gamma * b) ** 2)) / 3.1415
    cst = up_rel(F(x), F(1, 10 ** 6), 4)
    while not (Bq * (1 / kappa ** 2) * (gamma * b) ** 2 <= (F(31415, 10000) * cst) ** 2):
        cst = up_rel(cst, F(1, 10 ** 4), 4)
    return cst


# ---------------------------------------------------------------------------------------------- route A refined
def params_of(c):
    p = dict(c.params)
    return p


def refined_A(c, tag, kp=3, th=F(1, 8), J=20, log=print):
    p = params_of(c)
    box = c.freqBox
    kappa = box[1][0]
    R, rv = refined_claim(c)
    log("R", {k: float(v) for k, v in R.items()})
    # the bites of the run (NumQ.δ, NumQ.b; v2_q.Num mirrors RouteAQ)
    Q0 = V.Num(n=2, tau=1, rho=p["rho"], rhoInf=p["rhoInf"], kp=kp)
    bites = sorted({Q0.delta(s) for s in range(kp)} | {Q0.b(s) for s in range(kp)})
    sites = site_search(tag, bites, kappa, p["gamma"])
    log("sites", {float(b): (s["l"], s["J"], float(s["c"])) for b, s in sites.items()})
    sd = {}
    for s in range(kp):
        sd[("d", s)] = sites[Q0.delta(s)]["c"] if Q0.delta(s) in sites else None
        sd[("b", s)] = sites[Q0.b(s)]["c"] if Q0.b(s) in sites else None
    for k, v in sd.items():
        if v is None:      # no certified site: the classical constant (siteOk none)
            d = Q0.delta(k[1]) if k[0] == "d" else Q0.b(k[1])
            sd[k] = V.classical_c(2, 1, J, d)
    Xs = R2.max_Xs("refined", p, box, kp, th, J, R, sd, lo=-30.0, hi=8.0, steps=40)
    ok, why, w = R2.okB_at("refined", p, box, kp, th, J, Xs, R, sd, detail=True)
    assert ok, why
    w = dict(w, R=R)
    full = V.refinedCore(2, p, box, w, detail=True)
    log("refinedCore mirror", full[1], "Xs", float(Xs), "e*", float(Xs * p["gamma"] ** 4 * Q0.d0 ** 4))
    sitelist = []
    for s in range(kp):
        a = sites.get(Q0.delta(s))
        b = sites.get(Q0.b(s))
        sitelist.append((a, b))
    return dict(core=w, R=R, kappa=kappa, sites=sitelist, Xs=Xs, mirror=full, claim_values=rv, kp=kp, th=th, J=J)


# ---------------------------------------------------------------------------------------------- Lean terms
def lean_bite(s):
    if s is None:
        return "none"
    return "some ⟨%s, %d, %d, %s⟩" % (FL.lq(s["E1"]), s["l"], s["J"], FL.lq(s["B"]))


def lean_refined_wit(W):
    w = W["core"]
    q = FL.lq
    core = ("{ Xs := %s, kp := %d, th := %s, c := [%s], cbar := [%s], ctail := %s, sB := %s, sT := %s, "
            "sLt := %s, sN := %s, sNt := %s, t := %s, J := %d }") % (
        q(w["Xs"]), w["kp"], q(w["th"]), ", ".join(q(x) for x in w["c"]), ", ".join(q(x) for x in w["cbar"]),
        q(w["ctail"]), q(w["sB"]), q(w["sT"]), q(w["sLt"]), q(w["sN"]), q(w["sNt"]), q(w["t"]), w["J"])
    R = W["R"]
    Rs = "{ dh := %s, dx := %s, d2x := %s, d2h := %s, bL := %s, bN := %s, bNt := %s, bT := %s }" % tuple(
        q(R[k]) for k in ("dh", "dx", "d2x", "d2h", "bL", "bN", "bNt", "bT"))
    sites = ", ".join("(%s, %s)" % (lean_bite(a), lean_bite(b)) for a, b in W["sites"])
    return "{ core := %s, R := %s, κ := %s, sites := [%s] }" % (core, Rs, q(W["kappa"]), sites)


def check_in_lean(tag, wit_term, exprs_extra=()):
    prelude = "def wA : KAM.CertificateSharp.V2.RefinedWit := %s" % wit_term
    exprs = ["KAM.CertificateSharp.V2.refinedCore 2 %s.cert.params %s.cert.freqBox wA" % (tag, tag),
             "KAM.CertificateSharp.V2.checkHamClaim %s.cert wA.R" % tag]
    exprs += list(exprs_extra)
    return FL.lean_eval([MOD + tag + "Data", "KAM.CertificateSharp.V2.RouteAll"],
                        ["KAM.CertificateSharp.V2.Forced", "KAM.Certificate"], exprs, prelude=prelude)


if __name__ == "__main__":
    tag = sys.argv[1]
    c = load(tag)
    W = refined_A(c, tag)
    term = lean_refined_wit(W)
    print(term)
    print(check_in_lean(tag, term))


# ---------------------------------------------------------------------------------------------- lever L8'
def refined_R(tag, W, grid=None):
    """(bF, bT) of route A with lever L8' passing the compiled `refinedCoreR`, the first of the grid."""
    grid = grid or [(F(1, 10 ** a), F(1, 10 ** b)) for a in (4, 3, 5, 6) for b in (3, 2, 4)]
    term = lean_refined_wit(W)
    prelude = "def wA : KAM.CertificateSharp.V2.RefinedWit := %s" % term
    exprs = ["KAM.CertificateSharp.V2.refinedCoreR 2 %s.cert.params %s.cert.freqBox ⟨wA, %s, %s⟩" % (
        tag, tag, FL.lq(bF), FL.lq(bT)) for bF, bT in grid]
    outs = FL.lean_eval([MOD + tag + "Data", "KAM.CertificateSharp.V2.RouteAll"],
                        ["KAM.CertificateSharp.V2.Forced", "KAM.Certificate"], exprs, prelude=prelude)
    for (bF, bT), o in zip(grid, outs):
        if FL.parse_bool(o):
            return dict(bF=bF, bT=bT, grid=[(str(a), str(b), o) for (a, b), o in zip(grid, outs)])
    return None


def jsonable(x):
    if isinstance(x, F):
        return str(x)
    if isinstance(x, dict):
        return {str(k): jsonable(v) for k, v in x.items()}
    if isinstance(x, (list, tuple)):
        return [jsonable(v) for v in x]
    return x
