#!/usr/bin/env python3
"""V2-CONSOL #6: the hybrid restart (`Hybrid.routeHybrid`) on the forced toy.  Untrusted producer tooling.

    python3 -I scripts/certifier/forced/forced_hybrid.py [TAG] [--prune DIGITS] [--zero-step] [--json OUT]

From the mirror objects of TAG (the pickle of forced_build.py, rebuilt in FORCED_WORK when missing) it builds the
witness `HybWit` of `checkHybrid` (KAM/CertificateSharp/Hybrid/, format docs/campaign/design/hybrid/format.md):

  * the step dK: a Newton step of the base torus K^, the difference K' - K^ of the emitted mantissas of a finer
    Picard torus K' (forced_model.solve_torus at `prune_digits` DIGITS instead of the base spec's), in the format of
    the base embedding (angle 0 in u = 2 pi U at degree -1, the actions at degree 0, no identity); dyadic at 2^-P,
    so `ratE` is exact;
  * every step claim from the port below of the hybrid checks on the sofx mirror of the landed checker (CertFixed
    backend, the certificate's own models and advice): hybPolyOk (Step.lean: stepSupOk, stepRealOk, dstepOk),
    hybOmegaOk (Omega.lean: omegaOk of dkM, dk1M), hybCompOk (Lin.lean: linModel, linOk; Energy.lean: enModel,
    energyLinOk), hybCauchyOk; each claim the exact backend value rounded up by 10^-4 (re-checked with `ble`);
  * the restart: rho1 = rho (the base run's sites are reused), mu1 = mu - 10^-9, the transferred numbers by the exact
    port scripts/apost_sharp/hybrid_mirror.py (TransferQ.lean), params1 and witness1 rounded upward (format §4), the
    route-A' (L8') core at the restart numbers by scripts/apost_sharp/hybrid_numq.py with the base L8' run's caps;
then the compiled Lean `transferOk`, `hybWeightsOk`, `hybCauchyOk` and `refinedCoreR` (`#eval`, ℚ-level) re-decide.
The model-level checks (hybPolyOk, hybOmegaOk, hybCompOk) are the kernel's.
"""
import argparse
import json
import math
import os
import sys
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(1, os.path.join(HERE, "..", "..", "spin_orbit"))
sys.path.insert(2, os.path.join(HERE, "..", "..", "apost_sharp"))
sys.setrecursionlimit(100000)

import forced_l1 as L1               # noqa: E402  (ensure, the Lean oracle with $FORCED_LEAN_PREFIX, weights)
import forced_cert as FC             # noqa: E402
import forced_lean as FL             # noqa: E402
import forced_witness as FW          # noqa: E402
import sofx_arith as A               # noqa: E402
import sofx_check as C               # noqa: E402
import sofx_model as M               # noqa: E402
import hybrid_mirror as HM           # noqa: E402
import hybrid_numq as NQ             # noqa: E402

MOD = "KAM.CertificateSharp.V2.Tests.Forced."
REAL = M.Weight(F(0), F(1))          # realWeight = ⟨0, 1⟩
HYB_KEY = (8,)                       # hybKey


# ---------------------------------------------------------------------------------------------- the step
def newton_step(c, prune_digits):
    """dK = K' - K^ (mantissas of the backend), K' the Picard torus of the base spec at prune_digits; as a dict
    {angleDeg, angle, actionDeg, action} of (zero, [(key, (re, im))]) with exact dyadic rationals."""
    B = c.B
    sp = dict(c.spec, prune_digits=prune_digits)
    _, _, T2 = FC.solve(sp, c.toy)
    T = c.torus

    def diff(S1, S0):
        out = {}
        for k in set(S1) | set(S0):
            a, b = S1.get(k, (F(0), F(0))), S0.get(k, (F(0), F(0)))
            m = (FC.mant(B, a[0]) - FC.mant(B, b[0]), FC.mant(B, a[1]) - FC.mant(B, b[1]))
            if m != (0, 0):
                out[k] = (F(m[0], B.D), F(m[1], B.D))
        return out

    def poly(D):
        z = D.get((0, 0), (F(0), F(0)))[0]
        return (z, sorted((k, v) for k, v in D.items() if k > (0, 0)))
    zero = (F(0), [])
    return dict(angleDeg=[-1, 0], angle=[poly(diff(T2.u, T.u)), zero], actionDeg=[0, 0],
                action=[poly(diff(T2.p, T.p)), poly(diff(T2.J, T.J))], info=T2.info)


def zero_step():
    zero = (F(0), [])
    return dict(angleDeg=[-1, 0], angle=[zero, zero], actionDeg=[0, 0], action=[zero, zero], info={})


def step_terms(dK):
    return sum(len(P[1]) for P in dK["angle"] + dK["action"])


def ratE(B, dK):
    """`ratE` (Claims.lean): every rational coefficient rounded upward into the backend."""
    rp = lambda P: M.RealPoly(B.ofRatUp(P[0]), [(k, (B.ofRatUp(v[0]), B.ofRatUp(v[1]))) for k, v in P[1]])
    return M.Embedding(list(dK["angleDeg"]), [rp(P) for P in dK["angle"]], list(dK["actionDeg"]),
                       [rp(P) for P in dK["action"]])


# ---------------------------------------------------------------------------------------------- the checks (port)
def step_model(B, n, dK, a):
    if a < n:
        return M.realCompModel(B, n, M.getD(dK.angleDeg, a), dK.angleAt(a))
    return M.realCompModel(B, n, M.getD(dK.actionDeg, a - n), dK.actionAt(a - n))


def dstep_model(B, n, W, pe, dK, a, j):
    if a < n:
        return C.compDerivModel(B, n, W, pe, M.getD(dK.angleDeg, a), dK.angleAt(a), j)
    return C.compDerivModel(B, n, W, pe, M.getD(dK.actionDeg, a - n), dK.actionAt(a - n), j)


def dot_model(B, W, cfg, pe, cnt, fa, fb):
    """dotModel: direct products at hybKey, summed by modelSum."""
    cd = cfg.withExtra(HYB_KEY, ("direct",))
    return M.modelSum(B, W, pe, [M.model_mul(B, W, cd, HYB_KEY, fa(j), fb(j)) for j in range(cnt)])


def inv_model_at(c, s1, ms, a):
    """invarianceModel n K box s1 W cfgFull pe ms a."""
    B, n, W, pe = c.B, c.n, c.weight, c.piEnc
    DKm = C.dkModels(B, n, c.DKc)
    x = C.msGet(ms, C.swapNat(n, a), B)
    lhs = x if a < n else M.negM(B, x)
    return M.addMixed(B, W, pe, lhs, M.negM(B, C.dkFreqModel(B, n, DKm, c.freqBox, s1, W, c.cfgFull, pe, a)))


def lin_model(c, s1, dK, ms, mt, a):
    B, n, W, pe = c.B, c.n, c.weight, c.piEnc
    dxh = C.dxhModels(B, n, mt)
    P1 = dot_model(B, W, c.cfgFull, pe, n + n, lambda b: C.entry(dxh, a, b, B), lambda b: step_model(B, n, dK, b))
    P2 = dot_model(B, W, c.cfgFull, pe, n, lambda l: C.freqModel(B, n, c.freqBox, s1, l),
                   lambda l: dstep_model(B, n, W, pe, dK, a, l))
    return M.addMixed(B, W, pe, M.addMixed(B, W, pe, inv_model_at(c, s1, ms, a), P1), M.negM(B, P2))


def en_model(c, dK, mv, ms):
    B, n, W, pe = c.B, c.n, c.weight, c.piEnc
    a = M.addMixed(B, W, pe, M.toDeg(B, W, pe, 0, mv), M.constModel(B, n, -F(c.params["E0"]), 0, 0))
    d = dot_model(B, W, c.cfgFull, pe, n + n, lambda b: C.msGet(ms, b, B), lambda b: step_model(B, n, dK, b))
    return M.addMixed(B, W, pe, a, M.toDeg(B, W, pe, 0, d))


def dk_m(c, W):
    D = C.dkModels(c.B, c.n, C.dkCache(c.B, c.n, c.emb, W, c.piEnc))
    return lambda a, j: C.entry(D, a, j, c.B)


def dk1_m(c, W, dK):
    B, n, pe = c.B, c.n, c.piEnc
    D = dk_m(c, W)
    return lambda a, j: M.addMixed(B, W, pe, D(a, j), dstep_model(B, n, W, pe, dK, a, j))


def omega_rows(c, W, Wb, Mm):
    """the row sums of omegaOk: sumUp_j supBound Wb (lagModel W cfgFull pe Mm i j)."""
    B, n, pe = c.B, c.n, c.piEnc
    row = lambda a, j: M.negM(B, Mm(a + n, j)) if a < n else Mm(a - n, j)
    lag = lambda i, j: dot_model(B, W, c.cfgFull, pe, n + n, lambda a: Mm(a, i), lambda a: row(a, j))
    return [M.sumUp(B, [M.supBound(B, Wb, lag(i, j)) for j in range(n)]) for i in range(n)]


def sums(B, n, lv, col):
    return L1.sums(B, n, lv, col)


def step_values(c, dK, W1, Winf, WT, s1):
    """every backend value the step checks compare with a claim (the lists the claim must dominate)."""
    B, n, pe = c.B, c.n, c.piEnc
    msF, _ = L1.inv_models(c)
    mt = c.stages["ms"]
    mv = M.compose(B, n, c.jetOps, c.emb, c.wit, c.weight, c.cfgFull, pe, [c.jet["v0"]])
    assert mv is not None and len(mv) == 1
    v = {}
    v["d0"] = [M.supBound(B, W1, step_model(B, n, dK, a)) for a in range(n + n)]
    v["dinf"] = [M.supBound(B, Winf, step_model(B, n, dK, a)) for a in range(n + n)]
    v["d0R"] = [M.supBound(B, REAL, step_model(B, n, dK, a)) for a in range(n + n)]
    lv1 = lambda a, j: M.supBound(B, W1, dstep_model(B, n, W1, pe, dK, a, j))
    lvR = lambda a, j: M.supBound(B, REAL, dstep_model(B, n, Winf, pe, dK, a, j))
    v["d1"], v["d1t"] = sums(B, n, lv1, False), sums(B, n, lv1, True)
    v["d1R"], v["d1tR"] = sums(B, n, lvR, False), sums(B, n, lvR, True)
    v["o0"] = omega_rows(c, WT, WT, dk_m(c, WT))
    v["o0R"] = omega_rows(c, Winf, REAL, dk_m(c, Winf))
    v["o1"] = omega_rows(c, WT, WT, dk1_m(c, WT, dK))
    v["o1R"] = omega_rows(c, Winf, REAL, dk1_m(c, Winf, dK))
    v["lE"] = [M.supBound(B, W1, lin_model(c, s1, dK, msF, mt, a)) for a in range(n + n)]
    d = en_model(c, dK, mv[0], msF)
    assert d.deg == 0
    z = C.zeroModeBall(B, n, d)
    v["lH"] = [B.upAdd(B.upAdd(A.normUp(B, z[0]), z[1]), d.rad)]
    return v, dict(msF=msF, mv=mv)


def claim_of(B, xs, rel=F(1, 10 ** 4)):
    """the least short rational >= every value (ble against ofRatDown), and >= 0 (`decide (0 ≤ d)`)."""
    if all(B.ble(x, B.ofInt(0)) for x in xs):
        return F(0)
    return L1.up_claim(B, xs, rel, 6)


# ---------------------------------------------------------------------------------------------- the witness
def hm_params(p):
    """forced params (som, nu) -> the hybrid mirror's names (sigma_omega, nuRay)."""
    q = dict(p)
    q["sigma_omega"], q["nuRay"] = p["som"], p["nu"]
    return q


def rnd_up(x, sig=13):
    return FW.up_rel(F(x), F(0), sig) if x > 0 else F(x)


def hybrid_witness(c, tag, prune_digits=14, zero=False, dmu=F(1, 10 ** 9), log=print):
    B, n = c.B, c.n
    p = dict(c.params)
    box = c.freqBox
    R0, _ = FW.refined_claim(c)
    dK = zero_step() if zero else newton_step(c, prune_digits)
    log("step: %d half terms %s" % (step_terms(dK), {"u": [(k, float(v[0]), float(v[1])) for k, v in
                                                            dK["angle"][0][1]][:4]}))
    dKe = ratE(B, dK)
    s1 = p["s"]
    rho1, rhoi = p["rho"], p["rhoInf"]
    d1 = min(F(1), (rho1 - rhoi) / 6)
    rhoT = rho1 - d1
    W1 = c.weight                                             # rho1 = rho: the certificate's own weight
    Winf, WT = L1.weight(c, rhoi), L1.weight(c, rhoT)
    vals, aux = step_values(c, dKe, W1, Winf, WT, s1)
    cl = {k: claim_of(B, vals[k]) for k in ("d0", "dinf", "d1", "d1t", "d0R", "d1R", "d1tR", "lE", "o0", "o0R", "o1",
                                           "o1R")}
    dE = rnd_up(n * p["err"] / (p["rho"] - rhoT))
    cl["dE0"] = cl["dE0R"] = dE
    lH = claim_of(B, vals["lH"])
    dw = F(0)                                                 # s1 = s
    log("claims", {k: float(v) for k, v in cl.items()}, "lH %.3e" % float(lH))
    # the restart (format §4): params1, witness1 rounded upward from the transferred numbers
    hp = hm_params(p)
    mu1 = p["mu"] - dmu
    st = dict(cl=cl, lH=lH, dw=dw, s1=s1)
    p1 = dict(hp, rho=rho1, mu=mu1, s=s1, err=F(0), disp=F(0), sK=F(0), sB=F(0), sT=F(0), nuRay=hp["nuRay"] - dw)
    w = dict(R0=R0, step=st, p1=p1, w1=dict(base=dict(R=dict(R0))))
    h = HM.hyb_numbers(n, hp, w)
    err1 = rnd_up(max(h["e1"], lH + R0["d2h"] / 2 * cl["d0R"] ** 2), 4)
    p1.update(err=err1, sK=h["sK1"], sB=rnd_up(h["sB1"]), sT=F(0))
    w = dict(R0=R0, step=st, p1=p1, w1=dict(base=dict(R=dict(R0))))
    h = HM.hyb_numbers(n, hp, w)                               # tAx, mT, t1 read err1 (qq.lH) and the claims
    p1["sT"] = rnd_up(h["mT"] + mu1)
    R1 = dict(R0, bL=rnd_up(h["kq"]["lt"] + cl["d1t"]), bN=rnd_up(h["kq"]["nu"] + h["frS"]["nD"]),
              bNt=rnd_up(h["kq"]["nut"] + h["frS"]["nDt"]), bT=rnd_up(h["t1"]))
    # the L8' run at the restart: the base L8' witness (TinyWitness: refinedWitR), its caps and sites
    base = FW_base_L8(c, tag)
    core = dict(base["core"])
    wR = dict(base=dict(core=core, R=R1, kappa=base["kappa"], sites=base["sites"]), bF=base["bF"], bT=base["bT"])
    # the closeness budget of the restart: finalOkA's c2, c3 at err1, rounded up, then the outer room
    Q = NQ.refined_num(n, p1, box, wR["base"])
    c23 = max(Q.c2Q(core["Xs"]), Q.c3Q(core["Xs"]))
    p1["disp"] = rnd_up(c23 * err1 / (p1["gamma"] ** 2 * p1["rho"] ** (2 * p1["tau"])) * F(101, 100), 4)
    w = dict(R0=R0, step=st, p1=p1, w1=wR)
    h = HM.hyb_numbers(n, hp, w)
    tr = HM.transfer_ok(n, hp, box, w, h)
    bad = [k for k, ok in tr if not ok]
    ok, parts = NQ.refined_core_r(n, p1, box, wR, detail=True)
    log("restart: err1 %.3e (base err %.3e), mu1 %s, disp1 %.3e; transferOk fails %s; refinedCoreR (no sites) %s %s"
        % (float(err1), float(p["err"]), mu1, float(p1["disp"]), bad, ok, parts))
    assert not bad and ok, (bad, parts)
    Xmax, _ = NQ.max_xs(n, p1, box, wR)
    log("restart X* %s (witness), largest passing okR %.4g; threshold of the restart e1* = X* gamma^4 delta0^4 = %.3e"
        % (core["Xs"], float(Xmax), float(Xmax * p["gamma"] ** 4 * d1 ** 4)))
    return dict(dK=dK, cl=cl, lH=lH, dw=dw, s1=s1, W1=W1, Winf=Winf, WT=WT, p1=p1, R0=R0, R1=R1, wR=wR,
                values={k: [float(B.val(x)) for x in v] for k, v in vals.items()}, aux=aux, h=h, err1=err1,
                Xmax=Xmax, rhoT=rhoT, delta1=d1)


def FW_base_L8(c, tag):
    """the base L8' witness of TAG: forced_routes' refinedWitR (route A refined witness at X* = 191 with bF = bT =
    10^-3), read from the fixture of the base witnesses."""
    path = os.path.join(HERE, "..", "fixtures", "forced-toy", "%s_witness.json" % tag)
    with open(path) as fh:
        d = json.load(fh)
    A_ = d["refinedA"]
    core = {k: (int(v) if k in ("kp", "J") else ([F(x) for x in v] if isinstance(v, list) else F(v)))
            for k, v in A_["core"].items() if k in ("Xs", "kp", "th", "c", "cbar", "ctail", "sB", "sT", "sLt", "sN",
                                                       "sNt", "t", "J")}
    R = d.get("refinedR") or {}
    core["Xs"] = F(R.get("Xs", "191"))
    sites = A_["sites"]
    return dict(core=core, kappa=F(A_["kappa"]), sites=sites, bF=F(R.get("bF", "1/1000")), bT=F(R.get("bT", "1/1000")))


# ---------------------------------------------------------------------------------------------- Lean terms
def lean_poly(P):
    q = FL.lq
    half = ", ".join("([%d, %d], ⟨%s, %s⟩)" % (k[0], k[1], q(v[0]), q(v[1])) for k, v in P[1])
    return "⟨%s, [%s]⟩" % (q(P[0]), half)


def lean_step_emb(dK):
    return "⟨[%s], [%s], [%s], [%s]⟩" % (
        ", ".join(str(d) for d in dK["angleDeg"]), ", ".join(lean_poly(P) for P in dK["angle"]),
        ", ".join(str(d) for d in dK["actionDeg"]), ", ".join(lean_poly(P) for P in dK["action"]))


def lean_params(p):
    q = FL.lq
    return ("{ tau := %d, rho := %s, rhoInf := %s, M := %s, σK := %s, σB := %s, σT := %s, μ := %s, γbar := %s, "
            "σω := %s, nuRay := %s, γ := %s, s := %s, err := %s, E0 := %s, disp := %s }") % (
        p["tau"], q(p["rho"]), q(p["rhoInf"]), q(p["M"]), q(p["sK"]), q(p["sB"]), q(p["sT"]), q(p["mu"]),
        q(p["gbar"]), q(p["sigma_omega"]), q(p["nuRay"]), q(p["gamma"]), q(p["s"]), q(p["err"]), q(p["E0"]),
        q(p["disp"]))


def lean_claim(R):
    return "{ dh := %s, dx := %s, d2x := %s, d2h := %s, bL := %s, bN := %s, bNt := %s, bT := %s }" % tuple(
        FL.lq(R[k]) for k in ("dh", "dx", "d2x", "d2h", "bL", "bN", "bNt", "bT"))


def lean_stepnum(cl):
    names = ("d0", "dinf", "d1", "d1t", "d0R", "d1R", "d1tR", "lE", "dE0", "o0", "dE0R", "o0R", "o1", "o1R")
    return "{ %s }" % ", ".join("%s := %s" % (k, FL.lq(cl[k])) for k in names)


def lean_hyb_step(W):
    return ("{ dK := %s, s1 := %s, W1 := %s, Winf := %s, WT := %s, cl := %s, lH := %s, dw := %s }" % (
        lean_step_emb(W["dK"]), FL.lq(W["s1"]), L1.lean_weight(W["W1"]), L1.lean_weight(W["Winf"]),
        L1.lean_weight(W["WT"]), lean_stepnum(W["cl"]), FL.lq(W["lH"]), FL.lq(W["dw"])))


def lean_witR(wR):
    b = wR["base"]
    base = FW.lean_refined_wit(dict(core=b["core"], R=b["R"], kappa=b["kappa"], sites=[
        tuple(s if s is None else {k: (F(v) if k in ("E1", "B", "c") else v) for k, v in s.items()} for s in pr)
        for pr in b["sites"]]))
    return "{ base := %s, bF := %s, bT := %s }" % (base, FL.lq(wR["bF"]), FL.lq(wR["bT"]))


def lean_hyb_wit(W):
    return "{ R0 := %s, step := %s, p1 := %s, w1 := %s }" % (lean_claim(W["R0"]), lean_hyb_step(W),
                                                            lean_params(W["p1"]), lean_witR(W["wR"]))


def check_in_lean(tag, W):
    """the compiled Lean ℚ-level parts of `checkHybrid` (the model-level checks are the kernel's)."""
    H = "KAM.CertificateSharp.Hybrid."
    prelude = "def wH : %sHybWit := %s" % (H, lean_hyb_wit(W))
    c = "%s.cert" % tag
    exprs = [
        "%stransferOk 2 %s.params %s.freqBox wH" % (H, c, c),
        "%shybWeightsOk %s wH.step wH.p1.rho wH.p1.rhoInf (wH.ρT 2 %s.freqBox)" % (H, c, c),
        "%shybCauchyOk %s wH.step (wH.ρT 2 %s.freqBox)" % (H, c, c),
        "decide (|wH.step.s1 - %s.params.s| * KAM.CertificateSharp.V2.boxNormUp %s.freqBox ≤ wH.step.dw)" % (c, c),
        "KAM.CertificateSharp.V2.refinedCoreR 2 wH.p1 %s.freqBox wH.w1" % c,
        "KAM.CertificateSharp.V2.checkHamClaim %s wH.R0" % c,
    ]
    outs = L1.lean_eval([MOD + tag + "Data", "KAM.CertificateSharp.Hybrid.Iso"],
                        ["KAM.CertificateSharp.V2.Forced", "KAM.Certificate"], exprs, prelude=prelude)
    return dict(zip(["transferOk", "hybWeightsOk", "hybCauchyOk", "dw", "refinedCoreR", "checkHamClaim"],
                    [FL.parse_bool(o) for o in outs]))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("tag", nargs="?", default="Tiny")
    ap.add_argument("--prune", type=int, default=14)
    ap.add_argument("--zero-step", action="store_true")
    ap.add_argument("--no-lean", action="store_true")
    a = ap.parse_args()
    c = L1.ensure(a.tag)
    W = hybrid_witness(c, a.tag, a.prune, a.zero_step)
    print(lean_hyb_wit(W))
    if not a.no_lean:
        r = check_in_lean(a.tag, W)
        print("compiled Lean:", r)
        assert all(r.values()), r


if __name__ == "__main__":
    main()
