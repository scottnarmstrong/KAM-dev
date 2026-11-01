#!/usr/bin/env python3
"""V2-CONSOL #6: route A with the l1 entry (`L1.routeAL1`) on the forced toy.  Untrusted producer tooling.

    python3 -I scripts/certifier/forced/forced_l1.py [TAG] [--rho1 R] [--json OUT]

From the mirror objects of TAG (the pickle of forced_build.py, rebuilt in FORCED_WORK when missing, without
touching the fixtures) it chooses the witness `L1Wit` of `routeAL1` (KAM/CertificateSharp/V2/RouteAL1*.lean):

  * the l1 claim `L1Claim`: the sums of `checkL1Claim` (RouteAL1Facts.lean) computed by the sofx mirror of the
    landed checker on the certificate's own models (E: the invariance models of `checkInvariance`; L: `dkModels`;
    N: `frameNModels` = the omega of the [4, 0] stage; T: the torsion block of `torsionModels`), each `l1Up` at the
    weights `W1` (strip rho1 < rho) and `WT` (strip rho1 - delta0'), rounded up by 10^-4;
  * the run: C6's refined run on the strip rho1 (`L1Wit.num`), its certified small-divisor sites at the bites of
    that strip (Lean `balCheck`, forced_witness.site_search), the classical tail;
  * the entry record `EntryQ`: a_N = |L^T Om0|_1 |E|_1 / e, a_L = |N^T Om0|_1 |E|_1 / e (Wiener products), the
    torsion row bound, the frame caps, Gamma_inf(s w*, delta0') and Gamma_inf(s w*, rho1) by the fibered test
    (scripts/apost_sharp/c6l1_gamma.py);
  * X* the largest 3-digit value whose tight caps pass `okL1` (an exact port of RouteAL1Q.lean / RouteAL1Run.lean
    below, on v2_q.py's StepQ) and `finalL1`.
Every decision is then re-made by the compiled Lean `l1Core` (forced_lean `#eval`); the kernel decides the test.
"""
import argparse
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
sys.setrecursionlimit(100000)

import forced_build as FB            # noqa: E402
import forced_cert as FC             # noqa: E402
import forced_lean as FL             # noqa: E402
import forced_stages as FS           # noqa: E402
import forced_witness as FW          # noqa: E402
import sofx_check as C               # noqa: E402
import sofx_model as M               # noqa: E402
import v2_q as V                     # noqa: E402
import v2_r2 as R2                   # noqa: E402
import c6l1_gamma as G6              # noqa: E402

MOD = "KAM.CertificateSharp.V2.Tests.Forced."
EI = F(3679, 10000)
JI = [0, 1, 1, 1, 1, 1, 1, 1, 0]


# ---------------------------------------------------------------------------------------------- the Lean oracle
def lean_eval(imports, opens, exprs, timeout=1800, prelude=""):
    """forced_lean.lean_eval, with the Lean command prefixed by $FORCED_LEAN_PREFIX (default `nice -n 5`), e.g. a
    lock and memory-scope wrapper on a shared machine: FORCED_LEAN_PREFIX='flock LOCK leanrun.sh'."""
    import re
    import shlex
    import subprocess
    import tempfile
    tag = "@@V2T@@"
    lines = ["import %s" % m for m in imports]
    lines.append("open %s" % " ".join(opens) if opens else "")
    lines.append(prelude)
    for i, e in enumerate(exprs):
        lines.append('#eval IO.println ("%s%d " ++ toString (%s))' % (tag, i, e))
    pre = shlex.split(os.environ.get("FORCED_LEAN_PREFIX", "nice -n 5"))
    with tempfile.TemporaryDirectory(dir=os.environ.get("FORCED_WORK")) as d:
        path = os.path.join(d, "Probe.lean")
        with open(path, "w") as fh:
            fh.write("\n".join(lines) + "\n")
        r = subprocess.run(pre + ["lake", "env", "lean", path], cwd=FL.ROOT, capture_output=True, text=True,
                           timeout=timeout)
    out = {}
    for ln in (r.stdout + r.stderr).splitlines():
        m = re.match(r"%s(\d+) (.*)$" % tag, ln)
        if m:
            out[int(m.group(1))] = m.group(2)
    if len(out) != len(exprs):
        errs = [ln for ln in (r.stdout + r.stderr).splitlines() if "error" in ln]
        raise RuntimeError("lean_eval: %d of %d values; errors: %s" % (len(out), len(exprs), "\n".join(errs[:10])))
    return [out[i] for i in range(len(exprs))]


FL.lean_eval = lean_eval          # forced_witness.site_search and every oracle call below go through the prefix


# ---------------------------------------------------------------------------------------------- the mirror objects
def work_dir():
    d = os.environ.get("FORCED_WORK") or "/tmp"
    os.makedirs(d, exist_ok=True)
    return d


def ensure(tag):
    """the pickle of forced_build.py for TAG; rebuilt (mirror only: no Lean file and no fixture written) if absent."""
    path = os.path.join(work_dir(), "forced_%s.pkl" % tag)
    if not os.path.exists(path):
        spec = dict(FB.SPECS[tag], name=tag)
        c = FC.generate(spec, log=lambda *a: None)
        assert c.report["passes_base"], c.report["checks"]
        c.stages = FS.stages(c)
        with open(path, "wb") as fh:
            pickle.dump(c, fh)
    with open(path, "rb") as fh:
        return pickle.load(fh)


# ---------------------------------------------------------------------------------------------- checkL1Claim
def coth_pow_up(n, d):
    """cothPowUp n δ (Step0/L1Model.lean)."""
    return (1 + 1 / (F(314, 100) * d)) ** n


def l1up(B, W, Cq, m):
    """l1Up W C m = supBound W ⟨m.deg, m.poly, upMul (ofRatUp C) m.rad⟩ (RouteAL1Bridge.lean)."""
    return M.supBound(B, W, M.Model(m.deg, m.poly, B.upMul(B.ofRatUp(Cq), m.rad)))


def weight(c, rho):
    """a `CertWeight` at rho passing `checkWeight` at the certificate's expHalvings and expOrder."""
    W = M.Weight(F(rho), FC.weight_for(F(rho), c.expHalvings, c.expOrder))
    assert M.checkWeight(W, c.expHalvings, c.expOrder)
    return W


def inv_models(c):
    """the 2n coordinate models of `invarianceModel` (as `checkInvariance`, cfgFull, d1 slots)."""
    B, n, W, pe = c.B, c.n, c.weight, c.piEnc
    ms = M.compose(B, n, c.jetOps, c.emb, c.wit, W, c.cfgFull, pe, [M.getD(c.jet["d1"], a) for a in range(n + n)])
    assert ms is not None
    DKm = C.dkModels(B, n, c.DKc)
    out = []
    for a in range(n + n):
        x = C.msGet(ms, C.swapNat(n, a), B)
        lhs = x if a < n else M.negM(B, x)
        out.append(M.addMixed(B, W, pe, lhs, M.negM(B, C.dkFreqModel(B, n, DKm, c.freqBox, c.params["s"], W,
                                                                      c.cfgFull, pe, a))))
    return ms, out


def sums(B, n, lv, col):
    """the sums of `sumsOk` (backend values): column sums over the 2n phase rows, or row sums over the n columns."""
    if col:
        return [M.sumUp(B, [lv(a, j) for a in range(n + n)]) for j in range(n)]
    return [M.sumUp(B, [lv(a, j) for j in range(n)]) for a in range(n + n)]


def up_claim(B, xs, rel=F(1, 10 ** 4), sig=5):
    """the least short rational b >= max(xs) (relative slack rel) with ble x (ofRatDown b) for every x."""
    b = FW.up_rel(max(B.val(x) for x in xs), rel, sig)
    while not all(B.ble(x, B.ofRatDown(b)) for x in xs):
        b = FW.up_rel(b, rel, sig)
    return b


def l1_claim(c, rho1, rhoT):
    """(the claim, the raw values): checkL1L, checkL1N, checkL1T, checkL1E of RouteAL1Facts.lean on c."""
    B, n, st = c.B, c.n, c.stages
    W1, WT = weight(c, rho1), weight(c, rhoT)
    C1, CT = coth_pow_up(n, c.params["rho"] - W1.rho), coth_pow_up(n, c.params["rho"] - WT.rho)
    L = st["L"]
    N = C.modelMatOmega(B, n, n, st["N0"])                    # frameNModels = modelMatOmega n n N0
    T = st["T"]
    lvL = lambda a, j: l1up(B, W1, C1, C.entry(L, a, j, B))
    lvN = lambda a, j: l1up(B, W1, C1, C.entry(N, a, j, B))
    rowsT = [M.sumUp(B, [l1up(B, WT, CT, C.entry(T, i, j, B)) for j in range(n)]) for i in range(n)]
    _, E = inv_models(c)
    eE = [l1up(B, W1, C1, m) for m in E]
    raw = dict(aE=eE, aLt=sums(B, n, lvL, True), nuK=sums(B, n, lvL, False), aNt=sums(B, n, lvN, True),
               nuN=sums(B, n, lvN, False), t1=rowsT)
    claim = {k: up_claim(B, v) for k, v in raw.items()}
    claim.update(W1=W1, WT=WT)
    vals = {k: [float(B.val(x)) for x in v] for k, v in raw.items()}
    return claim, dict(values=vals, coth=dict(C1=float(C1), CT=float(CT)))


# ---------------------------------------------------------------------------------------------- the entry (RouteAL1Q)
def entry_consts(p, E):
    """eCE, erate, eCDK, eCDw, econd of RouteAL1Q.lean at the StepQ p (a v2_q.Step) and the entry record E."""
    n = F(p.n)
    g = p.gb * p.d ** p.kap
    COm = 2 * (n - 1) * p.c * p.sLt
    CRed = n * max(p.sNt, p.sLt + 2 * p.sN)
    w = 2 * p.M1 * p.sLt * p.sK + (2 * n * p.sK + n * p.sLt)
    P = p.sK + p.sN
    CFr = (p.M1 * p.sK + n) * (1 + p.sB) + p.sN * ((p.sLt * p.M1 + 2 * n) * p.sK + p.sLt * (p.M1 * p.sK + n)) * p.sB
    tavg = min(p.t, E["tR"])
    cavg = min(p.ca * p.sLt, E["Gr"] * E["aN"] * g)
    CS = p.sT * max(p.sNt * g + tavg * cavg, g + cavg * p.HY)
    cN1 = E["G0"] * E["aN"] * g
    CXiN = CS + min(p.c * p.sLt, cN1)
    CXiN1 = CS + cN1
    CG = p.t * CXiN + p.Th * CS + p.sNt * g
    CXiL1 = E["G0"] * g * (E["t1"] * CXiN1 + p.Th * CS + E["aL"] * g)
    CXiL = min(p.c * CG, CXiL1)
    CXi = max(CXiL, g * CXiN)
    CDK = p.sK * CXiL + p.sN * g * CXiN
    COmK = min(COm, n * E["ei"] * E["G0"] * E["aN"] * g)
    CSym = max(F(1), p.sB ** 2) * COmK
    CDXi = max(CG, p.sLt * g)
    CLin = CRed * CXi + CSym * CDXi + p.Th * COmK * CS
    CdK = CFr * CXi + P * g * CDXi
    CE1 = 2 * P * (p.gb ** 2 * p.d ** (2 * p.kap - 1)) * CLin + p.M2 / 2 * CDK ** 2 + g * CS * CdK
    CE2 = p.gb * p.d ** (p.kap - 1) * n * (p.sLt * g + p.Th * COmK) * CXiL + p.Mh2 / 2 * CDK ** 2
    CE = max(CE1, CE2)
    fr = E.get("frame")
    if fr is not None:
        dL = min(n * CDK, E["ei"] * (fr[0] * CXiL1 + fr[1] * g * CXiN1))
        dLt = min(2 * n * CDK, 2 * n * E["ei"] * (fr[0] * CXiL1 + fr[1] * g * CXiN1))
    else:
        dL, dLt = n * CDK, 2 * n * CDK
    GrK = p.sLt * dL + p.sK * dLt
    rB = p.sB ** 2 * (p.sLt * dL + p.sK * dLt) / (1 - p.th)
    rN = p.sB * dL + p.sK * rB
    rNt = rB * p.sLt + p.sB * dLt
    CDw = p.Th * g * CS
    CDT0 = (2 * p.M1 * (rNt * p.sN + p.sNt * rN) + 2 * p.M2 * p.sNt * p.sN * p.d * CDK
            + p.sB ** 3 * w * (p.sK * dLt + p.sLt * dL) + 2 * n * p.sNt * p.sB * (p.gb ** 2 * p.d ** (2 * p.kap))
            + p.sB ** 3 * w * (COm + COmK) * g)
    CDT = max(CDT0 + CDw * p.d, n * CDw * p.d + 2 * n * p.sNt * (p.gb ** 2 * p.d ** (2 * p.kap)))
    rT = p.sT ** 2 / (1 - p.th) * CDT
    rate = [CDK, dL, rB, rT, dLt, rN, rNt, CDT, CDw]

    def econd(x):
        return (p.gb ** 4 * p.d ** (2 * (2 * p.kap) - 1) * x <= 1
                and max(F(1), p.sB ** 2) * COmK * (p.gb ** 3 * p.d ** (3 * p.kap - 1)) * x <= F(1, 2)
                and CE * x <= 1 and p.sT * CDT * (p.gb ** 2 * p.d ** (2 * p.kap - 1)) * x <= p.th
                and p.sB * GrK * (p.gb ** 2 * p.d ** (2 * p.kap - 1)) * x <= p.th)
    return dict(CE=CE, rate=rate, CDK=CDK, CDw=CDw, econd=econd)


class L1Run:
    """NumQ.okL1 and its sums (RouteAL1Run.lean): stage 0 the entry, every later stage C6's StepQ (v2_q)."""

    def __init__(self, Q, E):
        self.Q, self.E = Q, E
        self.e0 = entry_consts(Q.inp(0), E)

    def stCE(self, s):
        return self.e0["CE"] if s == 0 else self.Q.inp(s).CE

    def stRate(self, s, i):
        return self.e0["rate"][i] if s == 0 else self.Q.inp(s).rate[i]

    def stCD(self, s):
        return self.e0["CDK"] if s == 0 else self.Q.inp(s).CDK

    def stCp(self, s):
        return self.e0["CDw"] if s == 0 else self.Q.inp(s).CDw

    def xs(self, Xs):
        out = [Xs]
        for s in range(self.Q.kp):
            if isinstance(out[-1], float) and not (out[-1] < 1e100):
                out.append(float("inf"))
                continue
            out.append(F(2) ** (2 * (2 * self.Q.tau)) * self.stCE(s) * out[-1] ** 2)
        return out

    def sums(self, Xs):
        Q, xs = self.Q, self.xs(Xs)
        return [Q.sumQ(Q.gb, xs, lambda s, i=i: self.stRate(s, i), 2 * Q.tau - JI[i]) for i in range(9)]

    def okL1(self, cap, m0, Xs, detail=False):
        Q, E, xs = self.Q, self.E, self.xs(Xs)
        why = []
        if any(isinstance(x, float) and not (x < 1e300) for x in xs):
            return (False, ["overflow"]) if detail else False
        if not (Xs >= 0 and Q.kp >= 1 and wfB(E) and E["ei"] >= EI):
            why.append("guards")
        if not self.e0["econd"](xs[0]):
            why.append("J1 entry")
        for s in range(1, Q.kp + 1):
            if not Q.inp(s).condB(xs[s]):
                why.append("J1 stage %d" % s)
        if F(2) ** (2 * (2 * Q.tau)) * Q.inp(Q.kp).CE * xs[Q.kp] > 1:
            why.append("J2 tail")
        sm = self.sums(Xs)
        for i in range(9):
            if m0[i] + sm[i] > cap[i]:
                why.append("J3 " + V.CAP_NAMES[i])
        return (not why, why) if detail else not why

    def c2c3(self, Xs):
        Q, xs = self.Q, self.xs(Xs)
        den = Xs * Q.d0 ** (4 * Q.tau)
        c2 = Q.rho ** (2 * Q.tau) * Q.sumQ(F(1), xs, self.stCD, 2 * Q.tau) / den
        c3 = Q.rho ** (2 * Q.tau) * Q.sumQ(F(1), xs, self.stCp, 2 * Q.tau) / den
        return c2, c3


def wfB(E):
    ok = all(E[k] >= 0 for k in ("aN", "aL", "t1", "tR", "G0", "Gr", "ei"))
    fr = E.get("frame")
    return ok and (fr is None or (fr[0] > 0 and fr[1] > 0))


def finalL1(run, p, box, Xs):
    """finalL1 Q E p box Xs (RouteAL1Core.lean) on the strip Q.rho."""
    Q = run.Q
    c2, c3 = run.c2c3(Xs)
    return (p["err"] < Xs * p["gamma"] ** 4 * Q.d0 ** (4 * p["tau"])
            and max(c2, c3) * p["err"] <= p["disp"] * (p["gamma"] ** 2 * Q.rho ** (2 * p["tau"]))
            and p["disp"] < (p["som"] - p["s"]) * V.freqNormLo(box))


# ---------------------------------------------------------------------------------------------- Gamma_inf (gamOk)
def gam_wit(box, kappa, gamma, s, d, slack=1.002):
    """(FibWit (N, E1, claim), G) with gamOk box kappa gamma s d G w (c6l1_gamma, the exact mirror)."""
    (c0, r0), _ = box
    w1 = float(c0 / kappa)
    gfib = G6.gamma_float(w1, float(d), K=int(4 / float(d)) + 10)
    E1 = G6.min_E1(d, 6)
    claim = F(math.ceil(gfib * slack * 10 ** 6), 10 ** 6)
    g = gamma / kappa
    for _ in range(40):
        N = 1
        while not (1 <= F(628, 100) * d * (N + 1) and (N + 1) * E1 ** (N + 1) <= claim * (F(628, 100) * g)):
            N += 1
        if G6.fibCheck(c0 / kappa, r0 / kappa, g, d, N, E1, claim):
            break
        claim = FW.up_rel(claim * F(101, 100), F(0), 7)
    else:
        raise RuntimeError("no fibered witness at delta %s" % d)
    G = FW.up_rel(claim / (s * kappa), F(1, 10 ** 6), 6)
    assert G6.gamOk(box, kappa, gamma, s, d, G, N, E1, claim)
    return dict(N=N, E1=E1, claim=claim), G, gfib


# ---------------------------------------------------------------------------------------------- the witness
def run_at(p1, box, R, sd, kp, th, J, Xs, E):
    """(L1Run, caps witness) at X*: tight caps (v2_r2.solve_caps on the L1 sums)."""
    d0 = min(F(1), (p1["rho"] - p1["rhoInf"]) / 6)
    Q0 = V.Num(n=2, tau=1, rho=p1["rho"], rhoInf=p1["rhoInf"], kp=kp)
    c = [sd[("d", s)] for s in range(kp)]
    cbar = [sd[("b", s)] for s in range(kp)]
    ctail = V.classical_c(2, 1, J, Q0.delta(kp))
    base = dict(Xs=Xs, kp=kp, th=th, c=c, cbar=cbar, ctail=ctail, J=J, R=R)
    m0 = V.initQ(R["bL"], R["bN"], R["bNt"], R["bT"], p1["sK"], p1["sB"], p1["sT"], p1["mu"])

    def mk(caps):
        w = dict(base, sB=caps[2], sT=caps[3], sLt=caps[4], sN=caps[5], sNt=caps[6], t=caps[7])
        return L1Run(V.refined_num(w, 2, p1, box), E)
    caps = R2.solve_caps(mk, m0, Xs, None)
    if caps is None:
        return None, None, m0
    w = dict(base, sB=caps[2], sT=caps[3], sLt=caps[4], sN=caps[5], sNt=caps[6], t=caps[7])
    assert d0 == Q0.d0
    return L1Run(V.refined_num(w, 2, p1, box), E), w, m0


def _fl(d):
    return {k: (float(v) if isinstance(v, F) else (tuple(float(x) for x in v) if isinstance(v, tuple) else v))
            for k, v in d.items()}


def passes(p1, box, R, sd, kp, th, J, Xs, E, detail=False, fl=False, final=True):
    """okL1 at tight caps, wfOk, the classical tail and (final) finalL1; fl: in floating point (only to locate X*;
    without `final` the test is monotone in X*, as v2_r2.max_Xs's)."""
    if fl:
        p1, R, sd, E, th, Xs = _fl(p1), _fl(R), _fl(sd), _fl(E), float(th), float(Xs)
        box = [(float(a), float(b)) for a, b in box]
    run, w, m0 = run_at(p1, box, R, sd, kp, th, J, Xs, E)
    if run is None:
        return (False, ["caps diverge"], None) if detail else False
    ok, why = run.okL1(V.capQ(run.Q, p1["mu"], p1["nu"]), m0, Xs, detail=True)
    wf = run.Q.wfOk()
    tail = V.classicalOk(2, 1, J, run.Q.delta(kp), run.Q.ctail)
    fin = finalL1(run, p1, box, Xs) if final else True
    ok = ok and wf and tail and fin
    why = why + ([] if wf else ["wf"]) + ([] if tail else ["tail"]) + ([] if fin else ["finalL1"])
    return (ok, why, w) if detail else ok


def max_Xs(p1, box, R, sd, kp, th, J, E, lo=-10.0, hi=8.0, steps=40):
    for _ in range(steps):
        mid = (lo + hi) / 2
        if passes(p1, box, R, sd, kp, th, J, V.up(10 ** mid, 3), E, fl=True, final=False):
            lo = mid
        else:
            hi = mid
    Xs = F(int(10 ** (lo - math.floor(lo)) * 100), 100) * F(10) ** math.floor(lo)
    while not passes(p1, box, R, sd, kp, th, J, Xs, E, final=False):
        Xs = Xs * F(99, 100)
    return Xs


def sites_at(tag, p1, box, kp, J):
    """the certified sites of the bites of the strip p1['rho'] (Lean balCheck), with the classical constant where none
    is found; (the site dict for the mirror, the Lean site list)."""
    kappa = box[1][0]
    Q0 = V.Num(n=2, tau=1, rho=p1["rho"], rhoInf=p1["rhoInf"], kp=kp)
    bites = sorted({Q0.delta(s) for s in range(kp)} | {Q0.b(s) for s in range(kp)})
    found = FW.site_search(tag, bites, kappa, p1["gamma"])
    sd, slist = {}, []
    for s in range(kp):
        a, b = found.get(Q0.delta(s)), found.get(Q0.b(s))
        sd[("d", s)] = a["c"] if a else V.classical_c(2, 1, J, Q0.delta(s))
        sd[("b", s)] = b["c"] if b else V.classical_c(2, 1, J, Q0.b(s))
        slist.append((a, b))
    return sd, slist


def l1_witness(c, tag, rho1, kp=3, th=F(1, 8), J=20, log=print):
    p = dict(c.params)
    box = c.freqBox
    kappa = box[1][0]
    R, _ = FW.refined_claim(c)
    p1 = dict(p, rho=F(rho1))
    d0 = min(F(1), (p1["rho"] - p1["rhoInf"]) / 6)
    rhoT = p1["rho"] - d0                                   # entryOk: Q.rho - Q.delta 0 <= WT.rho
    L, lraw = l1_claim(c, p1["rho"], rhoT)
    log("l1 claim", {k: (float(v) if isinstance(v, F) else (float(v.rho), float(v.w))) for k, v in L.items()})
    g0, G0, g0f = gam_wit(box, kappa, p["gamma"], p["s"], d0)
    gr, Gr, grf = gam_wit(box, kappa, p["gamma"], p["s"], p1["rho"])
    log("Gamma_inf: delta0' %.4g (float %.4g), rho1 %.4g (float %.4g)" % (float(G0), g0f, float(Gr), grf))
    E = dict(aN=FW.up_rel(L["aLt"] * L["aE"] / p["err"], F(1, 10 ** 6), 6),
             aL=FW.up_rel(L["aNt"] * L["aE"] / p["err"], F(1, 10 ** 6), 6),
             t1=L["t1"], tR=R["bT"], G0=G0, Gr=Gr, frame=(L["nuK"], L["nuN"]), ei=EI)
    assert L["aLt"] * L["aE"] <= E["aN"] * p["err"] and L["aNt"] * L["aE"] <= E["aL"] * p["err"]
    sd, slist = sites_at(tag, p1, box, kp, J)
    log("sites", {k: float(v) for k, v in sd.items()})
    Xs = max_Xs(p1, box, R, sd, kp, th, J, E)
    ok, why, w = passes(p1, box, R, sd, kp, th, J, Xs, E, detail=True)
    assert ok, why
    _, why_up, _ = passes(p1, box, R, sd, kp, th, J, Xs * F(11, 10), E, detail=True)
    # the same run without the l1 entry (C6's refined run on the same strip, same sites): its X*
    Xs_ref = R2.max_Xs("refined", p1, box, kp, th, J, R, sd, lo=-10.0, hi=8.0, steps=40)
    estar = Xs * p["gamma"] ** 4 * d0 ** 4
    log("l1 entry at rho1 = %s: X* %s (refined at the same strip %s), e* %.3e, err %.3e, binding at 1.1 X*: %s" % (
        rho1, Xs, Xs_ref, float(estar), float(p["err"]), why_up))
    return dict(core=w, R=R, kappa=kappa, sites=slist, L=L, E=E, g0=g0, gr=gr, Xs=Xs, Xs_refined=Xs_ref,
                estar=estar, estar_refined=Xs_ref * p["gamma"] ** 4 * d0 ** 4, binding=why_up, rho1=F(rho1),
                rhoT=rhoT, l1_raw=lraw)


# ---------------------------------------------------------------------------------------------- Lean terms
def lean_weight(W):
    return "⟨%s, %s⟩" % (FL.lq(W.rho), FL.lq(W.w))


def lean_l1_claim(L):
    q = FL.lq
    return ("{ W1 := %s, WT := %s, aE := %s, aLt := %s, aNt := %s, nuK := %s, nuN := %s, t1 := %s }" % (
        lean_weight(L["W1"]), lean_weight(L["WT"]), q(L["aE"]), q(L["aLt"]), q(L["aNt"]), q(L["nuK"]),
        q(L["nuN"]), q(L["t1"])))


def lean_entry(E):
    q = FL.lq
    fr = "some (%s, %s)" % (q(E["frame"][0]), q(E["frame"][1])) if E.get("frame") else "none"
    return ("{ aN := %s, aL := %s, t1 := %s, tR := %s, G0 := %s, Gρ := %s, frame := %s, ei := %s }" % (
        q(E["aN"]), q(E["aL"]), q(E["t1"]), q(E["tR"]), q(E["G0"]), q(E["Gr"]), fr, q(E["ei"])))


def lean_fib(g):
    return "⟨%d, %s, %s⟩" % (g["N"], FL.lq(g["E1"]), FL.lq(g["claim"]))


def lean_l1_wit(W):
    base = FW.lean_refined_wit(dict(core=W["core"], R=W["R"], kappa=W["kappa"], sites=W["sites"]))
    return "{ base := %s, L := %s, E := %s, g0 := %s, gρ := %s }" % (
        base, lean_l1_claim(W["L"]), lean_entry(W["E"]), lean_fib(W["g0"]), lean_fib(W["gr"]))


def check_in_lean(tag, W):
    """the compiled Lean `l1Core` and its parts (ℚ-level; the model-level checkL1Claim is the kernel's)."""
    prelude = "def wL : KAM.CertificateSharp.V2.L1.L1Wit := %s" % lean_l1_wit(W)
    P, Bx = "%s.cert.params" % tag, "%s.cert.freqBox" % tag
    Q = "(wL.num 2 %s %s)" % (P, Bx)
    exprs = [
        "KAM.CertificateSharp.V2.L1.l1Core 2 %s %s wL" % (P, Bx),
        "%s.wfOk" % Q,
        ("KAM.CertificateSharp.V2.L1.okL1 %s wL.E (KAM.CertificateSharp.V2.capQ %s %s.μ %s.nuRay) "
         "(KAM.CertificateSharp.V2.initQ wL.base.R.bL wL.base.R.bN wL.base.R.bNt wL.base.R.bT %s.σK %s.σB %s.σT "
         "%s.μ) wL.base.core.Xs") % (Q, Q, P, P, P, P, P, P),
        "KAM.CertificateSharp.V2.sitesOk %s wL.base.core.J %s wL.base.κ %s.γ wL.base.sites" % (Q, Bx, P),
        "KAM.CertificateSharp.V2.L1.entryOk 2 %s %s %s wL" % (Q, P, Bx),
        "KAM.CertificateSharp.V2.L1.finalL1 %s wL.E %s %s wL.base.core.Xs" % (Q, P, Bx),
        "KAM.CertificateSharp.V2.checkHamClaim %s.cert wL.base.R" % tag,
    ]
    outs = FL.lean_eval([MOD + tag + "Data", "KAM.CertificateSharp.V2.RouteAll"],
                        ["KAM.CertificateSharp.V2.Forced", "KAM.Certificate"], exprs, prelude=prelude)
    return dict(zip(["l1Core", "wfOk", "okL1", "sitesOk", "entryOk", "finalL1", "checkHamClaim"],
                    [FL.parse_bool(o) for o in outs]))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("tag", nargs="?", default="Tiny")
    ap.add_argument("--rho1", default="1/10")
    ap.add_argument("--json", default=None)
    ap.add_argument("--no-lean", action="store_true")
    a = ap.parse_args()
    c = ensure(a.tag)
    W = l1_witness(c, a.tag, F(a.rho1))
    print(lean_l1_wit(W))
    if not a.no_lean:
        r = check_in_lean(a.tag, W)
        print("compiled Lean:", r)
        assert all(r.values()), r
    if a.json:
        with open(a.json, "w") as fh:
            json.dump(report(W), fh, indent=1, sort_keys=True, default=str)


def report(W):
    """the witness and the mirror's numbers, JSON-ready."""
    L = dict((k, v) for k, v in W["L"].items() if k not in ("W1", "WT"))
    L.update(W1=[W["L"]["W1"].rho, W["L"]["W1"].w], WT=[W["L"]["WT"].rho, W["L"]["WT"].w])
    d = dict((k, v) for k, v in W.items() if k != "L")
    d["L"] = L
    d["lean"] = lean_l1_wit(W)
    return FW.jsonable(d)


if __name__ == "__main__":
    main()
