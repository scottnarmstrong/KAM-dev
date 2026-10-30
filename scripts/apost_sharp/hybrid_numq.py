#!/usr/bin/env python3
"""Exact rational port of the v2 certifier's route-A' numbers (package SHARP2-C8D).

Untrusted tooling.  A literal port, in Fractions with no float in any predicate, of
  * `StepQ` and its constants (KAM/CertificateSharp/V2/RouteAQ.lean);
  * `NumQ` (`δ0`, `δ`, `r`, `b`, `cS`, `caS`, `dS`, `inp`, `x`, `sumQ`, `wfOk`, `c2Q`, `c3Q`) (same file);
  * `StepQ.rAb`, `bLoc0`, `bLoc`, `cond0`, `rateR` and `NumQ.bLocS`, `condR`, `okR`, `budgetOk`
    (KAM/CertificateSharp/V2/RouteAQRef.lean); `jRI` (KAM/Iso/Sharp2/RouteA/Ref/Scheme.lean);
  * `capRQ`, `initRQ`, `refinedCoreR` without its two small-divisor certificates `sitesOk`, `classicalOk`
    (KAM/CertificateSharp/V2/RouteARefinedRef.lean); `FrozenWit.num`, `RefinedWit.num`
    (V2/RouteAFrozen.lean, V2/RouteARefined.lean); `finalOkA`, `boxNormUp` (V2/RouteACore.lean);
    `freqNormLo` (KAM/Certificate/Defs.lean).
The small-divisor sites are certified by their own `decide`s; this port takes their constants as given.

`validate()` reproduces the kernel facts of the repository: `r1_refinedCoreR` (passes at e = 155/10^13 with X* = 161000,
kernel-tests/CertificateSharp/V2/RefinedRefR1.lean), `r1R_final_rejects` (fails at 156/10^13), `toyCert2_refinedCoreR`
and `toyCert2_refinedCoreR_rejects` (KAM/CertificateSharp/V2/Tests/RefinedRef.lean).

Usage:  python3 -I scripts/apost_sharp/hybrid_numq.py      (runs validate())
"""
from fractions import Fraction as F

H = F(1, 2)
JRI = [0, 1, 1, 1, 1, 1, 1, 0]


# ============================================================================================ StepQ
class StepQ:
    """The rational inputs of one bite (RouteAQ.lean `StepQ`); the constants are cached properties."""

    def __init__(self, **kw):
        for k in ("n", "kap", "M1", "M2", "sK", "sB", "sT", "sLt", "sN", "sNt", "t", "c", "ca", "gb", "d", "th",
                  "Th", "HY", "Mh2"):
            setattr(self, k, kw[k])
        p = self
        n = F(p.n)
        p.g = p.gb * p.d ** p.kap
        p.COm = 2 * (n - 1) * p.c * p.sLt
        p.CSym = max(F(1), p.sB ** 2) * p.COm
        p.CRed = n * max(p.sNt, p.sLt + 2 * p.sN)
        p.w = 2 * p.M1 * p.sLt * p.sK + (2 * n * p.sK + n * p.sLt)
        p.CS = p.sT * max(p.sNt * p.g + p.t * p.ca * p.sLt, p.g + p.ca * p.HY * p.sLt)
        p.CXiN = p.CS + p.c * p.sLt
        p.CG = p.t * p.CXiN + p.Th * p.CS + p.sNt * p.g
        p.CDXi = max(p.CG, p.sLt * p.g)
        p.CXi = max(p.c * p.CG, p.g * p.CXiN)
        p.CDK = p.sK * p.c * p.CG + p.sN * p.g * p.CXiN
        p.CLin = p.CRed * p.CXi + p.CSym * p.CDXi + p.Th * p.COm * p.CS
        p.P = p.sK + p.sN
        p.CDw = p.Th * p.g * p.CS
        p.CFr = (p.M1 * p.sK + n) * (1 + p.sB) + \
            p.sN * ((p.sLt * p.M1 + 2 * n) * p.sK + p.sLt * (p.M1 * p.sK + n)) * p.sB
        p.CdK = p.CFr * p.CXi + p.P * p.g * p.CDXi
        p.CE1 = 2 * p.P * (p.gb ** 2 * p.d ** (2 * p.kap - 1)) * p.CLin + p.M2 / 2 * p.CDK ** 2 + \
            p.g * p.CS * p.CdK
        p.CE2 = p.gb * p.d ** (p.kap - 1) * n * (p.sLt * p.g + p.Th * p.COm) * p.c * p.CG + \
            p.Mh2 / 2 * p.CDK ** 2
        p.CE = max(p.CE1, p.CE2)
        p.CGr = n * p.sLt + 2 * n * p.sK
        p.CB = p.sB ** 2 * p.CGr / (1 - p.th)
        p.CNd = n * p.sB + p.sK * p.CB
        p.CNtd = p.CB * p.sLt + 2 * n * p.sB
        p.CDab = 2 * p.M1 * (p.CNtd * p.sN + p.sNt * p.CNd) + 2 * p.M2 * p.sNt * p.sN * p.d
        # RouteAQRef.lean
        p.rAb = max(p.CDab * p.CDK + p.CDw * p.d, n * p.CDw * p.d)
        p.rateR = [p.CDK, n * p.CDK, p.CB * p.CDK, p.rAb, 2 * n * p.CDK, p.CNd * p.CDK, p.CNtd * p.CDK, p.CDw]

    def bLoc0(self, ch):
        p, n = self, F(self.n)
        return (n * p.sNt * p.sB * (p.gb ** 4 * p.d ** (2 * (2 * p.kap) - 1)) +
                2 ** (p.kap + 1) * p.sB ** 3 * p.w * (2 * (n - 1) * ch * p.sLt) * (p.gb ** 3 * p.d ** (3 * p.kap - 1)))

    def bLoc(self, ch):
        p, n = self, F(self.n)
        return max(self.bLoc0(ch), n * p.sNt * (p.gb ** 4 * p.d ** (2 * (2 * p.kap))))

    def cond0(self, x):
        p = self
        return (p.gb ** 4 * p.d ** (2 * (2 * p.kap) - 1) * x <= 1 and
                p.CSym * (p.gb ** 3 * p.d ** (3 * p.kap - 1)) * x <= H and
                p.CE * x <= 1 and
                p.sB * p.CGr * p.CDK * (p.gb ** 2 * p.d ** (2 * p.kap - 1)) * x <= p.th)

    def cond0_slack(self, x):
        """the smallest relative slack of the four conditions (>= 0 iff cond0)."""
        p = self
        terms = [(p.gb ** 4 * p.d ** (2 * (2 * p.kap) - 1) * x, F(1)),
                 (p.CSym * (p.gb ** 3 * p.d ** (3 * p.kap - 1)) * x, H),
                 (p.CE * x, F(1)), (p.sB * p.CGr * p.CDK * (p.gb ** 2 * p.d ** (2 * p.kap - 1)) * x, p.th)]
        return min(1 - a / b for a, b in terms)


# ============================================================================================ NumQ
class NumQ:
    """`NumQ` (RouteAQ.lean) with `okR`, `budgetOk` (RouteAQRef.lean)."""

    FIELDS = ("n", "tau", "rho", "rhoinf", "M1", "M2", "sK", "sB", "sT", "sLt", "sN", "sNt", "t", "th", "gb", "c",
              "cbar", "ctail", "kp", "Th", "HY", "Mh2")

    def __init__(self, **kw):
        for k in self.FIELDS:
            setattr(self, k, kw[k])
        self.delta0 = min(F(1), (self.rho - self.rhoinf) / (2 * 3))
        self._inp = {}

    def getc(self, s):
        return self.c[s] if s < len(self.c) else F(0)

    def getcbar(self, s):
        return self.cbar[s] if s < len(self.cbar) else F(0)

    def delta(self, s):
        return H ** s * self.delta0

    def r(self, s):
        return self.rho - 2 * 3 * self.delta0 * (1 - H ** s)

    def b(self, s):
        return min(self.r(s), F(1))

    def cS(self, s):
        return self.getc(s) if s < self.kp else self.ctail

    def caS(self, s):
        return self.getcbar(s) * (self.delta(s) / self.b(s)) ** self.tau if s < self.kp else self.ctail

    def dS(self, s):
        return self.delta(min(s, self.kp))

    def inp(self, s):
        if s not in self._inp:
            self._inp[s] = StepQ(n=self.n, kap=self.tau, M1=self.M1, M2=self.M2, sK=self.sK, sB=self.sB,
                                 sT=self.sT, sLt=self.sLt, sN=self.sN, sNt=self.sNt, t=self.t, c=self.cS(s),
                                 ca=self.caS(s), gb=self.gb, d=self.dS(s), th=self.th, Th=self.Th, HY=self.HY,
                                 Mh2=self.Mh2)
        return self._inp[s]

    def xs(self, Xs):
        out = [Xs]
        for s in range(self.kp):
            out.append(2 ** (2 * (2 * self.tau)) * self.inp(s).CE * out[-1] ** 2)
        return out

    def sumQ(self, g, xs, rate, e):
        tot = sum(rate(t) * xs[t] * (g ** 2 * self.delta(t) ** e) for t in range(self.kp))
        return tot + 2 * rate(self.kp) * xs[self.kp] * (g ** 2 * self.delta(self.kp) ** e)

    def bLocS(self, s):
        return self.inp(s).bLoc(self.cS(s + 1))

    def condR(self, bF, s, x):
        return self.inp(s).cond0(x) and self.bLocS(s) * x <= bF

    def okR(self, bF, sig, m0, Xs, detail=False):
        if Xs < 0:
            return (False, "Xs < 0") if detail else False
        xs = self.xs(Xs)
        for s in range(self.kp + 1):
            if not self.condR(bF, s, xs[s]):
                return (False, "condR at stage %d" % s) if detail else False
        if not 2 ** (2 * (2 * self.tau)) * self.inp(self.kp).CE * xs[self.kp] <= 1:
            return (False, "tail J2") if detail else False
        for i in range(8):
            used = self.sumQ(self.gb, xs, lambda s, i=i: self.inp(s).rateR[i], 2 * self.tau - JRI[i])
            if not m0[i] + used <= sig[i]:
                return (False, "J3 cap %d" % i) if detail else False
        return (True, "") if detail else True

    def budgetOk(self, mT, iH, bF, bT):
        return (0 < mT and mT < self.sT and bT + 2 * bF <= (self.sT - mT) / (self.sT * mT) and
                iH + bT + 2 * bF <= self.t)

    def wfOk(self):
        return (2 <= self.n and 1 <= self.tau and 0 < self.rhoinf and self.rhoinf < self.rho and 0 <= self.M1 and
                0 <= self.M2 and 0 < self.sK and 0 < self.sB and 0 < self.sT and 0 <= self.sLt and 0 <= self.sN and
                0 <= self.sNt and 0 <= self.t and 0 < self.th and self.th < 1 and 0 < self.gb and
                all(a >= 0 for a in self.c) and all(a >= 0 for a in self.cbar) and 0 <= self.ctail and
                0 <= self.Th and 0 <= self.HY and 0 <= self.Mh2)

    def c2Q(self, Xs):
        xs = self.xs(Xs)
        return (self.rho ** (2 * self.tau) * self.sumQ(F(1), xs, lambda s: self.inp(s).CDK, 2 * self.tau) /
                (Xs * self.delta0 ** (4 * self.tau)))

    def c3Q(self, Xs):
        xs = self.xs(Xs)
        return (self.rho ** (2 * self.tau) * self.sumQ(F(1), xs, lambda s: self.inp(s).CDw, 2 * self.tau) /
                (Xs * self.delta0 ** (4 * self.tau)))


# ============================================================================================ the witnesses
def box_norm_up(box):
    return max([abs(c) + r for c, r in box] + [F(0)])


def freq_norm_lo(box):
    return max([abs(c) - r for c, r in box] + [F(0)])


def refined_num(n, p, box, w):
    """`RefinedWit.num` of `FrozenWit.num` (p: CertParams dict, w: RefinedWit dict with `core`, `R`)."""
    core, R = w["core"], w["R"]
    return NumQ(n=n, tau=p["tau"], rho=p["rho"], rhoinf=p["rhoInf"], M1=R["dx"], M2=R["d2x"], sK=p["sK"] - p["mu"] / 2,
                sB=core["sB"], sT=core["sT"], sLt=core["sLt"], sN=core["sN"], sNt=core["sNt"], t=core["t"],
                th=core["th"], gb=p["gbar"], c=core["c"], cbar=core["cbar"], ctail=core["ctail"], kp=core["kp"],
                Th=p["sigma_omega"] * box_norm_up(box), HY=R["dh"] * core["sN"], Mh2=R["d2h"])


def cap_rq(Q, mu, nu, bT):
    return [mu / 2, Q.sK, Q.sB, bT, Q.sLt, Q.sN, Q.sNt, nu / 2]


def init_rq(iLt, iN, iNt, sK, sB, mu):
    return [F(0), sK - mu, sB - mu, F(0), iLt, iN, iNt, F(0)]


def final_ok_a(Q, p, box, Xs, detail=False):
    a = p["err"] < Xs * p["gamma"] ** 4 * Q.delta0 ** (4 * p["tau"])
    b = max(Q.c2Q(Xs), Q.c3Q(Xs)) * p["err"] <= p["disp"] * (p["gamma"] ** 2 * p["rho"] ** (2 * p["tau"]))
    c = p["disp"] < (p["sigma_omega"] - p["s"]) * freq_norm_lo(box)
    return (a and b and c, dict(small=a, disp=b, ray=c)) if detail else (a and b and c)


def refined_core_r(n, p, box, wR, detail=False):
    """`refinedCoreR` without `sitesOk` and `classicalOk` (certified separately)."""
    w = wR["base"]
    Q = refined_num(n, p, box, w)
    Xs, R = w["core"]["Xs"], w["R"]
    parts = dict(Xs_pos=Xs > 0, wf=Q.wfOk(),
                 okR=Q.okR(wR["bF"], cap_rq(Q, p["mu"], p["nuRay"], wR["bT"]),
                           init_rq(R["bL"], R["bN"], R["bNt"], p["sK"], p["sB"], p["mu"]), Xs),
                 budget=Q.budgetOk(p["sT"] - p["mu"], R["bT"], wR["bF"], wR["bT"]),
                 final=final_ok_a(Q, p, box, Xs))
    ok = all(parts.values())
    return (ok, parts) if detail else ok


def max_xs(n, p, box, wR, lo=F(1), hi=None, steps=60):
    """the largest X* (on a rational bisection) with Xs_pos, okR (J1-J3 at X*): the threshold of the run is
    X* gamma^4 delta0^(4 tau) (the comparison of `finalOkA`)."""
    w = wR["base"]
    Q = refined_num(n, p, box, w)
    R = w["R"]
    sig = cap_rq(Q, p["mu"], p["nuRay"], wR["bT"])
    m0 = init_rq(R["bL"], R["bN"], R["bNt"], p["sK"], p["sB"], p["mu"])
    ok = lambda X: Q.okR(wR["bF"], sig, m0, X)
    if not ok(lo):
        lo = F(1, 10 ** 6)
        while not ok(lo) and lo > F(1, 10 ** 60):
            lo /= 1000
        if not ok(lo):
            return F(0), Q
    hi = hi or lo * 2
    while ok(hi):
        lo, hi = hi, hi * 2
    for _ in range(steps):
        mid = (lo + hi) / 2
        mid = F(round(mid.numerator * 10 ** 12 // mid.denominator), 10 ** 12) if mid > 1 else mid
        if mid <= lo or mid >= hi:
            break
        if ok(mid):
            lo = mid
        else:
            hi = mid
    return lo, Q


# ============================================================================================ repository data
R1_KAPPA = F(7, 4) / (1 + F(1, 10 ** 6))
R1_CLAIM = dict(dh=F(105, 100) * F(18228, 10000), dx=F(105, 100) * F(175, 100), d2x=F(105, 100) * F(10342, 10000),
                d2h=F(105, 100) * F(18323, 10000), bL=F(105, 100) * F(13268, 10000), bN=F(105, 100) * F(13540, 10000),
                bNt=F(105, 100) * F(13787, 10000), bT=F(105, 100) * F(33130, 10000))
R1_BOX = [(-(79 - F(2236067977, 1000000000)) / 3118 * R1_KAPPA, F(1, 10 ** 12)), (R1_KAPPA, F(0))]


def r1_params(err, disp):
    """`r1Params` (KAM/CertificateSharp/V2/Tests/Frozen.lean): the design package R1."""
    return dict(tau=1, rho=F(1, 70), rhoInf=F(1, 70000), M=F(1924, 1000), sK=F(105, 100) * F(1303, 1000) + F(1, 160),
                sB=F(105, 100) * F(1833, 1000) + F(1, 160), sT=F(105, 100) * F(1022, 1000) / F(7, 4) + F(1, 160),
                mu=F(1, 160), gbar=R1_KAPPA / 42, sigma_omega=F(2), nuRay=F(1, 10 ** 6), gamma=R1_KAPPA / 42,
                s=1 + F(1, 10 ** 6), err=err, E0=F(0), disp=disp)


R1_WIT_R = dict(  # r1RefinedWitR (kernel-tests/CertificateSharp/V2/RefinedRefR1.lean); sites: certified there
    base=dict(core=dict(Xs=F(161000), kp=5, th=F(1, 200),
                        c=[F(2978, 10 ** 6), F(2912, 10 ** 6), F(2900, 10 ** 6), F(2938, 10 ** 6), F(2939, 10 ** 6)],
                        cbar=[F(6745, 10 ** 6), F(4018, 10 ** 6), F(3122, 10 ** 6), F(2938, 10 ** 6),
                              F(2906, 10 ** 6)],
                        ctail=F(4071, 50000), sB=F(19294169, 10000000), sT=F(65, 100), sLt=F(13937561, 10000000),
                        sN=F(1428831, 1000000), sNt=F(7277337, 5000000), t=F(356, 100), J=4),
              R=R1_CLAIM, kappa=R1_KAPPA, sites="r1RefinedWitR.base.sites (certified per bite)"),
    bF=F(1177, 5000000), bT=F(99089, 1250000))

TOY_NU = F(6082472135954999579392818347337462552470881, 6236 * 10 ** 39)
TOY_PARAMS = dict(tau=1, rho=F(9), rhoInf=F(1), M=F(297, 100), sK=F(297, 100), sB=F(297, 100), sT=F(297, 100),
                  mu=F(1, 100), gbar=F(1, 42), sigma_omega=F(3), nuRay=F(49, 100), gamma=F(1, 42), s=F(2),
                  err=F(1, 3118 * 10 ** 39), E0=F(0), disp=F(94223, 5 * 10 ** 30))
TOY_BOX = [(F(6082472135954999579392818347337462552470881, 12472 * 10 ** 39), F(1, 12472 * 10 ** 39)),
           (F(1, 2), F(0))]
TOY_WIT_R = dict(  # toyRefinedWitR (KAM/CertificateSharp/V2/Tests/RefinedRef.lean, Refined.lean)
    base=dict(core=dict(Xs=F(1, 10 ** 30), kp=2, th=F(1, 8), c=[F(1, 5000), F(3, 500)], cbar=[F(1, 5000), F(1, 5000)],
                        ctail=F(111, 1000), sB=F(3), sT=F(3), sLt=F(11, 10), sN=F(11, 10), sNt=F(11, 10),
                        t=F(11, 10), J=2),
              R=dict(dh=F(2), dx=F(101, 100), d2x=F(1, 100), d2h=F(101, 100), bL=F(101, 100), bN=F(101, 100),
                     bNt=F(101, 100), bT=F(101, 100)),
              kappa=F(1, 2), sites="toyRefinedWit.sites (certified per bite)"),
    bF=F(1, 1000), bT=F(1, 1000))


def validate(log=print):
    """reproduce the kernel facts; returns True if all agree."""
    ok = True
    r, parts = refined_core_r(2, r1_params(F(155, 10 ** 13), F(1, 300)), R1_BOX, R1_WIT_R, detail=True)
    log("r1_refinedCoreR at e = 155/10^13: %s %s (kernel: true)" % (r, parts)); ok &= r
    Q = refined_num(2, r1_params(F(156, 10 ** 13), F(1, 300)), R1_BOX, R1_WIT_R["base"])
    f = final_ok_a(Q, r1_params(F(156, 10 ** 13), F(1, 300)), R1_BOX, F(161000))
    log("r1R_final_rejects at e = 156/10^13: finalOkA = %s (kernel: false)" % f); ok &= not f
    r, parts = refined_core_r(2, TOY_PARAMS, TOY_BOX, TOY_WIT_R, detail=True)
    log("toyCert2_refinedCoreR: %s %s (kernel: true)" % (r, parts)); ok &= r
    rej = dict(TOY_WIT_R, bT=F(1, 100))
    r = refined_core_r(2, TOY_PARAMS, TOY_BOX, rej)
    log("toyCert2_refinedCoreR_rejects (bT = 1/100): %s (kernel: false)" % r); ok &= not r
    log("validate: %s" % ("PASS" if ok else "FAIL"))
    return ok


if __name__ == "__main__":
    validate()
