#!/usr/bin/env python3
"""SO-V2PKG: exact rational mirror of the v2 route-A tests (untrusted tooling).

Transcribes, over Fraction, with the Lean names:
  KAM/CertificateSharp/V2/RouteAQ.lean      StepQ (g, COm, ..., CE, CDT, rT, condB, rateQ), NumQ (delta0, delta, r, b,
                                            cS, caS, dS, inp, x, sumQ, okB, wfOk, c2Q, c3Q)
  KAM/CertificateSharp/V2/RouteACore.lean   capQ, initQ, finalOk, finalOkA, boxNormUp
  KAM/CertificateSharp/V2/RouteAFrozen.lean FrozenWit.num, defaultInitQ, torsionCoefQ, torsionCapOk, classicalListOk,
                                            frozenCore
  KAM/CertificateSharp/V2/ClassicalQ.lean   zetaUp, shellUp, epsUp, radUp, classicalOk
  KAM/CertificateSharp/V2/RouteARefined.lean RefinedWit.num, refinedCore (sites: certified constants are taken from
                                            the float c_freq x margin, see `site_c`; the Lean biteOk is NOT mirrored)
and reuses sharp_q.py (the transcription of ConstantsQ.lean, cross-checked by the kernel at R2) for C2#, C3#, cRRQ.

A run is a dict `w` with the FrozenWit fields (Xs, kp, th, c, cbar, ctail, sB, sT, sLt, sN, sNt, t, J) and, for the
refined test, `R` (dh, dx, d2x, d2h, bL, bN, bNt, bT).  `p` is a CertParams dict (g3_r2.R2 shape: tau rho rhoInf M
sK sB sT mu gbar som nu gamma s err disp), `box` a list of (centre, radius) pairs.
"""
import math
from fractions import Fraction as F
import sharp_q as SQ

# ----------------------------------------------------------------------------------------------- ClassicalQ
PI_LO, PI_UP, E_LO = F(3141592, 10 ** 6), F(3141593, 10 ** 6), F(2718281, 10 ** 6)


def zetaUp(a, J):
    return sum(1 / (F(a) + j) ** 2 for j in range(J)) + 1 / (F(a) + J - F(1, 2))


def shellUp(tau, J):
    return F(2) ** (2 * tau + 1) * zetaUp(F(2) ** tau, J)


def epsUp(tau, d):
    return 4 * PI_UP * d * (2 * F(tau) / E_LO) ** (2 * tau) / math.factorial(2 * tau)


def radUp(n, tau, J, d):
    return F(2) ** n * (shellUp(tau, J) * math.factorial(2 * tau) * (1 + epsUp(tau, d)))


def classicalOk(n, tau, J, d, c):
    return c > 0 and radUp(n, tau, J, d) <= (c * (2 * PI_LO) * (4 * PI_LO) ** tau) ** 2


def up(x, sig=7):
    """A short rational >= x (x > 0 float or Fraction)."""
    x = float(x)
    e = math.floor(math.log10(x)) - sig + 1
    return F(math.ceil(x / 10.0 ** e * (1 + 1e-12)), 1) * F(10) ** e


def classical_c(n, tau, J, d):
    """The shortest 7-digit rational c with classicalOk."""
    r = radUp(n, tau, J, d)
    c = up(math.sqrt(float(r)) / float(2 * PI_LO * (4 * PI_LO) ** tau))
    while not classicalOk(n, tau, J, d, c):
        c = up(float(c) * (1 + 1e-6))
    return c


# ----------------------------------------------------------------------------------------------- StepQ
class Step:
    def __init__(self, **kw):
        self.__dict__.update(kw)
        p = self
        n, kap = F(p.n), p.kap
        g = p.gb * p.d ** kap
        self.g = g
        COm = 2 * (n - 1) * p.c * p.sLt
        CSym = max(F(1), p.sB ** 2) * COm
        CRed = n * max(p.sNt, p.sLt + 2 * p.sN)
        w = 2 * p.M1 * p.sLt * p.sK + (2 * n * p.sK + n * p.sLt)
        CS = p.sT * max(p.sNt * g + p.t * p.ca * p.sLt, g + p.ca * p.HY * p.sLt)
        CXiN = CS + p.c * p.sLt
        CG = p.t * CXiN + p.Th * CS + p.sNt * g
        CDXi = max(CG, p.sLt * g)
        CXi = max(p.c * CG, g * CXiN)
        CDK = p.sK * p.c * CG + p.sN * g * CXiN
        CLin = CRed * CXi + CSym * CDXi + p.Th * COm * CS
        P = p.sK + p.sN
        CDw = p.Th * g * CS
        CFr = (p.M1 * p.sK + n) * (1 + p.sB) + p.sN * ((p.sLt * p.M1 + 2 * n) * p.sK + p.sLt * (p.M1 * p.sK + n)) * p.sB
        CdK = CFr * CXi + P * g * CDXi
        CE1 = 2 * P * (p.gb ** 2 * p.d ** (2 * kap - 1)) * CLin + p.M2 / 2 * CDK ** 2 + g * CS * CdK
        CE2 = p.gb * p.d ** (kap - 1) * n * (p.sLt * g + p.Th * COm) * p.c * CG + p.Mh2 / 2 * CDK ** 2
        CE = max(CE1, CE2)
        CGr = n * p.sLt + 2 * n * p.sK
        CB = p.sB ** 2 * CGr / (1 - p.th)
        CNd = n * p.sB + p.sK * CB
        CNtd = CB * p.sLt + 2 * n * p.sB
        CDab = 2 * p.M1 * (CNtd * p.sN + p.sNt * CNd) + 2 * p.M2 * p.sNt * p.sN * p.d
        CDc = p.sB ** 3 * w * (2 * n * p.sK + n * p.sLt)
        CDT0 = (CDab + CDc) * CDK + 2 * n * p.sNt * p.sB * (p.gb ** 2 * p.d ** (2 * kap)) + 2 * p.sB ** 3 * w * COm * g
        CDT = max(CDT0 + CDw * p.d, n * CDw * p.d + 2 * n * p.sNt * (p.gb ** 2 * p.d ** (2 * kap)))
        rT = p.sT ** 2 / (1 - p.th) * CDT
        self.CSym, self.CE, self.CDK, self.CDw, self.CDT, self.CGr = CSym, CE, CDK, CDw, CDT, CGr
        self.rate = [CDK, n * CDK, CB * CDK, rT, 2 * n * CDK, CNd * CDK, CNtd * CDK, CDT, CDw]

    def cond_terms(self, x):
        """The five condB comparisons as (lhs, rhs)."""
        p, kap = self, self.kap
        return [(p.gb ** 4 * p.d ** (2 * (2 * kap) - 1) * x, F(1)),
                (p.CSym * (p.gb ** 3 * p.d ** (3 * kap - 1)) * x, F(1, 2)),
                (p.CE * x, F(1)),
                (p.sT * p.CDT * (p.gb ** 2 * p.d ** (2 * kap - 1)) * x, p.th),
                (p.sB * p.CGr * p.CDK * (p.gb ** 2 * p.d ** (2 * kap - 1)) * x, p.th)]

    def condB(self, x):
        return all(a <= b for a, b in self.cond_terms(x))


JI = [0, 1, 1, 1, 1, 1, 1, 1, 0]
CAP_NAMES = ["mu/2", "sK", "sB", "sT", "sLt", "sN", "sNt", "t", "nu/2"]


# ----------------------------------------------------------------------------------------------- NumQ
class Num:
    """NumQ.  Q fields: n tau rho rhoInf M1 M2 sK sB sT sLt sN sNt t th gb c cbar ctail kp Th HY Mh2."""

    def __init__(self, **kw):
        self.__dict__.update(kw)
        self.d0 = min(F(1), (self.rho - self.rhoInf) / 6)
        self._inp = {}

    def delta(self, s):
        return F(1, 2) ** s * self.d0

    def r(self, s):
        return self.rho - 6 * self.d0 * (1 - F(1, 2) ** s)

    def b(self, s):
        return min(self.r(s), F(1))

    def cS(self, s):
        return (self.c[s] if s < len(self.c) else F(0)) if s < self.kp else self.ctail

    def caS(self, s):
        if s < self.kp:
            cb = self.cbar[s] if s < len(self.cbar) else F(0)
            return cb * (self.delta(s) / self.b(s)) ** self.tau
        return self.ctail

    def dS(self, s):
        return self.delta(min(s, self.kp))

    def inp(self, s):
        if s not in self._inp:
            self._inp[s] = Step(n=self.n, kap=self.tau, M1=self.M1, M2=self.M2, sK=self.sK, sB=self.sB, sT=self.sT,
                                sLt=self.sLt, sN=self.sN, sNt=self.sNt, t=self.t, c=self.cS(s), ca=self.caS(s),
                                gb=self.gb, d=self.dS(s), th=self.th, Th=self.Th, HY=self.HY, Mh2=self.Mh2)
        return self._inp[s]

    def xs(self, Xs):
        out = [Xs]
        for s in range(self.kp):
            if isinstance(out[-1], float) and not (out[-1] < 1e100):       # float search mode: overflow
                out.append(float("inf"))
                continue
            out.append(F(2) ** (2 * (2 * self.tau)) * self.inp(s).CE * out[-1] ** 2)
        return out

    def sumQ(self, gam, xs, cf, e):
        kp = self.kp
        tot = sum(cf(t) * xs[t] * (gam ** 2 * self.delta(t) ** e) for t in range(kp))
        return tot + 2 * cf(kp) * xs[kp] * (gam ** 2 * self.delta(kp) ** e)

    def sums(self, Xs):
        xs = self.xs(Xs)
        return [self.sumQ(self.gb, xs, lambda s, i=i: self.inp(s).rate[i], 2 * self.tau - JI[i]) for i in range(9)]

    def okB(self, cap, m0, Xs, detail=False):
        xs = self.xs(Xs)
        why = []
        if any(isinstance(x, float) and not (x < 1e300) for x in xs):      # float search mode: overflow / nan
            return (False, ["overflow"]) if detail else False
        if Xs < 0:
            why.append("Xs<0")
        for s in range(self.kp + 1):
            for j, (a, bnd) in enumerate(self.inp(s).cond_terms(xs[s])):
                if a > bnd:
                    why.append("J1 stage %d cond %d" % (s, j))
        if F(2) ** (2 * (2 * self.tau)) * self.inp(self.kp).CE * xs[self.kp] > 1:
            why.append("J2 tail")
        sm = self.sums(Xs)
        for i in range(9):
            if m0[i] + sm[i] > cap[i]:
                why.append("J3 " + CAP_NAMES[i])
        return (not why, why) if detail else not why

    def wfOk(self):
        Q = self
        return (2 <= Q.n and 1 <= Q.tau and 0 < Q.rhoInf < Q.rho and Q.M1 >= 0 and Q.M2 >= 0 and Q.sK > 0
                and Q.sB > 0 and Q.sT > 0 and Q.sLt >= 0 and Q.sN >= 0 and Q.sNt >= 0 and Q.t >= 0 and 0 < Q.th < 1
                and Q.gb > 0 and all(a >= 0 for a in Q.c) and all(a >= 0 for a in Q.cbar) and Q.ctail >= 0
                and Q.Th >= 0 and Q.HY >= 0 and Q.Mh2 >= 0)

    def c2Q(self, Xs):
        xs = self.xs(Xs)
        return (self.rho ** (2 * self.tau) * self.sumQ(F(1), xs, lambda s: self.inp(s).CDK, 2 * self.tau)
                / (Xs * self.d0 ** (4 * self.tau)))

    def c3Q(self, Xs):
        xs = self.xs(Xs)
        return (self.rho ** (2 * self.tau) * self.sumQ(F(1), xs, lambda s: self.inp(s).CDw, 2 * self.tau)
                / (Xs * self.d0 ** (4 * self.tau)))


# ----------------------------------------------------------------------------------------------- RouteACore
def boxNormUp(box):
    return max([abs(F(c)) + F(r) for c, r in box] + [F(0)])


def freqNormLo(box):
    return max([abs(F(c)) - F(r) for c, r in box] + [F(0)])


def capQ(Q, mu, nu):
    return [mu / 2, Q.sK, Q.sB, Q.sT, Q.sLt, Q.sN, Q.sNt, Q.t, nu / 2]


def initQ(iLt, iN, iNt, iH, sK, sB, sT, mu):
    return [F(0), sK - mu, sB - mu, sT - mu, iLt, iN, iNt, iH, F(0)]


def defaultInitQ(n, p):
    sK, sB, mu, M = p["sK"], p["sB"], p["mu"], p["M"]
    hT = 4 * n * M * sK ** 2 * sB ** 2 + 1
    return initQ(2 * n * (sK - mu), (sK - mu) * (sB - mu), 2 * n * (sK - mu) * (sB - mu), hT, sK, sB, p["sT"], mu)


def disp_coefs(Q, n, p, Xs, frozen):
    """The constants of the displacement comparison: (max of the constants, c2Q, c3Q, C2#, C3#)."""
    c2, c3 = Q.c2Q(Xs), Q.c3Q(Xs)
    if frozen:
        r = SQ.sharp(p)
        return max(r["C2"], r["C3"], c2, c3), c2, c3, r["C2"], r["C3"]
    return max(c2, c3), c2, c3, None, None


def finalOk(Q, n, p, box, Xs, frozen=True):
    tau = p["tau"]
    a = p["err"] < Xs * p["gamma"] ** 4 * Q.d0 ** (4 * tau)
    C = disp_coefs(Q, n, p, Xs, frozen)[0]
    b = C * p["err"] <= p["disp"] * (p["gamma"] ** 2 * p["rho"] ** (2 * tau))
    cc = p["disp"] < (p["som"] - p["s"]) * freqNormLo(box)
    return a and b and cc


# ----------------------------------------------------------------------------------------------- RouteAFrozen
def frozen_num(w, n, p, box):
    return Num(n=n, tau=p["tau"], rho=p["rho"], rhoInf=p["rhoInf"], M1=p["M"], M2=p["M"], sK=p["sK"] - p["mu"] / 2,
               sB=w["sB"], sT=w["sT"], sLt=w["sLt"], sN=w["sN"], sNt=w["sNt"], t=w["t"], th=w["th"], gb=p["gbar"],
               c=w["c"], cbar=w["cbar"], ctail=w["ctail"], kp=w["kp"], Th=p["som"] * boxNormUp(box),
               HY=p["M"] * w["sN"], Mh2=p["M"])


def refined_num(w, n, p, box):
    Q = frozen_num(w, n, p, box)
    R = w["R"]
    Q.M1, Q.M2, Q.HY, Q.Mh2 = R["dx"], R["d2x"], R["dh"] * w["sN"], R["d2h"]
    Q._inp = {}
    return Q


def torsionCoefQ(Q, M, sK, sB):
    n, tau = Q.n, Q.tau
    cR = SQ.cRRQ(n, tau)
    nn = F(n)
    cT1 = 2 * nn ** 2 * sK * sB ** 2
    wT = 4 * nn * M * sK ** 2 + 2 * nn * (nn + 1) * sK
    cOm = 2 * nn * (nn + 1) * cR * sK
    cT2 = F(2) ** (tau + 1) * sB ** 3 * wT * cOm
    return cT1 * (Q.gb ** 4 * Q.delta(0) ** (2 * (2 * tau) - 1)) + cT2 * (Q.gb ** 3 * Q.delta(0) ** (3 * tau - 1))


def torsionCapOk(Q, M, sK, sB, Xs):
    return (1 + torsionCoefQ(Q, M, sK, sB)) * Xs <= 1


def classicalListOk(Q, J):
    return (all(classicalOk(Q.n, Q.tau, J, Q.delta(s), Q.c[s]) and classicalOk(Q.n, Q.tau, J, Q.b(s), Q.cbar[s])
                for s in range(Q.kp)) and classicalOk(Q.n, Q.tau, J, Q.delta(Q.kp), Q.ctail))


def frozenCore(n, p, box, w, detail=False):
    Q = frozen_num(w, n, p, box)
    parts = dict(Xs=w["Xs"] > 0, wf=Q.wfOk(), okB=Q.okB(capQ(Q, p["mu"], p["nu"]), defaultInitQ(n, p), w["Xs"]),
                 torsion=torsionCapOk(Q, p["M"], p["sK"], p["sB"], w["Xs"]), classical=classicalListOk(Q, w["J"]),
                 final=finalOk(Q, n, p, box, w["Xs"], frozen=True))
    return (all(parts.values()), parts) if detail else all(parts.values())


def refinedCore(n, p, box, w, detail=False):
    """The numerical part of refinedTest; the sites use w['c'], w['cbar'] as given (certified or classical, see
    `site_c`), the tail is checked classical exactly as in Lean."""
    Q = refined_num(w, n, p, box)
    R = w["R"]
    m0 = initQ(R["bL"], R["bN"], R["bNt"], R["bT"], p["sK"], p["sB"], p["sT"], p["mu"])
    parts = dict(Xs=w["Xs"] > 0, wf=Q.wfOk(), okB=Q.okB(capQ(Q, p["mu"], p["nu"]), m0, w["Xs"]),
                 tail=classicalOk(n, p["tau"], w["J"], Q.delta(w["kp"]), Q.ctail),
                 final=finalOk(Q, n, p, box, w["Xs"], frozen=False))
    return (all(parts.values()), parts) if detail else all(parts.values())
