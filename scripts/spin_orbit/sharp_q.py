#!/usr/bin/env python3
"""SO-GEN3: exact rational mirror of the landed sharp test (untrusted tooling).

Transcribes KAM/CertificateSharp/ConstantsQ.lean (sharpIsoC1Q/2Q/3Q and their sub-constants) and
KAM/CertificateSharp/Constants.lean (sqrtUpQ, cRRadQ, cRRQ) and KAM/CertificateSharp/Sharp.lean (sharpTest):
    sharpIsoC1Q * err < gamma^4 rho^(4 tau),   max(sharpIsoC2Q, sharpIsoC3Q) * err <= disp gamma^2 rho^(2 tau).
All arithmetic is exact (Fraction).
"""
import math
from fractions import Fraction as F


def ceil_nat(x):
    x = F(x)
    return max(0, -((-x.numerator) // x.denominator))


def sqrtUpQ(x):
    x = F(x)
    s = F(math.isqrt(ceil_nat(x * 1000000)) + 1, 1000)
    return (x / s + s) / 2


PI6 = F(3141592, 1000000)


def cRRadQ(n, tau):
    return F(2) ** n * (6 * (1 + F(2) ** tau) * (2 * F(tau) / (F(2718, 1000) * PI6)) ** (2 * tau))


def cRRQ(n, tau):
    return 1 / (2 * PI6) * sqrtUpQ(cRRadQ(n, tau))


def consts(n, tau, cR, M, sK, sB, sT, gb, mu, nu):
    n = F(n)
    thetaS = 2 * n * sK * sB * (M + 1)
    cOm = 2 * n * (n + 1) * cR * sK
    cSym = max(F(1), sB ** 2) * cOm
    cRed = 2 * n * sK * max(n * sB, n + sB)
    cT0 = 4 * n * M * sK ** 2 * sB ** 2
    cT1 = 2 * n ** 2 * sK * sB ** 2
    wT = 4 * n * M * sK ** 2 + 2 * n * (n + 1) * sK
    cT2 = F(2) ** (tau + 1) * sB ** 3 * wT * cOm
    hT = cT0 + 1
    cGram = 2 * n * sK * (n * (1 + F(1, 8)) + 1)
    cB = F(8, 7) * sB ** 2 * cGram
    cDab = 4 * F(8, 7) ** 4 * n * M * sK ** 2 * sB ** 2 * (2 * cB / sB + (n + 1) / sK + 1)
    cDc = 2 * n * F(8, 7) ** 5 * sK * sB ** 3 * wT * (n + F(8, 7))
    iCS = sT * max(2 * n * sK * sB * gb + 2 * n * cR * sK * hT, gb + 2 * n * cR * M * sK ** 2 * sB)
    iCXiN = iCS + 2 * n * cR * sK
    iCG = hT * iCXiN + thetaS * iCS + 2 * n * sK * sB * gb
    iCDXi = max(iCG, 2 * n * sK * gb)
    iCXi = max(cR * iCG, gb * iCXiN)
    iCDK = sK * (cR * iCG + sB * gb * iCXiN)
    iCDw = thetaS * gb * iCS
    iCP = (M * sK + n) * (1 + sB) + 2 * n * sK ** 2 * sB ** 2 * (2 * M * sK + n + 1)
    iCdK = iCP * iCXi + sK * (1 + sB) * gb * iCDXi
    iCLin = cRed * iCXi + cSym * iCDXi + thetaS * cOm * iCS
    iCE1 = 2 * sK * (1 + sB) * gb ** 2 * iCLin + M / 2 * iCDK ** 2 + gb * iCS * iCdK
    iCE2 = gb * n * (2 * n * sK * gb + thetaS * cOm) * cR * iCG + M / 2 * iCDK ** 2
    iCE = max(iCE1, iCE2)
    iCDT = (cDab + cDc) * iCDK + (1 + F(8, 7) ** 3) * cT1 * gb ** 2 + (1 + F(8, 7) ** 5) * sB ** 3 * wT * cOm * gb
    iCDTb = max(iCDT + iCDw, n * iCDw + 2 * n ** 2 * (1 + F(8, 7) ** 2) * sK * sB * gb ** 2)
    iRateD = n * iCDK
    iRateB = cB * iCDK
    iRateT = F(8, 7) * sT ** 2 * iCDTb
    iCStep = max(gb ** 4 * (1 + cT1) + gb ** 3 * cT2,
                 2 * gb ** 3 * cSym,
                 gb ** 2 * iRateD / (F(1, 8) * sK),
                 gb ** 2 * sB * cGram * iCDK / F(1, 8),
                 gb ** 2 * sT * iCDTb / F(1, 8),
                 iCE)
    iCSum = 4 * gb ** 2 * max(2 * iCDK, iRateD, iRateB, iRateT)
    terms = {"E": F(2) ** (2 * (2 * tau)) * iCE, "step": iCStep, "sum": iCSum / mu, "nu": 4 * gb ** 2 * iCDw / nu}
    return dict(iCStar=max(terms.values()), iCDK=iCDK, iCDw=iCDw, terms=terms, active=max(terms, key=terms.get))


def delta0sQ(rho, rhoinf):
    return min(F(1), (rho - rhoinf) / 6)


def sharp(p):
    """p: dict tau rho rhoInf M sK sB sT mu gbar nu gamma.  Returns C1, C2, C3, threshold, disp coefficient."""
    n, tau = 2, p["tau"]
    cR = cRRQ(n, tau)
    k = consts(n, tau, cR, p["M"], p["sK"], p["sB"], p["sT"], p["gbar"], p["mu"], p["nu"])
    d0 = delta0sQ(p["rho"], p["rhoInf"])
    rho, g = p["rho"], p["gamma"]
    C1 = rho ** (4 * tau) * max(p["gbar"] ** 4, k["iCStar"] / d0 ** (4 * tau))
    C2 = 2 * k["iCDK"] * rho ** (2 * tau) / d0 ** (2 * tau)
    C3 = 2 * k["iCDw"] * rho ** (2 * tau) / d0 ** (2 * tau)
    thr = g ** 4 * rho ** (4 * tau) / C1                  # err < thr
    dcoef = max(C2, C3) / (g ** 2 * rho ** (2 * tau))     # disp >= dcoef * err
    return dict(C1=C1, C2=C2, C3=C3, threshold=thr, disp_coef=dcoef, active=k["active"], terms=k["terms"])


def sharpTest(p):
    r = sharp(p)
    rho, g, tau = p["rho"], p["gamma"], p["tau"]
    return (r["C1"] * p["err"] < g ** 4 * rho ** (4 * tau)) and (
        max(r["C2"], r["C3"]) * p["err"] <= p["disp"] * g ** 2 * rho ** (2 * tau))


def lg(q):
    q = F(q)
    return math.log10(q.numerator) - math.log10(q.denominator)


def R1(err=0, disp=0):
    """LunarParams.lean lunarR1 (for the cross-check against the design's ~1e-25)."""
    c = F(237, 125); s = 1 + F(1, 10 ** 6); kap = c / s
    return dict(tau=1, rho=F(1, 70), rhoInf=F(1, 70000), M=F(203, 100), sK=F(1987, 1000), sB=F(1987, 1000),
                sT=F(1987, 1000), mu=F(1, 160), gbar=kap / 42, nu=F(1, 10 ** 6), gamma=kap / 42, err=F(err),
                disp=F(disp))


if __name__ == "__main__":
    r = sharp(R1())
    print("R1 sharp: log10 threshold %.3f active %s log10 disp coef %.3f" % (lg(r["threshold"]), r["active"],
                                                                            lg(r["disp_coef"])))
