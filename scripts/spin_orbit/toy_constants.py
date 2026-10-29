#!/usr/bin/env python3
"""Exact (Fraction) mirror of KAM/Certificate/Constants.lean: cRUpQ, the mirror chain and isoC1Q, isoC2Q.

Untrusted tooling (SO-TOYGEN).  Every function transcribes the Lean definition of the same name for
general n, tau in N (exact_constants.py covers only n = 2, tau = 1 with c_R = 1).  The checker's
smallness test (checkSmallness, A-E §G) is `isoC1Q e < gamma^4 rho^(4 tau)` and
`isoC2Q e <= disp gamma^2 rho^(2 tau)`.
"""
from fractions import Fraction as F

PI_LO = F(3141592, 1000000)          # piLoQ


def qdiv(a, b):
    """Lean's division on ℚ: x / 0 = 0."""
    return F(a) / F(b) if b != 0 else F(0)


def qinv(a):
    return qdiv(1, a)


def cRUpQ(n, tau):
    """Constants.lean cRUpQ: max 1 ((2 piLo)^-1 (tau/(2.718 piLo))^tau (8 n/piLo)^n)."""
    n = F(n); tau_n = int(tau)
    v = qinv(2 * PI_LO) * qdiv(tau_n, F(2718, 1000) * PI_LO) ** tau_n * qdiv(8 * n, PI_LO) ** int(n)
    return max(F(1), v)


def mirrors(n, tau, M, sK, sB, sT):
    n_i = int(n); n = F(n); M, sK, sB, sT = map(F, (M, sK, sB, sT))
    cR = cRUpQ(n_i, tau)
    m = max(F(1), max(M, max(sK, max(sB, sT))))
    Theta = 4 * n * m ** 3
    CX = 5 * n ** 2 * m ** 5
    CT = 2 * n * m ** 2 * CX
    COmega = 2 * n * (n + 1) * cR * m
    Csym = m ** 2 * COmega
    Cred = 2 * n * (n + 1) * m ** 2
    Cxi0 = 2 * n * m ** 2 * (m * Theta + cR * CT)
    CG = 6 * n ** 2 * m
    CB = 2 * m ** 2 * CG
    CDN = 2 * n * m + m * CB
    CDX = 2 * m ** 3 + (m + n * Theta) * CDN
    CDT = 4 * n * m ** 2 * CDX + 2 * n * CDN * CX
    CY = n * m * (2 * m ** 2 + CDN)
    CDTbord = CDT + 8 * n ** 2 * m ** 4 + 1 + CY
    hatCS = max(Cxi0, m * Theta + 2 * n * cR * m ** 5)
    hatCxiN = hatCS + 2 * n * cR * m
    hatCg = CT * hatCxiN + Theta * hatCS + 2 * n * m ** 2 * Theta
    hatCxi = max(cR * hatCg, Theta * hatCxiN)
    hatCDK = 2 * m ** 2 * hatCxi
    hatCDelta = max(hatCDK, Theta ** 2 * hatCS)
    CP = m ** 2 + n + m ** 3 + CX
    hatCpartial = CP * hatCxi + 2 * m ** 2 * Theta * hatCg
    hatClin = Cred * hatCxi + Csym * hatCg + Theta * COmega * hatCS
    hatCE1 = 4 * m ** 2 * Theta ** 2 * hatClin + m * hatCDK ** 2 + Theta * hatCS * hatCpartial
    hatCE2 = n * Theta ** 2 * (2 * n * m + COmega) * cR * hatCg + m * hatCDK ** 2
    hatCE = max(hatCE1, hatCE2)
    hatcStep = 2 * Theta ** 3 * max(Csym, m * CDTbord * hatCDelta)
    hatcSum = 4 * Theta ** 2 * hatCDelta * max(n, max(CB, m ** 2 * CDTbord))
    return dict(cR=cR, m=m, Theta=Theta, hatCDelta=hatCDelta, hatCE=hatCE, hatcStep=hatcStep,
                hatcSum=hatcSum)


def hatcStarQ(n, tau, M, sK, sB, sT, mu, nu):
    k = mirrors(n, tau, M, sK, sB, sT)
    mu, nu = F(mu), F(nu)
    terms = {"E": F(2) ** (2 * (2 * (int(tau) + int(n)) + 2)) * k["hatCE"],
             "step": k["hatcStep"] * max(F(1), qdiv(2, mu)),
             "sum": qdiv(2 * k["hatcSum"], mu),
             "nu": qdiv(4 * k["Theta"] ** 2 * k["hatCDelta"], nu)}
    return max(terms["E"], max(terms["step"], max(terms["sum"], terms["nu"]))), terms, k


def delta0Q(rho, rhoinf):
    return min(F(1), qdiv(F(rho) - F(rhoinf), 8))


def isoC1Q(n, tau, rho, rhoinf, M, sK, sB, sT, mu, nu, gbar):
    star, _, _ = hatcStarQ(n, tau, M, sK, sB, sT, mu, nu)
    a2 = 2 * (2 * (int(tau) + int(n)) + 2)
    return F(rho) ** (4 * int(tau)) * max(F(gbar) ** 4, star * qinv(delta0Q(rho, rhoinf) ** a2))


def isoC2Q(n, tau, rho, rhoinf, M, sK, sB, sT):
    k = mirrors(n, tau, M, sK, sB, sT)
    a = 2 * (int(tau) + int(n)) + 2
    return 2 * k["hatCDelta"] * F(rho) ** (2 * int(tau)) * qinv(delta0Q(rho, rhoinf) ** a)


def smallness(p):
    """checkSmallness on a parameter dict p (keys as CertParams): returns (ok, data)."""
    n, tau = int(p["n"]), int(p["tau"])
    c1 = isoC1Q(n, tau, p["rho"], p["rhoInf"], p["M"], p["sK"], p["sB"], p["sT"], p["mu"], p["nuRay"],
                p["gbar"])
    c2 = isoC2Q(n, tau, p["rho"], p["rhoInf"], p["M"], p["sK"], p["sB"], p["sT"])
    lhs1, rhs1 = c1 * p["err"], p["gamma"] ** 4 * p["rho"] ** (4 * tau)
    lhs2, rhs2 = c2 * p["err"], p["disp"] * p["gamma"] ** 2 * p["rho"] ** (2 * tau)
    thr = qdiv(rhs1, c1)
    return (lhs1 < rhs1 and lhs2 <= rhs2), dict(isoC1Q=c1, isoC2Q=c2, threshold=thr,
                                                  ratio1=qdiv(lhs1, rhs1), disp_min=qdiv(c2 * p["err"],
                                                      p["gamma"] ** 2 * p["rho"] ** (2 * tau)))


if __name__ == "__main__":
    import math
    lg = lambda q: math.log10(q.numerator) - math.log10(q.denominator)
    # cross-check with exact_constants.py at n = 2, tau = 1 (c_R = 1 there; cRUpQ(2, 1) = 1 too)
    import exact_constants as ec
    p = dict(n=2, tau=1, rho=F(1, 200), rhoinf=F(1, 400), M=F(4), sK=F(4), sB=F(4), sT=F(4),
             mu=F(1, 1000), nu=F(1, 4), gbar=F(1, 42))
    ref = ec.constants(**p)
    mine = isoC1Q(2, 1, p["rho"], p["rhoinf"], 4, 4, 4, 4, p["mu"], p["nu"], p["gbar"])
    assert ref["isoC1"] == mine, "isoC1 mismatch"
    assert ref["isoC2"] == isoC2Q(2, 1, p["rho"], p["rhoinf"], 4, 4, 4, 4)
    print("cross-check with exact_constants.py: OK;  cRUpQ(2,1) =", cRUpQ(2, 1), " cRUpQ(3,2) =",
          float(cRUpQ(3, 2)))
