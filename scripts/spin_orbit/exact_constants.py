#!/usr/bin/env python3
"""Exact (Fraction) transcription of the KAM constants for the SO pilot parameter package.

Untrusted tooling.  Each function cites the Lean definition it transcribes:
  KAM/Apost/Constants.lean   (kappa, aExp, cR, mSize, Theta, C_X, C_T, C_Omega, C_sym, C_red, C_xi0,
                              C_G, C_B, C_DN, C_DX, C_DT, delta0)
  KAM/Iso/Apost/Defs.lean    (hatCS .. hatCDelta, CP, hatClin, hatCE1/2, hatCE, CY, CDTbord, hatcStep,
                              hatcSum, hatcStar, isoC1, isoC2)
cR = max 1 (cohConst n tau), cohConst n tau = (2 pi)^-1 (tau/(e pi))^tau (8n/pi)^n
(KAM/Strip/CohomologicalDefs.lean:31); for n=2, tau=1 it equals 128/(e pi^4) < 1 (e > 2.7, pi^4 > 97,
so e pi^4 > 261 > 128), hence cR = 1 exactly.  All exponents here are integers.
"""
from fractions import Fraction as F
import json, sys, math

def constants(n, tau, rho, rhoinf, M, sK, sB, sT, mu, nu, gbar):
    assert n == 2 and tau == 1, "cR = 1 is only justified for n = 2, tau = 1"
    n = F(n); tau = F(tau)
    kappa = tau + n                         # Constants.lean: kappa = tau + n
    a = 2 * kappa + 2                       # aExp = 2 kappa + 2
    cR = F(1)                               # see module docstring
    m = max(F(1), M, sK, sB, sT)            # mSize
    Theta = 4 * n * m**3
    C_X = 5 * n**2 * m**5
    C_T = 2 * n * m**2 * C_X
    C_Omega = 2 * n * (n + 1) * cR * m
    C_sym = m**2 * C_Omega
    C_red = 2 * n * (n + 1) * m**2
    C_xi0 = 2 * n * m**2 * (m * Theta + cR * C_T)
    C_G = 6 * n**2 * m
    C_B = 2 * m**2 * C_G
    C_DN = 2 * n * m + m * C_B
    C_DX = 2 * m**3 + (m + n * Theta) * C_DN
    C_DT = 4 * n * m**2 * C_DX + 2 * n * C_DN * C_X
    # Iso/Apost/Defs.lean
    hatCS = max(C_xi0, m * Theta + 2 * n * cR * m**5)
    hatCxiN = hatCS + 2 * n * cR * m
    hatCg = C_T * hatCxiN + Theta * hatCS + 2 * n * m**2 * Theta
    hatCxi = max(cR * hatCg, Theta * hatCxiN)
    hatCDK = 2 * m**2 * hatCxi
    hatCDelta = max(hatCDK, Theta**2 * hatCS)
    CP = m**2 + n + m**3 + C_X
    hatCpartial = CP * hatCxi + 2 * m**2 * Theta * hatCg
    hatClin = C_red * hatCxi + C_sym * hatCg + Theta * C_Omega * hatCS
    hatCE1 = 4 * m**2 * Theta**2 * hatClin + m * hatCDK**2 + Theta * hatCS * hatCpartial
    hatCE2 = n * Theta**2 * (2 * n * m + C_Omega) * cR * hatCg + m * hatCDK**2
    hatCE = max(hatCE1, hatCE2)
    CY = n * m * (2 * m**2 + C_DN)
    CDTbord = C_DT + 8 * n**2 * m**4 + 1 + CY
    hatcStep = 2 * Theta**3 * max(C_sym, m * CDTbord * hatCDelta)
    hatcSum = 4 * Theta**2 * hatCDelta * max(n, C_B, m**2 * CDTbord)
    t_E = F(2)**int(2 * a) * hatCE
    t_step = hatcStep * max(F(1), 2 / mu)
    t_sum = 2 * hatcSum / mu
    t_nu = 4 * Theta**2 * hatCDelta / nu
    hatcStar = max(t_E, t_step, t_sum, t_nu)
    delta0 = min(F(1), (rho - rhoinf) / 8)
    isoC1 = rho**int(4 * tau) * max(gbar**4, hatcStar * delta0**(-int(2 * a)))
    isoC2 = 2 * hatCDelta * rho**int(2 * tau) * delta0**(-int(a))
    active = max([("E", t_E), ("step", t_step), ("sum", t_sum), ("nu", t_nu)], key=lambda x: x[1])[0]
    return dict(a=a, delta0=delta0, m=m, Theta=Theta, hatCDelta=hatCDelta, hatCE=hatCE, hatcStep=hatcStep,
                hatcSum=hatcSum, hatcStar=hatcStar, active=active, isoC1=isoC1, isoC2=isoC2,
                terms={"E": t_E, "step": t_step, "sum": t_sum, "nu": t_nu})

def package_R1(c, m):
    """Owner ruling O5, package R1 (rotated frame): rho' = 1/70, rho_inf = rho'/1000, mu = 1/160, ray scalar
    s = 1 + 10^-6, ray margin nu = 10^-6, sigma_omega = 2, time scale c (H -> c H', omega* = c (nu - 1, 1)/s),
    gamma = gbar = c/(42 s) (gamma((nu - 1, 1)) = 1/42 from SO-DIO's (nu/2, 1/2) in Dio(1/42, 1)), and
    M = sK = sB = sT = m (only mSize = max enters the constants).  Exact rationals; returns (params, extra)."""
    c = F(c); m = F(m)
    s = 1 + F(1, 10**6)
    gbar = c / (42 * s)
    p = dict(n=2, tau=1, rho=F(1, 70), rhoinf=F(1, 70000), M=m, sK=m, sB=m, sT=m, mu=F(1, 160),
             nu=F(1, 10**6), gbar=gbar)
    return p, dict(s=s, sigma_omega=F(2), c=c, gamma=gbar)

def threshold_of(p, gamma):
    """exact threshold: e < threshold  <=>  isoC1 e/(gamma^4 rho^4) < 1; also the displacement coefficient."""
    k = constants(**p)
    thr = gamma**4 * p["rho"]**4 / k["isoC1"]
    coef = k["isoC2"] / (gamma**2 * p["rho"]**2)
    return thr, coef, k

def main_R1(c, m, out=None):
    p, x = package_R1(c, m)
    thr, coef, k = threshold_of(p, x["gamma"])
    lg = lambda q: math.log10(q.numerator) - math.log10(q.denominator)
    print("R1 package: c =", c, " m =", m, " gamma = gbar =", x["gamma"], " active:", k["active"])
    print("threshold log10 = %.6f   threshold float = %.16e" % (lg(thr), float(thr)))
    print("displacement coefficient float = %.16e" % float(coef))
    res = dict(package="R1", params={kk: str(v) for kk, v in p.items()}, s=str(x["s"]), sigma_omega=str(x["sigma_omega"]),
               c=str(x["c"]), gamma=str(x["gamma"]), hatCDelta=str(k["hatCDelta"]), hatcStar=str(k["hatcStar"]),
               active=k["active"], isoC1=str(k["isoC1"]), isoC2=str(k["isoC2"]), threshold=str(thr),
               threshold_log10=lg(thr), displacement_coefficient=str(coef))
    if out:
        json.dump(res, open(out, "w"), indent=1)
    return res

def main():
    if len(sys.argv) > 1 and sys.argv[1] == "R1":
        main_R1(F(sys.argv[2]), F(sys.argv[3]), sys.argv[4] if len(sys.argv) > 4 else None)
        return
    p = dict(n=2, tau=1, rho=F(1, 200), rhoinf=F(1, 400), M=F(4), sK=F(4), sB=F(4), sT=F(4),
             mu=F(1, 1000), nu=F(1, 4), gbar=F(1, 42))
    c = constants(**p)
    gamma = F(1, 42)                        # gamma = gbar; the I-G1 smallness C1 e/(gamma^4 rho^(4 tau)) < 1
    thr = gamma**4 * p["rho"]**4 / c["isoC1"]
    coef = c["isoC2"] / (gamma**2 * p["rho"]**2)   # displacement: |Kinf-K| <= C2 e/(gamma^2 rho^(2 tau))
    print("hatCDelta =", c["hatCDelta"])
    print("hatcStar  =", c["hatcStar"], " active:", c["active"])
    print("terms:", {k: float(v) for k, v in c["terms"].items()})
    print("threshold (exact, e < ) =", thr)
    print("threshold float = %.16e" % float(thr))
    print("displacement coefficient float = %.16e" % float(coef))
    e = F(1, 10**103)
    print("ratio C1 e/(g^4 rho^4) at e=1e-103 = %.16e" % float(c["isoC1"] * e / (gamma**4 * p["rho"]**4)))
    print("displacement bound at e=1e-103 = %.6e" % float(coef * e))
    out = dict(params={k: str(v) for k, v in p.items()}, hatCDelta=str(c["hatCDelta"]), hatcStar=str(c["hatcStar"]),
               active=c["active"], isoC1=str(c["isoC1"]), isoC2=str(c["isoC2"]), threshold=str(thr),
               displacement_coefficient=str(coef))
    if len(sys.argv) > 1:
        json.dump(out, open(sys.argv[1], "w"), indent=1)

if __name__ == "__main__":
    main()
