#!/usr/bin/env python3
"""Threshold columns of the feasibility study: current theorem, v1 (design, Russmann) and an ESTIMATED v2.

current and v1 call scripts/apost_sharp/thresholds.py unchanged.  v2 has no numbers yet (package SHARP-PLUS is open), so
`v2_est` below is this study's own estimate: the v1 constants of Definition bpI:p2s:constants with three substitutions
taken from the SHARP-PLUS brief, each of which needs a proof that does not exist yet:
  L1  the derived torsion bound H_T = 4 n M sK^2 sB^2 + 1 is replaced by (actual sup |T|) + 1, and M/2 in the quadratic
      term by M2/2 with M2 >= |D^2 X_H| alone;
  L2  c_R is replaced by a frequency-specific constant: either FHL17's classic value 0.036 (Table 4, L = 0, n = 2) or
      (v2+) the ad hoc constant computed here from S(omega, delta) = sum_k |k.omega|^-2 exp(-4 pi delta |k|_1).
Nothing else changes.  The ell^1 coefficient-norm route of PlasmaLean (c = 1/(4 pi^2 e) = 0.0093 in period-1 units) is
reported as a separate variant.
"""
import math
import os
import sys
from fractions import Fraction as F

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "apost_sharp"))
import thresholds as TH  # noqa: E402


def Q(x, up=True):
    """rational upper bound with 6 significant digits."""
    x = float(x)
    if x == 0:
        return F(0)
    e = math.floor(math.log10(abs(x))) - 5
    m = math.ceil(x / 10.0 ** e) if up else math.floor(x / 10.0 ** e)
    return F(m) * (F(10) ** e)


def sharp_mod(n, tau, kappa, cR, M, sK, sB, sT, mu, rho, rhoinf, gbar, nu=None, iso=True, HT=None, M2=None,
              lam=3, theta=F(1, 8), qS=F(1, 2), tX=F(1, 2)):
    """Copy of thresholds.sharp (design defaults) with the overrides HT (torsion bound) and M2 (quadratic term)."""
    n = F(n); tau = F(tau); kappa = F(kappa)
    a = 2 * kappa
    th = F(theta); thh = 1 / (1 - th)
    NS = 1 / (1 - F(qS))
    Theta = 2 * n * sK * sB * (M + 1)
    g = gbar
    C_Om = 2 * n * (n + 1) * cR * sK
    C_sym = max(F(1), sB ** 2) * C_Om
    C_red = 2 * n * sK * max(n * sB, n + sB)
    C_T0 = 4 * n * M * sK ** 2 * sB ** 2
    C_T1 = 2 * n ** 2 * sK * sB ** 2
    w = 4 * n * M * sK ** 2 + 2 * n * (n + 1) * sK
    C_T2 = F(2) ** int(kappa + 1) * C_Om * sB ** 3 * w
    H_T = (C_T0 + 1) if HT is None else HT
    if not iso:
        C_S = 2 * n * sK * sT * (sB * g + cR * H_T)
        C_xiN = C_S + 2 * n * cR * sK
        C_g = H_T * C_xiN + 2 * n * sK * sB * g
    else:
        C_S = sT * max(2 * n * sK * sB * g + 2 * n * cR * sK * H_T, g + 2 * n * cR * M * sK ** 2 * sB)
        C_xiN = C_S + 2 * n * cR * sK
        C_g = H_T * C_xiN + Theta * C_S + 2 * n * sK * sB * g
    C_dxi = max(C_g, 2 * n * sK * g)
    C_xi = max(cR * C_g, g * C_xiN)
    C_DK = sK * (cR * C_g + sB * g * C_xiN)
    MQ = M if M2 is None else M2
    if not iso:
        C_lin = C_red * C_xi + C_sym * C_dxi
        C_E = NS * sK * (1 + sB) * g ** 2 * C_lin + tX * MQ * C_DK ** 2
        C_Dw = None
    else:
        C_Dw = Theta * g * C_S
        C_P = (M * sK + n) * (1 + sB) + 2 * n * sK ** 2 * sB ** 2 * (2 * M * sK + n + 1)
        C_dK = C_P * C_xi + sK * (1 + sB) * g * C_dxi
        C_lin = C_red * C_xi + C_sym * C_dxi + Theta * C_Om * C_S
        C_E1 = NS * sK * (1 + sB) * g ** 2 * C_lin + tX * MQ * C_DK ** 2 + g * C_S * C_dK
        C_E2 = g * n * (2 * n * sK * g + Theta * C_Om) * cR * C_g + tX * MQ * C_DK ** 2
        C_E = max(C_E1, C_E2)
    C_G = 2 * n * sK * (n * (1 + th) + 1)
    C_B = thh * sB ** 2 * C_G
    C_Dab = 2 * thh ** 4 * 2 * n * M * sK ** 2 * sB ** 2 * (2 * C_B / sB + (n + 1) / sK + 1)
    C_Dc = thh ** 5 * sB ** 3 * w * 2 * n * sK * (n + thh)
    C_DT = (C_Dab + C_Dc) * C_DK + (1 + thh ** 3) * C_T1 * g ** 2 + (thh ** 5 + 1) * sB ** 3 * w * C_Om * g
    if iso:
        C_DT = max(C_DT + C_Dw, n * C_Dw + n * (1 + thh ** 2) * 2 * n * sK * sB * g ** 2)
    rates = {"ball": 2 * C_DK, "DK": n * C_DK, "B": C_B * C_DK, "twist": thh * sT ** 2 * C_DT}
    c_step = max(g ** 4 * (1 + C_T1) + C_T2 * g ** 3, C_sym * g ** 3 / F(qS),
                 n * C_DK * g ** 2 / (th * sK), sB * C_G * C_DK * g ** 2 / th, sT * C_DT * g ** 2 / th, C_E)
    c_sum = 4 * g ** 2 * max(rates.values())
    terms = {"E": F(2) ** int(2 * a) * C_E, "step": c_step, "sum": c_sum / mu}
    if iso:
        terms["nu"] = 4 * g ** 2 * C_Dw / nu
    c_star = max(terms.values())
    delta0 = min(F(1), (rho - rhoinf) / (2 * lam))
    return dict(a=a, delta0=delta0, c_star=c_star, terms=terms, C_DK=C_DK, gbar=gbar, rho=rho, tau=tau,
                active=max(terms, key=terms.get))


def cR_lean(n, tau):
    return TH.cohConstR_lean(n, tau)


def cR_freq(om, gamma, tau=1, delta0=0.005, kmax=1500):
    """sup over dyadic delta <= delta0 of gamma delta^tau 2^{n/2} (2 pi)^-1 S(om, delta)^{1/2}, n = 2,
    S = sum_{k != 0} |k.om|^-2 exp(-4 pi delta |k|_1): the Parseval bound with the exact divisors (estimate; the tail
    beyond kmax is negligible for delta >= delta0/64, and the sup is attained on the first few dyadic steps)."""
    import numpy as np
    k1, k2 = np.meshgrid(np.arange(-kmax, kmax + 1), np.arange(-kmax, kmax + 1), indexing="ij")
    k1 = k1.ravel().astype(float); k2 = k2.ravel().astype(float)
    nz = (k1 != 0) | (k2 != 0)
    k1, k2 = k1[nz], k2[nz]
    d = np.abs(k1 * om[0] + k2 * om[1])
    n1 = np.abs(k1) + np.abs(k2)
    best = 0.0
    for j in range(0, 7):
        dl = delta0 * 2.0 ** (-j)
        if 4 * math.pi * dl * kmax < 25:
            break
        S = float((np.exp(-4 * math.pi * dl * n1) / d ** 2).sum())
        best = max(best, gamma * dl ** tau * 2 / (2 * math.pi) * math.sqrt(S))
    return best


def columns(P, gamma, om=None, rhoinf_frac=1 / 1000, n=2, tau=1, nu=F(1, 10 ** 6), iso=True, kappa=None):
    """log10 thresholds for package P (dict with M, sK, sB, sT, mu, rho, M2, Tmax) at Diophantine constant gamma."""
    rho = Q(P["rho"], up=False)
    rhoinf = rho * F(rhoinf_frac).limit_denominator(10 ** 6)
    gam = Q(gamma, up=False)
    M, sK, sB, sT = Q(P["M"]), Q(P["sK"]), Q(P["sB"]), Q(P["sT"])
    mu = Q(P.get("mu", 1 / 160))
    gbar = gam
    res = {}
    m = max(M, sK, sB, sT, F(1))
    if iso:
        k0 = TH.current_iso(n=n, tau=tau, M=m, sK=m, sB=m, sT=m, mu=mu, nu=nu, rho=rho, rhoinf=rhoinf, gbar=gbar,
                            cR=max(F(1), TH.cohConst_crude(n, tau)))
    else:
        k0 = TH.current_fixed(n=n, tau=tau, M=m, sK=m, sB=m, sT=m, mu=mu, rho=rho, rhoinf=rhoinf, gbar=gbar,
                              cR=max(F(1), TH.cohConst_crude(n, tau)))
    res["current"] = TH.lg(TH.threshold(k0, gam))
    kap = tau if kappa is None else kappa
    cR = cR_lean(n, tau)
    k1 = TH.sharp(n=n, tau=tau, kappa=kap, cR=cR, M=M, sK=sK, sB=sB, sT=sT, mu=mu, rho=rho, rhoinf=rhoinf, gbar=gbar,
                  nu=nu, iso=iso)
    res["v1"] = TH.lg(TH.threshold(k1, gam))
    res["active_v1"] = k1["active"]
    HT = Q(P["Tmax"] * 1.05 + 1)
    M2 = Q(P["M2"])
    kv = sharp_mod(n, tau, kap, Q(0.036), M, sK, sB, sT, mu, rho, rhoinf, gbar, nu=nu, iso=iso, HT=HT, M2=M2)
    res["v2"] = TH.lg(TH.threshold(kv, gam))
    res["active_v2"] = kv["active"]
    if om is not None:
        cf = cR_freq(om, float(gamma), tau=1, delta0=float(k1["delta0"]))
        kvp = sharp_mod(n, tau, kap, Q(cf), M, sK, sB, sT, mu, rho, rhoinf, gbar, nu=nu, iso=iso, HT=HT, M2=M2)
        res["v2+"] = TH.lg(TH.threshold(kvp, gam))
        res["c_fs"] = cf
    kl = sharp_mod(n, tau, kap, Q(1 / (4 * math.pi ** 2 * math.e)), M, sK, sB, sT, mu, rho, rhoinf, gbar, nu=nu,
                   iso=iso, HT=HT, M2=M2)
    res["ell1"] = TH.lg(TH.threshold(kl, gam))
    return res


def digits_needed(log10_e, rho, a_min, c0=3.0, margin=2.0):
    """Truncation digits L: |c_k| >= 10^-L kept.  The invariance error on the strip is about
    10^(c0 - L (1 - w)), w = 2 pi rho/(ln 10 a_min) the strip weight per digit at the slowest decay a_min (digits per mode).
    Calibrated on SO-GEN2 (R1: log10 eta = -78, L = 88, rho = 1/70, a_min = 0.5)."""
    w = 2 * math.pi * rho / (math.log(10) * a_min)
    if w >= 0.9:
        return float("inf")
    return (-log10_e + margin + c0) / (1 - w)


if __name__ == "__main__":
    # reproduces the R1 row of APOST-SHARP-LEAN-DESIGN section 6 and shows the effect of each substitution
    p, gamma = TH.package_R1()
    P = dict(M=float(p["M"]), sK=float(p["sK"]), sB=float(p["sB"]), sT=float(p["sT"]), mu=float(p["mu"]),
             rho=float(p["rho"]), Tmax=1.2, M2=1.05 * 0.598 * 7 / 4)
    print({k: (round(v, 2) if isinstance(v, float) else v) for k, v in columns(P, float(gamma), om=(1.75 * 0.02462, 1.75)).items()})
