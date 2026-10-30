#!/usr/bin/env python3
"""Exact thresholds of the sharp a-posteriori theorems (design SHARP-DESIGN), lunar package R1.

Untrusted tooling (design numbers, not a certificate).  Every formula transcribes a constant of
  blueprint/parts/p2s-sharp.tex        (Definition bp:p2s:constants, fixed frequency)
  blueprint-I/parts/p2s-iso-sharp.tex  (Definition bpI:p2s:constants, isoenergetic)
and the planned Lean defs of docs/campaign/design/APOST-SHARP-LEAN-DESIGN.md (KAM.Sharp.*,
KAM.Iso.Sharp.*).  The current constants are those of KAM/Apost/Constants.lean and
KAM/Iso/Apost/Defs.lean (the iso ones copied from scripts/spin_orbit/exact_constants.py).

All arithmetic is exact (fractions.Fraction).  Irrational inputs (the cohomological constants c_R)
enter as rational upper bounds, rounded up at 10 significant digits (mpmath).

The threshold of a theorem is the largest e with C1 e/(gamma^4 rho^{4 tau}) < 1, i.e.
    threshold = gamma^4 rho^{4 tau} / C1 = gamma^4 delta0^{2a} / c_star   (when c_star delta0^{-2a} >= gbar^4).
Usage:  python3 -I scripts/apost_sharp/thresholds.py [--json OUT]
"""
from fractions import Fraction as F
import math, json, sys

try:
    import mpmath as mp
    mp.mp.dps = 40
except ImportError:                                   # pragma: no cover
    mp = None

def lg(q):
    q = F(q)
    return math.log10(q.numerator) - math.log10(q.denominator)

def up(x, digits=10):
    """A rational upper bound of the real number x (mpmath), 10 significant digits, rounded up."""
    x = mp.mpf(x)
    e = int(mp.floor(mp.log10(x))) - digits + 1
    m = int(mp.ceil(x / mp.mpf(10) ** e))
    return F(m) * (F(10) ** e)

# ---------------------------------------------------------------------------------------------
# cohomological constants c_R (Gamma_delta = c_R gamma^-1 delta^-kappa, 0 < delta <= 1)
# ---------------------------------------------------------------------------------------------

def cohConst_crude(n, tau):
    """KAM.cohConst n tau = (2 pi)^-1 (tau/(e pi))^tau (8 n/pi)^n (KAM/Strip/CohomologicalDefs.lean:31),
    exponent kappa = tau + n."""
    return up((2 * mp.pi) ** -1 * (mp.mpf(tau) / (mp.e * mp.pi)) ** tau * (8 * mp.mpf(n) / mp.pi) ** n)

def cohConstP_lean(n, tau):
    """KAM.cohConstP n tau = (2 pi)^-1 sqrt(2^n (2 tau/(e pi))^{2 tau} (8 n/pi)^n)
    (KAM/Strip/CohomologicalParsevalLattice.lean:33), exponent kappa = tau + n/2."""
    t = mp.mpf(tau)
    return up((2 * mp.pi) ** -1 * mp.sqrt(2 ** n * (2 * t / (mp.e * mp.pi)) ** (2 * t) * (8 * mp.mpf(n) / mp.pi) ** n))

def cohConstR_lean(n, tau):
    """KAM.cohConstR n tau = (2 pi)^-1 sqrt(2^n 6 (1 + 2^tau) (2 tau/(e pi))^{2 tau})
    (KAM/Strip/CohomologicalRussmannLattice.lean:195), exponent kappa = tau (Russmann), all delta > 0."""
    t = mp.mpf(tau)
    return up((2 * mp.pi) ** -1 * mp.sqrt(2 ** n * 6 * (1 + 2 ** t) * (2 * t / (mp.e * mp.pi)) ** (2 * t)))

def cohConst_parseval_n2(tau=1):
    """The optimal constant of the Parseval route for n = 2, tau = 1 (for comparison only):
    c = (2 pi)^-1 2^{n/2} sup_{0<delta<=1} (delta^{2 tau + n} sum_{k != 0} |k|_1^{2 tau} e^{-2 pi delta |k|_1})^{1/2},
    with #{|k|_1 = m} = 4m and sum_m m^3 x^m = x(1+4x+x^2)/(1-x)^4.  The sup is taken on a grid of
    step 10^-3 and multiplied by 1.001.  The Lean constant KAM.cohConstP 2 1 = 0.380 is cruder."""
    assert tau == 1
    def f(d):
        b = 2 * mp.pi * d; x = mp.e ** (-b)
        return d ** 4 * 4 * x * (1 + 4 * x + x * x) / (1 - x) ** 4
    s = max(f(mp.mpf(k) / 1000) for k in range(1, 1001)) * mp.mpf('1.001')
    return up((2 * mp.pi) ** -1 * 2 * mp.sqrt(s))

# ---------------------------------------------------------------------------------------------
# current theorems (transcriptions)
# ---------------------------------------------------------------------------------------------

def current_fixed(n, tau, M, sK, sB, sT, mu, rho, rhoinf, gbar, cR=F(1)):
    """KAM/Apost/Constants.lean (c_star) and KAM/Apost/G1.lean (C_1); cR = max 1 cohConst = 1 (n=2,tau=1)."""
    n = F(n); tau = F(tau)
    kappa = tau + n; a = 2 * kappa + 2
    m = max(F(1), M, sK, sB, sT)
    Theta = 4 * n * m ** 3
    C_X = 5 * n ** 2 * m ** 5; C_T = 2 * n * m ** 2 * C_X
    C_Omega = 2 * n * (n + 1) * cR * m; C_sym = m ** 2 * C_Omega; C_red = 2 * n * (n + 1) * m ** 2
    C_xi0 = 2 * n * m ** 2 * (m * Theta + cR * C_T); C_xiN = C_xi0 + 2 * n * cR * m
    C_g = C_T * C_xiN + 2 * n * m ** 2 * Theta; C_xi = cR * C_g + Theta * C_xiN
    C_DK = 2 * m ** 2 * C_xi; C_lin = C_red * C_xi + C_sym * C_g
    C_E = 4 * m ** 2 * Theta ** 2 * C_lin + m * C_DK ** 2
    C_G = 6 * n ** 2 * m; C_B = 2 * m ** 2 * C_G; C_DN = 2 * n * m + m * C_B
    C_DX = 2 * m ** 3 + (m + n * Theta) * C_DN; C_DT = 4 * n * m ** 2 * C_DX + 2 * n * C_DN * C_X
    c_step = 2 * Theta ** 4 * max(C_sym, 2 * m * C_DT * C_DK)
    c_sum = 4 * Theta ** 2 * C_DK * max(n, C_B, m ** 2 * C_DT)
    terms = {"E": F(2) ** int(2 * a) * C_E, "step": c_step * max(F(1), 2 / mu), "sum": 2 * c_sum / mu}
    c_star = max(terms.values())
    delta0 = min(F(1), (rho - rhoinf) / 8)
    return dict(a=a, delta0=delta0, c_star=c_star, terms=terms, C_DK=C_DK,
                active=max(terms, key=terms.get), gbar=gbar, rho=rho, tau=tau)

def current_iso(n, tau, M, sK, sB, sT, mu, nu, rho, rhoinf, gbar, cR=F(1)):
    """KAM/Iso/Apost/Defs.lean (hatcStar, isoC1), as scripts/spin_orbit/exact_constants.py."""
    n = F(n); tau = F(tau)
    kappa = tau + n; a = 2 * kappa + 2
    m = max(F(1), M, sK, sB, sT)
    Theta = 4 * n * m ** 3
    C_X = 5 * n ** 2 * m ** 5; C_T = 2 * n * m ** 2 * C_X
    C_Omega = 2 * n * (n + 1) * cR * m; C_sym = m ** 2 * C_Omega; C_red = 2 * n * (n + 1) * m ** 2
    C_xi0 = 2 * n * m ** 2 * (m * Theta + cR * C_T)
    C_G = 6 * n ** 2 * m; C_B = 2 * m ** 2 * C_G; C_DN = 2 * n * m + m * C_B
    C_DX = 2 * m ** 3 + (m + n * Theta) * C_DN; C_DT = 4 * n * m ** 2 * C_DX + 2 * n * C_DN * C_X
    hatCS = max(C_xi0, m * Theta + 2 * n * cR * m ** 5); hatCxiN = hatCS + 2 * n * cR * m
    hatCg = C_T * hatCxiN + Theta * hatCS + 2 * n * m ** 2 * Theta
    hatCxi = max(cR * hatCg, Theta * hatCxiN); hatCDK = 2 * m ** 2 * hatCxi
    hatCDelta = max(hatCDK, Theta ** 2 * hatCS)
    CP = m ** 2 + n + m ** 3 + C_X
    hatCpartial = CP * hatCxi + 2 * m ** 2 * Theta * hatCg
    hatClin = C_red * hatCxi + C_sym * hatCg + Theta * C_Omega * hatCS
    hatCE1 = 4 * m ** 2 * Theta ** 2 * hatClin + m * hatCDK ** 2 + Theta * hatCS * hatCpartial
    hatCE2 = n * Theta ** 2 * (2 * n * m + C_Omega) * cR * hatCg + m * hatCDK ** 2
    hatCE = max(hatCE1, hatCE2)
    CY = n * m * (2 * m ** 2 + C_DN); CDTbord = C_DT + 8 * n ** 2 * m ** 4 + 1 + CY
    hatcStep = 2 * Theta ** 3 * max(C_sym, m * CDTbord * hatCDelta)
    hatcSum = 4 * Theta ** 2 * hatCDelta * max(n, C_B, m ** 2 * CDTbord)
    terms = {"E": F(2) ** int(2 * a) * hatCE, "step": hatcStep * max(F(1), 2 / mu),
             "sum": 2 * hatcSum / mu, "nu": 4 * Theta ** 2 * hatCDelta / nu}
    c_star = max(terms.values())
    delta0 = min(F(1), (rho - rhoinf) / 8)
    return dict(a=a, delta0=delta0, c_star=c_star, terms=terms, C_DK=hatCDelta, C_Dw=hatCDelta,
                active=max(terms, key=terms.get), gbar=gbar, rho=rho, tau=tau)

# ---------------------------------------------------------------------------------------------
# sharp theorems (Definition bp:p2s:constants / bpI:p2s:constants)
# ---------------------------------------------------------------------------------------------

def sharp(n, tau, kappa, cR, M, sK, sB, sT, mu, rho, rhoinf, gbar, nu=None, iso=False,
          lam=3, theta=F(1, 8), qS=F(1, 2), tX=F(1, 2), absorb="gbar", cR_floor=False, step_mu=False):
    """The sharp constants.  Switches (for the intermediate variants of the table only):
       lam      loss per step lam * delta_s (3 in the design; 4 = the current schedule);
       theta    the smallness ratio of the perturbation lemmas (1/8 in the design; 1/2 = current);
       qS       the bound |E_sym| <= qS (1/2 in the design and currently); Neumann factor 1/(1-qS);
       tX       Taylor factor of the quadratic remainders (1/2 in the design; 1 = current);
       absorb   'gbar' (gamma delta^j <= gbar, design) or 'Theta' (gamma delta^j <= Theta, current);
       cR_floor use max(1, cR) (current) instead of cR;
       step_mu  the current structure c_step * max{1, 2/mu} (the ball condition inside c_step) instead of the
                split  c_step X <= 1,  2 d <= beta  of Proposition bp:p2s:step."""
    n = F(n); tau = F(tau); kappa = F(kappa)
    assert kappa >= 1 and kappa.denominator == 1
    if cR_floor:
        cR = max(F(1), cR)
    a = 2 * kappa
    th = F(theta); thh = 1 / (1 - th)              # vartheta, hat vartheta = 1/(1 - vartheta)
    NS = 1 / (1 - F(qS))
    Lt = 2 * n * sK                                 # |L^T|
    Theta = 2 * n * sK * sB * (M + 1)               # |omega| (Lemma bp:p2:frequency)
    g = gbar if absorb == "gbar" else Theta
    # geometry (Lemma bp:p2s:geometry)
    C_Om = 2 * n * (n + 1) * cR * sK
    C_sym = max(F(1), sB ** 2) * C_Om
    C_red = 2 * n * sK * max(n * sB, n + sB)
    # torsion (Lemma bp:p2s:torsion-bound)
    C_T0 = 4 * n * M * sK ** 2 * sB ** 2
    C_T1 = 2 * n ** 2 * sK * sB ** 2
    w = 4 * n * M * sK ** 2 + 2 * n * (n + 1) * sK
    C_T2 = F(2) ** int(kappa + 1) * C_Om * sB ** 3 * w
    H_T = C_T0 + 1
    # correction (Lemma bp:p2s:correction / bpI:p2s:correction)
    if not iso:
        C_S = 2 * n * sK * sT * (sB * g + cR * H_T)                     # C_xi0
        C_xiN = C_S + 2 * n * cR * sK
        C_g = H_T * C_xiN + 2 * n * sK * sB * g
    else:
        C_S = sT * max(2 * n * sK * sB * g + 2 * n * cR * sK * H_T, g + 2 * n * cR * M * sK ** 2 * sB)
        C_xiN = C_S + 2 * n * cR * sK
        C_g = H_T * C_xiN + Theta * C_S + 2 * n * sK * sB * g
    C_dxi = max(C_g, 2 * n * sK * g)
    C_xi = max(cR * C_g, g * C_xiN)
    C_DK = sK * (cR * C_g + sB * g * C_xiN)
    # new errors (Lemma bp:p2s:newton-error / bpI:p2s:newton-error)
    if not iso:
        C_lin = C_red * C_xi + C_sym * C_dxi
        C_E = NS * sK * (1 + sB) * g ** 2 * C_lin + tX * M * C_DK ** 2
        C_Dw = None
    else:
        C_Dw = Theta * g * C_S
        C_P = (M * sK + n) * (1 + sB) + 2 * n * sK ** 2 * sB ** 2 * (2 * M * sK + n + 1)
        C_dK = C_P * C_xi + sK * (1 + sB) * g * C_dxi
        C_lin = C_red * C_xi + C_sym * C_dxi + Theta * C_Om * C_S
        C_E1 = NS * sK * (1 + sB) * g ** 2 * C_lin + tX * M * C_DK ** 2 + g * C_S * C_dK
        C_E2 = g * n * (2 * n * sK * g + Theta * C_Om) * cR * C_g + tX * M * C_DK ** 2
        C_E = max(C_E1, C_E2)
    # perturbation (Lemma bp:p2s:perturbation)
    C_G = 2 * n * sK * (n * (1 + th) + 1)
    C_B = thh * sB ** 2 * C_G
    C_Dab = 2 * thh ** 4 * 2 * n * M * sK ** 2 * sB ** 2 * (2 * C_B / sB + (n + 1) / sK + 1)
    C_Dc = thh ** 5 * sB ** 3 * w * 2 * n * sK * (n + thh)
    C_DT = (C_Dab + C_Dc) * C_DK + (1 + thh ** 3) * C_T1 * g ** 2 + (thh ** 5 + 1) * sB ** 3 * w * C_Om * g
    if iso:
        C_DT = max(C_DT + C_Dw, n * C_Dw + n * (1 + thh ** 2) * 2 * n * sK * sB * g ** 2)
    rates = {"ball": C_DK, "DK": n * C_DK, "B": C_B * C_DK, "twist": thh * sT ** 2 * C_DT}
    c_step = max(g ** 4 * (1 + C_T1) + C_T2 * g ** 3, C_sym * g ** 3 / F(qS),
                 n * C_DK * g ** 2 / (th * sK), sB * C_G * C_DK * g ** 2 / th, sT * C_DT * g ** 2 / th, C_E)
    if step_mu:
        c_step = max(c_step, 2 * C_DK * g ** 2)
        c_sum = 4 * g ** 2 * max(rates.values())
        terms = {"E": F(2) ** int(2 * a) * C_E, "step": c_step * max(F(1), 2 / mu), "sum": c_sum / mu}
    else:
        rates["ball"] = 2 * C_DK                    # budget mu/4 for the ball (Proposition bp:p2s:engine-iteration)
        c_sum = 4 * g ** 2 * max(rates.values())
        terms = {"E": F(2) ** int(2 * a) * C_E, "step": c_step, "sum": c_sum / mu}
    if iso:
        terms["nu"] = 4 * g ** 2 * C_Dw / nu
    c_star = max(terms.values())
    delta0 = min(F(1), (rho - rhoinf) / (2 * lam))
    return dict(a=a, delta0=delta0, c_star=c_star, terms=terms, C_DK=C_DK, C_Dw=C_Dw, C_E=C_E,
                H_T=H_T, active=max(terms, key=terms.get), gbar=gbar, rho=rho, tau=tau,
                rate_max=max(rates, key=rates.get))

def threshold(k, gamma):
    """gamma^4 rho^{4 tau} / C1 with C1 = rho^{4 tau} max{gbar^4, c_star delta0^{-2a}}."""
    C1n = max(k["gbar"] ** 4, k["c_star"] / k["delta0"] ** int(2 * k["a"]))
    return gamma ** 4 / C1n

# ---------------------------------------------------------------------------------------------
# package R1 (CONSTANTS-STUDY section 2.2; owner ruling O5)
# ---------------------------------------------------------------------------------------------

def package_R1(mu=F(1, 160)):
    """Rotated frame, rho' = 1/70, rho_inf = rho'/1000, time scale c = 7/4, s = 1 + 10^-6,
    gamma = gbar = c/(42 s), nu = 10^-6.  Norm majorants = sampled sup x 1.05 (x c for M,
    / c for the torsion inverse) + mu where the hypothesis carries the margin:
    M >= 1.05 * 1.047 * 7/4 = 153909/80000 = 1.9238625 (taken as 1.924), sK = 1.05 * 1.303 + mu, sB = 1.05 * 1.833 + mu,
    sT = 1.05 * 1.022 / (7/4) + mu (CONSTANTS-STUDY 2.2 lists 1.92, 1.37, 1.93, 0.62 at mu = 1/160; here M is rounded up)."""
    c = F(7, 4); s = 1 + F(1, 10 ** 6)
    gamma = c / (42 * s)
    M = F(1924, 1000)
    sK = F(105, 100) * F(1303, 1000) + mu
    sB = F(105, 100) * F(1833, 1000) + mu
    sT = F(105, 100) * F(1022, 1000) / c + mu
    rho = F(1, 70)
    return dict(n=2, tau=1, rho=rho, rhoinf=rho / 1000, M=M, sK=sK, sB=sB, sT=sT, mu=mu,
                nu=F(1, 10 ** 6), gbar=gamma), gamma

def table(out=None):
    rows = []
    p, gamma = package_R1()
    m = F(39, 20)                                   # one-size: m >= max{1, M, sK, sB, sT} of R1 (a conservative upper bound; the max is sB = 19309/10000)
    one = dict(M=m, sK=m, sB=m, sT=m)
    sep = dict(M=p["M"], sK=p["sK"], sB=p["sB"], sT=p["sT"])
    base = dict(n=2, tau=1, mu=p["mu"], rho=p["rho"], rhoinf=p["rhoinf"], gbar=p["gbar"])
    crude = dict(lam=4, theta=F(1, 2), qS=F(1, 2), tX=F(1), absorb="Theta", cR_floor=True, step_mu=True)
    cC, cP, cR = cohConst_crude(2, 1), cohConstP_lean(2, 1), cohConstR_lean(2, 1)
    variants = [
        ("V0 current theorem (KAM.Apost / KAM.Iso.Apost g1_explicit)", None),
        ("V1 torsion route only (kappa = tau+n, one size m, Theta-absorption, 4 delta)",
         dict(kappa=3, cR=cC, **one, **crude)),
        ("V2 + Parseval (kappa = tau+n/2, cohConstP)", dict(kappa=2, cR=cP, **one, **crude)),
        ("V3 + Russmann instead (kappa = tau, cohConstR)", dict(kappa=1, cR=cR, **one, **crude)),
        ("V4 + 3 delta schedule", dict(kappa=1, cR=cR, **one, **dict(crude, lam=3))),
        ("V5 + separate norms M, sK, sB, sT", dict(kappa=1, cR=cR, **sep, **dict(crude, lam=3))),
        ("V6 + gbar-absorption (gamma delta^j <= gbar)",
         dict(kappa=1, cR=cR, **sep, **dict(crude, lam=3, absorb="gbar"))),
        ("V7 + c_R itself (no max{1, c_R})",
         dict(kappa=1, cR=cR, **sep, **dict(crude, lam=3, absorb="gbar", cR_floor=False))),
        ("V8 = design, Russmann (headline): + ratio 1/8, Taylor M/2, step smallness without 2/mu",
         dict(kappa=1, cR=cR, **sep)),
        ("design, Parseval instance (kappa = tau+n/2, cohConstP)", dict(kappa=2, cR=cP, **sep)),
        ("design, crude instance (kappa = tau+n, cohConst)", dict(kappa=3, cR=cC, **sep)),
    ]
    for name, kw in variants:
        for iso in (False, True):
            if kw is None:
                if iso:
                    k = current_iso(M=one["M"], sK=m, sB=m, sT=m, nu=p["nu"], **base)
                else:
                    k = current_fixed(M=one["M"], sK=m, sB=m, sT=m, **base)
            else:
                k = sharp(nu=p["nu"], iso=iso, **base, **kw)
            thr = threshold(k, gamma)
            rows.append(dict(variant=name, form="iso" if iso else "fixed", log10_threshold=round(lg(thr), 2),
                             active=k["active"], a=str(k["a"]), delta0=float(k["delta0"]),
                             log10_c_star=round(lg(k["c_star"]), 2),
                             log10_C2=round(lg(2 * k["C_DK"] * p["rho"] ** 2 / k["delta0"] ** int(k["a"])), 2),
                             terms={kk: round(lg(v), 2) for kk, v in k["terms"].items()}))
    return rows

def sensitivity():
    """Design, Russmann instance (iso) against c_R, mu and the ratio vartheta."""
    out = []
    p, gamma = package_R1()
    for name, cR in (("cohConstR 2 1 (Lean)", cohConstR_lean(2, 1)), ("c_R = 0.1", F(1, 10)), ("c_R = 1", F(1))):
        k = sharp(n=2, tau=1, kappa=1, cR=cR, M=p["M"], sK=p["sK"], sB=p["sB"], sT=p["sT"], mu=p["mu"],
                  rho=p["rho"], rhoinf=p["rhoinf"], gbar=p["gbar"], nu=p["nu"], iso=True)
        out.append(("c_R: " + name, float(cR), round(lg(threshold(k, gamma)), 2), k["active"]))
    for mu in (F(1, 320), F(1, 160), F(1, 80), F(1, 40), F(1, 20)):
        p2, gamma2 = package_R1(mu)
        k = sharp(n=2, tau=1, kappa=1, cR=cohConstR_lean(2, 1), M=p2["M"], sK=p2["sK"], sB=p2["sB"], sT=p2["sT"],
                  mu=mu, rho=p2["rho"], rhoinf=p2["rhoinf"], gbar=p2["gbar"], nu=p2["nu"], iso=True)
        out.append(("mu = %s" % mu, float(mu), round(lg(threshold(k, gamma2)), 2), k["active"]))
    for th in (F(1, 16), F(1, 4), F(1, 2)):
        k = sharp(n=2, tau=1, kappa=1, cR=cohConstR_lean(2, 1), M=p["M"], sK=p["sK"], sB=p["sB"], sT=p["sT"],
                  mu=p["mu"], rho=p["rho"], rhoinf=p["rhoinf"], gbar=p["gbar"], nu=p["nu"], iso=True, theta=th)
        out.append(("vartheta = %s" % th, float(th), round(lg(threshold(k, gamma)), 2), k["active"]))
    return out

def main():
    print("c_R: cohConstR 2 1 =", float(cohConstR_lean(2, 1)), " cohConstP 2 1 =", float(cohConstP_lean(2, 1)),
          " cohConst 2 1 =", float(cohConst_crude(2, 1)),
          " (Parseval route-optimal, for comparison:", float(cohConst_parseval_n2()), ")")
    rows = table()
    print()
    print("| variant | form | log10 threshold | active branch | a | log10 c_* | log10 C_2 | log10 branches |")
    print("|---|---|---:|---|---:|---:|---:|---|")
    for r in rows:
        print("| %s | %s | %.2f | %s | %s | %.2f | %.2f | %s |" % (r["variant"], r["form"], r["log10_threshold"],
              r["active"], r["a"], r["log10_c_star"], r["log10_C2"],
              ", ".join("%s %.2f" % kv for kv in r["terms"].items())))
    print()
    print("Sensitivity of the design (Russmann instance, iso):")
    print("| input | value | log10 threshold | active |")
    print("|---|---:|---:|---|")
    sens = sensitivity()
    for s_ in sens:
        print("| %s | %.4g | %.2f | %s |" % s_)
    if len(sys.argv) > 2 and sys.argv[1] == "--json":
        json.dump(dict(rows=rows, sensitivity=sens), open(sys.argv[2], "w"), indent=1)

if __name__ == "__main__":
    main()
