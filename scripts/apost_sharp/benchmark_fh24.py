#!/usr/bin/env python3
"""Figueras-Haro 2024 (arXiv:2304.10205v1, "A modified parameterization method for invariant Lagrangian tori for
partially integrable Hamiltonian systems", Physica D 462 (2024) 134127) evaluated exactly on the lunar package R1.

Untrusted tooling (design numbers, not a certificate).  All arithmetic is exact (fractions.Fraction); the irrational
small-divisor constants enter as rational upper bounds (thresholds.up, 10 significant digits rounded up).

Transcription.  Every constant of Appendix B (Tables 1-4) is transcribed in fh24() and cited by its equation label;
the formulas were checked against the PDF (pp. 36-39), not only the text extraction.  The general constants of H1
(c_Omega, c_G, c_J, ..., c_Xp, ..., c_DPhi) are kept, with the defaults CANONICAL of the canonical case d = n
(Remarks 2.20, 2.21: Omega = Omega0, G = I_2n, J = Omega0, no extra first integrals; then sigma_L = sigma_DK and
sigma_L^T = sigma_(DK)^T, H2).  Theorem 2.18: if C/(gamma delta^{tau+1}) eps < 1 with
    eps := max{||eta^L||_rho, ||eta^N||_rho/(gamma delta^tau)},  eta^L = -N^T Omega E,  eta^N = L^T Omega E   (2.24)
then an invariant torus exists, with ||K_inf - K||_{rho_inf} <= C_{Delta K}/(gamma delta^tau) eps   (2.32).
By p. 19 (before Lemma 3.3), ||eta^L|| <= sigma_N^T c_Omega e and ||eta^N|| <= sigma_L^T c_Omega e (e = ||E||_rho),
hence eps <= c_Omega max{sigma_N^T, sigma_L^T/(gamma delta^tau)} e; this gives threshold_e and the closeness
coefficient per unit e.

Free parameters (H3, Theorem 2.18): the bite delta in ]0, (rho - rho_inf)/3[ (a = (rho - rho_inf)/(rho - 3 delta -
rho_inf), (3.88)), nu in ]0,1[ (Lemma 3.3), and the two control constants of H3, typeset differently in the PDF:
    kappa1 = varkappa (\\varkappa): the entry 1/varkappa of (3.27), (3.99); it bounds eps/(gamma delta^{tau+1})
             ((3.95)) and enters Q_{eta^N} through (3.80).  H3 asks only varkappa > 0; we take it in ]0,1[.
    kappa2 = kappa (\\kappa): the entry a^{tau+1} Q_eta/kappa of (3.99) ((3.91)) and the factors a/(a - kappa),
             1/(1 - kappa) of (3.100)-(3.101).
Small divisors: Section 3.3 (p. 31) replaces c_R(delta_j), c^1_R(delta_j) by uniform bounds; cR and cR1 are inputs,
and the same cR is used for c_R(rho) in C^N_{xi0^N} (3.45).

Suspected errata (see the report; switch errata=True applies the one that changes numbers in the canonical case):
  E1 Lemma 2.14: the last inequality is false as printed (the middle line carries pi^{-2 tau}, the last
     pi^{-2 tau - 2}) and the definition of c_R(delta) lacks the factor (2 pi)^{-2} under the root (u_k = -v_k/(2 pi i
     k.omega)).  With it, the Russmann ordering argument and exact Abel summation give
     sqrt(2^{d-1-2 tau} zeta(2, 2^tau) pi^{-2 tau-2} Gamma(2 tau+1)) = hat c_R / 2.  The printed hat c_R is still a
     valid (conservative) bound.  cR_hat_fh24 returns the printed value, cR_hat_halved the corrected one.
  E2 (3.72): N^T = B L^T J^T, so the bound of (N-bbar)^T - N^T needs sigma_L^T and C_{Delta L-bbar^T}; the table
     prints sigma_L (twice) and C_{Delta L-bbar} (which does not bound the transposed norm in general).  In the
     canonical case the printed (3.72) coincides with (3.71).
Norm convention: FH24's matrix norm is max_i sum_j ||M_ij||_rho (Section 2.7: row sums of entrywise sups), which
dominates the sup of the pointwise row-sum norm used for our sigma's; on R1 the two agree for L, B, N and differ by
5% for L^T, N^T, inside the 1.05 safety factor of the finer data (scratch measurement with r1_norms.objects).
Usage:  python3 -I scripts/apost_sharp/benchmark_fh24.py [--json OUT]
"""
from fractions import Fraction as F
import json, os, sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import thresholds as v1  # noqa: E402  (scripts/apost_sharp/thresholds.py: lg, up, mpmath, package_R1)

lg, up, mp = v1.lg, v1.up, v1.mp

# Remarks 2.20 (d = n: c_Xp = c_Xp^T = c_DXp = c_DXp^T = 0, c_DPhi = 1) and 2.21 (canonical case).
CANONICAL = dict(c_Om=1, c_DOm=0, c_G=1, c_DG=0, c_J=1, c_DJ=0, c_JT=1, c_DJT=0,
                 c_Xp=0, c_XpT=0, c_DXp=0, c_DXpT=0, c_DPhi=1)


def cR_hat_fh24(n, tau):
    """hat c_R of Lemma 2.14 as printed, with d = n:  sqrt(2^{d+1-2 tau} zeta(2, 2^tau) pi^{-2 tau-2} Gamma(2 tau+1)),
    zeta(a, b) the Hurwitz zeta function.  Rational upper bound.  (Erratum E1: twice the classical constant.)"""
    t = mp.mpf(tau)
    return up(mp.sqrt(mp.mpf(2) ** (n + 1 - 2 * t) * mp.zeta(2, mp.mpf(2) ** t) * mp.pi ** (-2 * t - 2)
                      * mp.gamma(2 * t + 1)))


def cR_hat_halved(n, tau):
    """The corrected classical constant (erratum E1): sqrt(2^{d-1-2 tau} zeta(2, 2^tau) pi^{-2 tau-2} Gamma(2 tau+1))."""
    t = mp.mpf(tau)
    return up(mp.sqrt(mp.mpf(2) ** (n - 1 - 2 * t) * mp.zeta(2, mp.mpf(2) ** t) * mp.pi ** (-2 * t - 2)
                      * mp.gamma(2 * t + 1)))


def cR1_fh24(cR, tau):
    """Corollary 2.16 (2.22): c^1_R = (tau+1)^{tau+1}/tau^tau c_R (exact for integer tau); 4 c_R for tau = 1."""
    t = int(tau)
    assert t == tau and t >= 1
    return F(t + 1) ** (t + 1) / F(t) ** t * F(cR)


def fh24(d, cR, cR1, delta, nu, kappa1, kappa2, exact=True, errata=False):
    """Theorem 2.18 constants (Appendix B, Tables 1-4) for the data d and the free parameters.
    d: dict with n, tau, rho, rhoinf, gamma; c_Xh, c_DXh, c_DXhT (|(DX_h)^T|), c_D2Xh, c_Th, c_DTh (H1);
       s_DK, s_DKT, s_B, s_N, s_NT, s_Tinv (strict bounds of H2); the actual values DK, DKT, B, N, NT, Tinv
       (||DK||_rho, ||(DK)^T||_rho, ||B||_rho, ||N||_rho, ||N^T||_rho, |<T>^-1|); dist = dist(K(T_rho), dU0);
       optionally dim (the torus dimension, the paper's d; default n) and any key of CANONICAL.
    cR, cR1: the uniform small-divisor constants (Lemma 2.14, Corollary 2.16).
    kappa1 = varkappa (entry 1/varkappa), kappa2 = kappa (entry a^{tau+1} Q/kappa); see the module docstring.
    exact=False evaluates the same formulas in floating point (used by the grid search only).
    errata=True applies erratum E2 to (3.72)."""
    num = F if exact else float
    D = dict(CANONICAL)
    D.update(d)
    v = {k: num(x) for k, x in D.items()}
    n, rho, rhoinf, g = v["n"], v["rho"], v["rhoinf"], v["gamma"]
    dim = v.get("dim", n)
    t = int(D["tau"])
    assert t == D["tau"] and t >= dim - 1 and int(n) == n and int(dim) == dim
    delta, nu, k1, k2, cR, cR1 = num(delta), num(nu), num(kappa1), num(kappa2), num(cR), num(cR1)
    half = num(1) / 2
    c_Om, c_DOm, c_G, c_DG = v["c_Om"], v["c_DOm"], v["c_G"], v["c_DG"]
    c_J, c_DJ, c_JT, c_DJT = v["c_J"], v["c_DJ"], v["c_JT"], v["c_DJT"]
    c_Xp, c_XpT, c_DXp, c_DXpT, c_DPhi = v["c_Xp"], v["c_XpT"], v["c_DXp"], v["c_DXpT"], v["c_DPhi"]
    c_Xh, c_DXh, c_DXhT, c_D2Xh, c_Th, c_DTh = (v[k] for k in ("c_Xh", "c_DXh", "c_DXhT", "c_D2Xh", "c_Th", "c_DTh"))
    sDK, sDKT, sB, sN, sNT, sTi = (v[k] for k in ("s_DK", "s_DKT", "s_B", "s_N", "s_NT", "s_Tinv"))
    # standing conditions: H2 (strict bounds), H3, the bite, small-divisor constants
    margins = {"DK": sDK - v["DK"], "DKT": sDKT - v["DKT"], "B": sB - v["B"], "N": sN - v["N"],
               "NT": sNT - v["NT"], "Tinv": sTi - v["Tinv"]}
    assert all(m > 0 for m in margins.values()), margins
    assert v["dist"] > 0 and g > 0 and cR > 0 and cR1 > 0
    assert 0 < rhoinf < rho and 0 < delta < (rho - rhoinf) / 3
    assert 0 < nu < 1 and 0 < k1 < 1 and 0 < k2 < 1
    sL = sDK + c_Xp                                             # H2: sigma_L = sigma_DK + c_Xp
    sLT = max(sDKT, c_XpT)                                      # H2: sigma_L^T = max{sigma_(DK)^T, c_Xp^T}
    gd = g * delta ** t                                         # gamma delta^tau
    cRrho = cR                                                  # c_R(rho) <= uniform bound (Section 3.3, p. 31)
    # ---- Table 1 (Section 3.1, Lemmas 3.1-3.5) ----
    C_OmL = (dim + n - 2) * cR1                                 # (3.2)  C^N_{Omega_L}
    C_OmN = sB ** 2 * C_OmL                                     # (3.3)  C^N_{Omega_N}
    C_sym = max(C_OmL, C_OmN)                                   # (3.7)
    CL_E = (sL + sN * nu) / (1 - nu ** 2)                       # (3.9)
    CN_E = (sN + sL * nu) / (1 - nu ** 2)
    C_E = CL_E + gd * CN_E
    CL_ET = n * (sLT + nu * sNT) / (1 - nu ** 2)                # (3.10)
    CN_ET = n * (sNT + nu * sLT) / (1 - nu ** 2)
    C_ET = CL_ET + gd * CN_ET                                   # (printed "C_E =", a typo for C_{E^T})
    f_DE = 1 + c_Om * (sNT * CL_E + sLT * CN_E)                 # (3.11)
    CL_DE, CN_DE = dim * f_DE * CL_E, dim * f_DE * CN_E
    C_DE = CL_DE + gd * CN_DE
    f_DET = 1 + c_Om * (sN * CL_ET + sL * CN_ET)                # (3.12)
    CL_DET, CN_DET = n * f_DET * CL_ET, n * f_DET * CN_ET
    C_DET = CL_DET + gd * CN_DET
    C_LK = C_E * delta * nu + c_Xh                              # (3.14)
    C_LL = C_DE * nu + c_DXp * C_E * delta * nu + c_DXh * sL    # (3.15)
    C_LLT = max(C_DET * nu, c_DXpT * C_E * delta * nu) + sLT * c_DXhT   # (3.16)
    C_LGL = C_LLT * c_G * sL + sLT * c_DG * C_LK * sL + sLT * c_G * C_LL   # (3.17)
    C_LB = sB ** 2 * C_LGL                                      # (3.18)
    C_LN = c_DJ * C_LK * sL * sB + c_J * C_LL * sB + c_J * sL * C_LB   # (3.19)
    C_T = sNT * c_Th * sN                                       # (3.20)
    CL_ELL = dim + (dim + delta * c_DXp) * sNT * c_Om * CL_E    # (3.22) (not used further)
    CN_ELL = (dim + delta * c_DXp) * sNT * c_Om * CN_E
    CL_ENL = (dim + delta * c_DXp) * sLT * c_Om * CL_E          # (3.23)
    CN_ENL = dim + (dim + delta * c_DXp) * sLT * c_Om * CN_E
    CL_ENN = delta * sLT * c_DOm * CL_E * sN + max(n + dim * CL_E * c_Om * sNT, delta * c_DXpT * CL_E * c_Om * sN)  # (3.24)
    CN_ENN = delta * sLT * c_DOm * CN_E * sN + max(dim * CN_E * c_Om * sNT, delta * c_DXpT * CN_E * c_Om * sN)
    C_ENN = CL_ENN + gd * CN_ENN
    CL_ELN = delta * sB ** 2 * sLT * c_G * c_DJ * sL * CL_E + sB ** 2 * CL_ENL   # (3.25)
    CN_ELN = gd * delta * sB ** 2 * sLT * c_G * c_DJ * sL * CN_E + gd * sB ** 2 * CN_ENL + sB * C_OmL * C_LB
    C_ELN = CL_ELN + CN_ELN
    # ---- Table 2 (Lemma 3.6, steps 1 and 2) ----
    CL_xi0 = sTi                                                # (3.45)
    CN_xi0 = (delta / rho) ** t * sTi * C_T * cRrho
    C_xi0 = CL_xi0 + CN_xi0
    CL_xiN, CN_xiN = CL_xi0, CN_xi0 + cR                        # (3.46)
    C_xiN = CL_xiN + CN_xiN
    CL_dKb, CN_dKb = sN * CL_xiN, sN * CN_xiN                   # (3.47)  K-bar - K
    C_dKb = CL_dKb + CN_dKb
    CL_dDKb, CN_dDKb = dim * sN * CL_xi0, dim * sN * (CN_xi0 + cR1)   # (3.49)
    C_dDKb = CL_dDKb + CN_dDKb
    CL_dDKTb, CN_dDKTb = n * sNT * CL_xi0, n * sNT * (CN_xi0 + cR1)   # (3.50)
    C_dDKTb = CL_dDKTb + CN_dDKTb
    CL_dLb, CN_dLb = CL_dDKb + delta * c_DXp * CL_dKb, CN_dDKb + delta * c_DXp * CN_dKb   # (3.54)
    C_dLb = CL_dLb + CN_dLb
    CL_dLTb = max(CL_dDKTb, delta * c_DXpT * CL_dKb)            # (3.55)
    CN_dLTb = max(CN_dDKTb, delta * c_DXpT * CN_dKb)
    C_dLTb = CL_dLTb + CN_dLTb
    CL_Eb = CL_E + c_DXh * CL_dKb + C_LN * CL_xiN               # (3.56)
    CN_Eb = gd * (CN_E + sN) + c_DXh * CN_dKb + C_LN * CN_xiN
    C_Eb = CL_Eb + CN_Eb
    Q_etaNb = ((C_dLTb * c_Om + delta * sLT * c_DOm * C_dKb) * C_Eb + C_ENN * C_xiN
               + delta * sLT * c_Om * half * c_D2Xh * C_dKb ** 2)   # (3.59)
    # ---- Table 3 (Lemma 3.6, steps 3 and 4) ----
    CL_xiL, CN_xiL = cR * (1 + C_T * CL_xiN), cR * C_T * CN_xiN   # (3.61)
    C_xiL = CL_xiL + CN_xiL
    CL_dK, CN_dK = c_DPhi * sL * CL_xiL + gd * CL_dKb, c_DPhi * sL * CN_xiL + gd * CN_dKb   # (3.64)  K-bbar - K
    C_dK = CL_dK + CN_dK
    CL_dDK = dim * c_DPhi * sL * CL_xiL + gd * CL_dDKb          # (3.65)
    CN_dDK = dim * c_DPhi * sL * CN_xiL + gd * CN_dDKb
    C_dDK = CL_dDK + CN_dDK
    CL_dDKT = 2 * n * c_DPhi * sL * CL_xiL + gd * CL_dDKTb      # (3.66)
    CN_dDKT = 2 * n * c_DPhi * sL * CN_xiL + gd * CN_dDKTb
    C_dDKT = CL_dDKT + CN_dDKT
    CL_dL, CN_dL = CL_dDK + delta * c_DXp * CL_dK, CN_dDK + delta * c_DXp * CN_dK   # (3.67)
    C_dL = CL_dL + CN_dL
    CL_dLT = max(CL_dDKT, delta * c_DXpT * CL_dK)               # (3.68)
    CN_dLT = max(CN_dDKT, delta * c_DXpT * CN_dK)
    C_dLT = CL_dLT + CN_dLT
    CL_dG = CL_dLT * c_G * sL + delta * sLT * c_DG * CL_dK * sL + sLT * c_G * CL_dL   # (3.69)
    CN_dG = CN_dLT * c_G * sL + delta * sLT * c_DG * CN_dK * sL + sLT * c_G * CN_dL
    C_dG = CL_dG + CN_dG
    CL_dB, CN_dB, C_dB = sB ** 2 * CL_dG, sB ** 2 * CN_dG, sB ** 2 * C_dG   # (3.70)
    CL_dN = delta * c_DJ * CL_dK * sL * sB + c_J * CL_dL * sB + c_J * sL * CL_dB   # (3.71)
    CN_dN = delta * c_DJ * CN_dK * sL * sB + c_J * CN_dL * sB + c_J * sL * CN_dB
    C_dN = CL_dN + CN_dN
    if not errata:                                              # (3.72) as printed
        CL_dNT = delta * sB * sL * c_DJT * CL_dK + sB * CL_dL * c_JT + CL_dB * sL * c_JT
        CN_dNT = delta * sB * sL * c_DJT * CN_dK + sB * CN_dL * c_JT + CN_dB * sL * c_JT
    else:                                                       # (3.72) with erratum E2 (N^T = B L^T J^T)
        CL_dNT = delta * sB * sLT * c_DJT * CL_dK + sB * CL_dLT * c_JT + CL_dB * sLT * c_JT
        CN_dNT = delta * sB * sLT * c_DJT * CN_dK + sB * CN_dLT * c_JT + CN_dB * sLT * c_JT
    C_dNT = CL_dNT + CN_dNT
    CL_dT = CL_dNT * c_Th * sN + delta * sNT * c_DTh * CL_dK * sN + sNT * c_Th * CL_dN   # (3.73)
    CN_dT = CN_dNT * c_Th * sN + delta * sNT * c_DTh * CN_dK * sN + sNT * c_Th * CN_dN
    C_dT = CL_dT + CN_dT
    C_dTi = sTi ** 2 * C_dT                                     # (3.74)
    CL_LxiL, CN_LxiL = 1 + C_T * CL_xiN, C_T * CN_xiN           # (3.77)
    C_LxiL = CL_LxiL + CN_LxiL
    CL_Ebb, CN_Ebb = c_DPhi * (CL_Eb + sL * CL_LxiL), c_DPhi * (CN_Eb + sL * CN_LxiL)   # (3.78)
    C_Ebb = CL_Ebb + CN_Ebb
    Q_etaN = (1 + n) * (1 + C_OmL * C_LxiL * k1) * Q_etaNb      # (3.80)  (varkappa)
    Q_L1 = C_ELN * C_xiN + delta * sNT * c_Om * half * c_D2Xh * C_dKb ** 2 + gd * C_OmN   # (3.82)
    Q_L2 = sNT * c_Om * dim * C_Eb * C_xiL                      # (3.83)
    Q_L3 = sNT * c_Om * (dim * sL * C_xiL + gd * C_dLb) * C_LxiL   # (3.84)
    Q_L4 = sNT * c_Om * c_DXp * c_DPhi * C_xiL * (C_Eb + sL * C_LxiL)   # (3.85)
    Q_L5 = (C_dNT * c_Om + delta * sNT * c_DOm * C_dK) * C_Ebb  # (3.86)
    Q_etaL = gd * Q_L1 + Q_L2 + Q_L3 + delta * Q_L4 + Q_L5      # (3.87)
    # ---- Table 4 (Theorem 2.18, Section 3.3) ----
    a = (rho - rhoinf) / (rho - 3 * delta - rhoinf)             # (3.88)
    Q_eta = max(Q_etaL, a ** t * Q_etaN)                        # (3.89)
    CC = {"K": a / (a - k2) * C_dK, "DK": C_dDK / (1 - k2), "DKT": C_dDKT / (1 - k2),   # (3.100)
          "B": C_dB / (1 - k2), "N": C_dN / (1 - k2), "NT": C_dNT / (1 - k2), "Tinv": C_dTi / (1 - k2)}   # (3.101)
    entries = {"sym": gd * max(1, C_sym) / nu,                  # (3.99), in order
               "xiL": C_xiL,
               "dist": delta * CC["K"] / v["dist"],
               "DK": CC["DK"] / margins["DK"], "DKT": CC["DKT"] / margins["DKT"],
               "B": CC["B"] / margins["B"], "N": CC["N"] / margins["N"], "NT": CC["NT"] / margins["NT"],
               "Tinv": CC["Tinv"] / margins["Tinv"],
               "varkappa": 1 / k1,
               "Q": a ** (t + 1) * Q_eta / k2}
    C = max(entries.values())
    thr_eta = g * delta ** (t + 1) / C                          # (2.24): eps < gamma delta^{tau+1}/C
    eta_per_e = c_Om * max(sNT, sLT / gd)                       # p. 19: eps <= c_Om max{sigma_N^T, sigma_L^T/(gamma delta^tau)} e
    ranked = sorted(entries, key=entries.get, reverse=True)
    return dict(C=C, entries=entries, active=ranked[0], runner_up=ranked[1], a=a, delta=delta, nu=nu,
                kappa1=k1, kappa2=k2, threshold_eta=thr_eta, eta_per_e=eta_per_e, threshold_e=thr_eta / eta_per_e,
                closeness_eta=CC["K"] / gd,                     # (2.32): ||K_inf - K|| <= closeness_eta * eps
                closeness_e=CC["K"] / gd * eta_per_e,           # ... <= closeness_e * e
                CC=CC, Q_eta=Q_eta, Q_etaL=Q_etaL, Q_etaN=Q_etaN, Q_etaNb=Q_etaNb,
                Q_L=dict(L1=Q_L1, L2=Q_L2, L3=Q_L3, L4=Q_L4, L5=Q_L5),
                C_OmL=C_OmL, C_OmN=C_OmN, C_sym=C_sym, CL_E=CL_E, CN_E=CN_E, C_E=C_E, C_ET=C_ET, C_DE=C_DE,
                C_DET=C_DET, C_LK=C_LK, C_LL=C_LL, C_LLT=C_LLT, C_LGL=C_LGL, C_LB=C_LB, C_LN=C_LN, C_T=C_T,
                C_ELL=CL_ELL + gd * CN_ELL, C_ENL=CL_ENL + gd * CN_ENL, C_ENN=C_ENN, C_ELN=C_ELN,
                C_xi0=C_xi0, CL_xiN=CL_xiN, CN_xiN=CN_xiN, C_xiN=C_xiN, C_dKb=C_dKb, C_dDKb=C_dDKb,
                C_dDKTb=C_dDKTb, C_dLb=C_dLb, C_dLTb=C_dLTb, C_Eb=C_Eb, C_xiL=C_xiL, C_dK=C_dK, C_dDK=C_dDK,
                C_dDKT=C_dDKT, C_dL=C_dL, C_dLT=C_dLT, C_dG=C_dG, C_dB=C_dB, C_dN=C_dN, C_dNT=C_dNT, C_dT=C_dT,
                C_dTi=C_dTi, C_LxiL=C_LxiL, C_Ebb=C_Ebb)


def _grid_t(lo, hi, steps):
    return [lo + (hi - lo) * F(k, steps) for k in range(1, steps)]


def best_fh24(d, cR, cR1, errata=False):
    """Maximise threshold_e over the free parameters on grids: delta = t (rho - rho_inf)/3 and kappa on the grid
    k/40 (0 < k < 40), nu and varkappa on the logarithmic grid m 10^-j (m = 1, 2, 5; 0 < j <= 24).  Search: (nu,
    varkappa) by coordinate descent at t = kappa = 1/2; the full (delta, kappa) grid; a coordinate descent over all
    four grids; joint local refinement of (delta, kappa) on 17 x 17 grids of steps 1/200, 1/800, 1/3200.  Finally nu and
    varkappa are moved off the crossings of the entries gamma delta^tau max{1, C_sym}/nu and 1/varkappa with C (C
    depends on them elsewhere only through tiny terms) when this loses less than 1e-6 (relative), so that the reported
    active entry is a genuine constraint.  The search runs in floating point; the constants are recomputed exactly at
    the rational optimum."""
    D = (F(d["rho"]) - F(d["rhoinf"])) / 3
    logg = sorted({F(m, 10 ** j) for j in range(1, 25) for m in (1, 2, 5)} | {F(1, 2), F(1, 5)})
    obj = lambda p: fh24(d, cR, cR1, p[0] * D, p[1], p[2], p[3], exact=False, errata=errata)["threshold_e"]

    def descend(p, grids):
        best = obj(p)
        for _ in range(4):
            moved = False
            for i, gr in enumerate(grids):
                for x in gr:
                    q = list(p); q[i] = x
                    val = obj(q)
                    if val > best:
                        best, p, moved = val, q, True
            if not moved:
                break
        return p, best

    tk = _grid_t(F(0), F(1), 40)
    p, best = descend([F(1, 2), F(1, 10 ** 6), F(1, 10 ** 6), F(1, 2)], [[F(1, 2)], logg, logg, [F(1, 2)]])
    for t0 in tk:                                               # full (delta, kappa) grid at that (nu, varkappa)
        for k0 in tk:
            q = [t0, p[1], p[2], k0]
            val = obj(q)
            if val > best:
                p, best = q, val
    p, best = descend(p, [tk, logg, logg, tk])                  # global coordinate descent
    for step in (F(1, 200), F(1, 800), F(1, 3200)):             # local refinement: joint (delta, kappa) grid (the
        for _ in range(3):                                      # optimum sits on a ridge Q = Tinv of the max, where
            p0 = p                                              # coordinate moves stall), then (nu, varkappa)
            for tj in [p0[0] + j * step for j in range(-8, 9) if 0 < p0[0] + j * step < 1]:
                for kj in [p0[3] + j * step for j in range(-8, 9) if 0 < p0[3] + j * step < 1]:
                    q = [tj, p0[1], p0[2], kj]
                    val = obj(q)
                    if val > best:
                        p, best = q, val
            p, best = descend(p, [[p[0]], logg, logg, [p[3]]])
            if p == p0:
                break
    for i in (1, 2):                                            # detach nu, varkappa from their crossings: C depends
        for f in (10 ** 4, 10 ** 3, 10 ** 2, 10, 5, 2):         # on them only through tiny terms there, so take the
            q = list(p); q[i] = p[i] * f                        # largest value losing < 1e-6 (relative)
            if q[i] < 1 and obj(q) >= best * (1 - 1e-6):
                p = q
                break
    r = fh24(d, cR, cR1, p[0] * D, p[1], p[2], p[3], exact=True, errata=errata)
    r["t"] = p[0]                                               # delta = t (rho - rho_inf)/3
    return r


def r1_data(mode, finer=False):
    """Package R1 in FH24's variables (canonical case, d = n = 2).  mode: 'stated' or 'normalised', as in
    scripts/apost_sharp/benchmark_hl19.py: 'stated' takes FH24's strict bounds sigma = ours and the domain margin mu
    (generous to FH24, whose conclusion ||DK_inf|| < sigma_DK, dist > 0 is weaker than ours); 'normalised' takes
    sigma - mu/2 for every sigma and dist = mu/2, so that FH24's conclusion implies ours (margins mu/2).
    Actual values: sigma - mu, or sigma - 2 n mu for the transposes of the v1 data (sigma_(DK)^T = 2 n sigma_K, sigma_N^T
    = 2 n sigma_K sigma_B).
    finer=False (v1 data): c_Xh = c_DXh = c_(DXh)^T = c_D2Xh = M; c_Th = 2M (canonical T_h = Omega0 DX_h - DX_h Omega0,
      |Omega0 A - A Omega0| <= 2|A|); c_DTh = 2M (|D T_h| <= 2|D^2 X_h|); sigma_DK = sigma_K, sigma_(DK)^T = 2 n sigma_K,
      sigma_N = sigma_K sigma_B, sigma_N^T = 2 n sigma_K sigma_B (Remark 2.19, c_J = c_J^T = 1).
    finer=True (scripts/apost_sharp/r1_norms.py, sampled sup x 1.05 (+ mu where the hypothesis carries the margin)):
      |X_h| = |DX_h| = |(DX_h)^T| = 1.05 * 1.75, |D^2 X_h| = 1.05 * 1.0342, sigma_(DK)^T = 1.05 * 1.3268 + mu,
      sigma_N = 1.05 * 1.354 + mu, sigma_N^T = 1.05 * 1.3787 + mu.  For H' = c (P1^2/2 - P1 + P2 + V(Q1 + Q2, Q2)),
      h_qp = 0 and h_pp = c diag(1, 0) =: C, so T_h = [[A - C, 0], [0, C - A]] with A = c V_QQ: |T_h| <= c max(g2_0 + 1,
      g2_1) = 1.82011 (g2_i the row sums of the cosh majorants of |V_QQ| in r1_norms.H_parts), c_Th = 1.05 * 1.8202;
      and D T_h = diag(DA, -DA) while D^2 X_h = [[0, 0], [-DA, 0]], so |D T_h| = |D^2 X_h|: c_DTh = 1.05 * 1.0342."""
    p, gamma = v1.package_R1()
    mu, n = p["mu"], 2
    sK, sB, sT = p["sK"], p["sB"], p["sT"]
    if finer:
        cX = cDX = F(105, 100) * F(175, 100)
        cD2X = F(105, 100) * F(10342, 10000)
        cTh, cDTh = F(105, 100) * F(18202, 10000), cD2X
        sKT = F(105, 100) * F(13268, 10000) + mu
        sN = F(105, 100) * F(1354, 1000) + mu
        sNT = F(105, 100) * F(13787, 10000) + mu
        mT = mu                                                 # margin of the transposes
    else:
        cX = cDX = cD2X = p["M"]
        cTh = cDTh = 2 * p["M"]
        sKT, sN, sNT = 2 * n * sK, sK * sB, 2 * n * sK * sB
        mT = 2 * n * mu
    sh = mu / 2 if mode == "normalised" else F(0)
    return dict(n=n, tau=1, rho=p["rho"], rhoinf=p["rhoinf"], gamma=gamma,
                c_Xh=cX, c_DXh=cDX, c_DXhT=cDX, c_D2Xh=cD2X, c_Th=cTh, c_DTh=cDTh,
                s_DK=sK - sh, s_DKT=sKT - sh, s_B=sB - sh, s_N=sN - sh, s_NT=sNT - sh, s_Tinv=sT - sh,
                DK=sK - mu, DKT=sKT - mT, B=sB - mu, N=sN - mu, NT=sNT - mT, Tinv=sT - mu, dist=mu - sh)


def main():
    p, gamma = v1.package_R1()
    cRs = [("(a) cohConstR 2 1", v1.cohConstR_lean(2, 1)),
           ("(b) classical 0.0814", F(814, 10000)),
           ("(c) FH24 hat c_R", cR_hat_fh24(2, 1))]
    print("FH24 (arXiv:2304.10205v1) Theorem 2.18 on package R1, canonical case d = n = 2, tau = 1; c^1_R = 4 c_R.")
    print("hat c_R(2,1): printed %.6f, halved (erratum E1) %.6f; cohConstR 2 1 = %.6f"
          % (float(cR_hat_fh24(2, 1)), float(cR_hat_halved(2, 1)), float(v1.cohConstR_lean(2, 1))))
    sh = v1.sharp(n=2, tau=1, kappa=1, cR=v1.cohConstR_lean(2, 1), M=p["M"], sK=p["sK"], sB=p["sB"], sT=p["sT"],
                  mu=p["mu"], rho=p["rho"], rhoinf=p["rhoinf"], gbar=p["gbar"])
    print("for orientation: v1 sharp design (fixed frequency, Russmann data) log10 threshold = %.2f"
          % lg(v1.threshold(sh, gamma)))
    print()
    print("| reading | data | c_R | t = 3 delta/(rho - rho_inf) | a | nu | varkappa | kappa | log10 thr_e "
          "| log10 thr_eta | log10 closeness/e | log10 gamma^2 closeness/e | active entry of (3.99) (runner-up, dex below) "
          "| log10 thr_e, (3.72) corrected |")
    print("|---|---|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---|---:|")
    rows = []
    for mode in ("stated", "normalised"):
        for finer in (False, True):
            d = r1_data(mode, finer)
            for name, cR in cRs:
                cR1 = cR1_fh24(cR, 1)
                r = best_fh24(d, cR, cR1)
                rc = best_fh24(d, cR, cR1, errata=True)
                row = dict(reading=mode, data="finer" if finer else "v1", cR=name, cR_value=float(cR),
                           t=str(r["t"]), a=float(r["a"]), nu=str(r["nu"]), varkappa=str(r["kappa1"]),
                           kappa=str(r["kappa2"]), log10_threshold_e=round(lg(r["threshold_e"]), 2),
                           log10_threshold_eta=round(lg(r["threshold_eta"]), 2),
                           log10_closeness_e=round(lg(r["closeness_e"]), 2),
                           log10_gamma2_closeness_e=round(lg(gamma ** 2 * r["closeness_e"]), 2),
                           active=r["active"], runner_up=r["runner_up"],
                           runner_up_gap=round(lg(r["C"] / r["entries"][r["runner_up"]]), 3), log10_C=round(lg(r["C"]), 2),
                           entries={k: round(lg(x), 2) for k, x in r["entries"].items()},
                           log10_threshold_e_corrected=round(lg(rc["threshold_e"]), 2), active_corrected=rc["active"])
                rows.append(row)
                print("| %s | %s | %s (%.5f) | %s | %.3f | %s | %s | %s | %.2f | %.2f | %.2f | %.2f | %s (%s -%.3f) "
                      "| %.2f (%s) |"
                      % (mode, row["data"], name, float(cR), row["t"], row["a"], row["nu"], row["varkappa"],
                         row["kappa"], row["log10_threshold_e"], row["log10_threshold_eta"],
                         row["log10_closeness_e"], row["log10_gamma2_closeness_e"], row["active"],
                         row["runner_up"], row["runner_up_gap"],
                         row["log10_threshold_e_corrected"], row["active_corrected"]))
    print()
    print("log10 of the entries of (3.99) at the optimum (row order as above):")
    for r in rows:
        print("  %s/%s/%s: log10 C = %.2f; %s" % (r["reading"], r["data"], r["cR"], r["log10_C"],
              ", ".join("%s %.2f" % kv for kv in r["entries"].items())))
    print()
    print("thr_e: largest e = ||E||_rho with C/(gamma delta^{tau+1}) eps < 1 guaranteed via eps <= c_Om max{sigma_N^T,")
    print("sigma_L^T/(gamma delta^tau)} e; closeness/e: ||K_inf - K|| <= coefficient * e by (2.32); the gamma^2 column")
    print("matches the normalisation of benchmark_hl19.py (C2 rho^{-2 tau}).")
    if len(sys.argv) > 2 and sys.argv[1] == "--json":
        json.dump(dict(rows=rows), open(sys.argv[2], "w"), indent=1)


if __name__ == "__main__":
    main()
