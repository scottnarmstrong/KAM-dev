#!/usr/bin/env python3
"""Haro-Luque 2019 (arXiv:1711.05515v1, "A-posteriori KAM theory with optimal estimates for partially integrable
systems") evaluated exactly on the lunar package R1, next to our theorems.

Untrusted tooling (design numbers, not a certificate).  All arithmetic is exact (fractions.Fraction); c_R enters as
a rational upper bound.  Every HL19 constant is transcribed from Appendix B (Tables 1-5) and cited by its equation
number; the specialisation is the canonical case of Remark 3.3 (Omega = Omega~ = J = Omega0, G = I_2n), d = n
(Remark 3.2: no extra first integrals, all c_{Xp,*}, c_{p,*} = 0), which is HL19's Case III (Section 2.5:
J^2 = -I, hence A = 0 and every constant marked * in the tables vanishes).

Data mapping (our frozen hypotheses -> HL19's H1-H5, H1', H4', H5'):
  c_{Xh,0} >= |X_h|, c_{Xh,1} >= |DX_h|, c_{Xh,2} >= |D^2 X_h|      <- M (one size) or M0, M1, M2 (finer data)
  c_{Xh^T,1} >= |DX_h^T|                                              <- M1 (canonical: (DX_h)^T = Om0 DX_h Om0)
  c_{c,1} >= |Dh|, c_{c,2} >= |D^2 h|   (Theorem 3.6 with c = h, Remark 3.7)   <- M or Mh1, Mh2
  sigma_K, sigma_K^T (H2), sigma_B (H3), sigma_T (H4) / sigma_Tc (H4')   <- sigma's (two mappings, see below)
  omega in D_{gamma,tau} (H5), ray Theta(omega*, sigma_omega) (H5')      <- the same gamma, tau, omega*, sigma_omega
  dist(K(T_rho), dB)                                                      <- the ball radius mu of the frozen statement
  dist(omega, dTheta)                                                     <- the ray margin nu of the frozen statement
HL19's conclusion is weaker than ours (|DK_inf| < sigma_K, dist > 0, versus |DK_inf| <= sigma_K - mu/2 and a ball of
radius mu/2).  Two readings are evaluated:
  'as stated'   HL19 with sigma_HL = sigma, margins mu (generous to HL19: it does not deliver our margins);
  'normalised'  HL19 applied with sigma_HL = sigma - mu/2 and the domain shrunk by mu/2, so that its conclusion
                implies ours (margins mu/2): the like-for-like comparison.
Free parameters: a1 > 1 (optimised on a grid), a2 = rho/rho_inf (fixed by the package), nu_HL > ||E||/delta (the
smallness (4.40); chosen self-consistently at the threshold, its effect is ~1e-20 relative).
The small-divisor constant c_R of Lemma 4.1 is an input: the same value is given to every theorem.

Usage:  python3 -I scripts/apost_sharp/benchmark_hl19.py [--json OUT]
"""
from fractions import Fraction as F
import json, math, os, sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import thresholds as v1  # noqa: E402  (scripts/apost_sharp/thresholds.py)

lg = v1.lg


def hl19(d, cR, a1, nuHL, iso=False):
    """HL19 Theorem 3.1 (iso=False) or 3.6 (iso=True), canonical case, d = n, Case III.
    d: dict with n, tau, rho, rhoinf, gamma, cX0, cX1, cX2, cXT1, sK, sKT, sB, sT (strict bounds of H2-H4/H4'),
       DK, DKT, Bact, Tinv (actual values of ||DK||, ||DK^T||, ||B||, |<T>^-1| or |<Tc>^-1|), dist (domain margin),
       iso only: cc1, cc2, omstar (|omega*|), sigom (sigma_omega), distom (dist(omega, dTheta)).
    Returns the constants C1, C2 (and C3 for iso) and the threshold gamma^4 rho^{4 tau}/C1."""
    n = F(d["n"]); tau = F(d["tau"]); g = F(d["gamma"]); rho = F(d["rho"])
    a2 = rho / F(d["rhoinf"])
    a1 = F(a1)
    a3 = 3 * a1 / (a1 - 1) * a2 / (a2 - 1)                      # Section 5.3, p. 42
    delta = rho / a3                                            # delta_0 = rho_0/a_3; constants taken at delta_0
    assert tau.denominator == 1
    t = int(tau)
    gd = g * delta ** t                                         # gamma delta^tau
    cX0, cX1, cX2, cXT1 = (F(d[k]) for k in ("cX0", "cX1", "cX2", "cXT1"))
    sK, sKT, sB, sT = (F(d[k]) for k in ("sK", "sKT", "sB", "sT"))
    nu = F(nuHL); dn = n                                        # d = n
    # ---- Table 1 (Section 4) ----
    C_LOmK = 2 * n * sK + dn * sKT                              # (4.14): 2n c_{Om,0} sK + sKT c_{Om,1} sK delta + d sKT c_{Om,0}
    C_OmK = cR * C_LOmK                                         # (4.15)
    C_L = sK                                                    # (4.23): sK + c_{Xp,0}
    C_LT = sKT                                                  # (4.24): max{sKT, c_{Xp^T,0}}
    C_OmL = cR * C_LOmK                                         # (4.25): cR max{C_LOmK + c_{p^T,1}, d c_{p,1}}
    C_N0 = C_L                                                  # (4.31): c_{J,0} C_L
    C_N0T = C_LT                                                # (4.32): C_L^T c_{J^T,0}
    C_A = F(0)                                                  # (4.33)*, Case III
    C_N = C_L * C_A + C_N0 * sB                                 # (4.34)
    C_NT = C_A * C_LT + sB * C_N0T                              # (4.35)
    C_sym = (1 + C_A) * max(F(1), C_A + sB ** 2) * C_OmL        # (4.39), chi_0(C_A) = 1
    C_LK = delta * nu + cX0                                     # (4.44)
    C_LL = dn * nu + cX1 * sK                                   # (4.45)
    C_LLT = 2 * n * nu + cXT1 * sKT                             # (4.46): max{2n nu + c_{Xh^T,1} sKT, c_{Xp^T,1} C_LK}
    C_LN0 = C_LL                                                # (4.51): C_LJ C_L + c_{J,0} C_LL, C_LJ = c_{J,1} C_LK = 0
    C_LGL = C_LLT * C_L + C_LT * C_LL                           # (4.52), C_LG = c_{G,1} C_LK = 0
    C_LB = sB ** 2 * C_LGL                                      # (4.54)
    C_LA = F(0)                                                 # (4.55)*
    C_LN = C_LL * C_A + C_L * C_LA + C_LN0 * sB + C_N0 * C_LB  # (4.56)
    C_XL = dn                                                   # (4.57): d + c_{Xp,1} delta
    C_XLT = 2 * n                                               # (4.58): max{2n, c_{Xp^T,1} delta}
    C_XN = C_XL * nu * C_A + cX1 * C_N0 * sB + C_L * C_LA + C_LN0 * sB + C_N0 * C_LB   # (4.59)
    C_T = C_NT * C_XN                                           # (4.60): C_N^T c_{Om,0} C_XN
    C_LOmL = C_LOmK                                             # (4.69)
    Cr11 = C_NT * C_XL                                          # (4.70)
    Cr21 = C_LT * C_XL                                          # (4.71)
    Cr22 = (C_XLT * C_N + C_LOmL * C_A) * gd + C_OmL * C_LA     # (4.72): (C_L^T c_{Om,1} C_N delta + C_XL^T c_{Om,0} C_N + C_LOmL C_A) gd + C_OmL C_LA
    C_red = max(Cr11 * gd, Cr21 * gd + Cr22)                    # (4.73)
    # ---- Table 2 (Lemma 5.2) / Table 4 (Lemma 6.2) ----
    if not iso:
        C_xi0 = sT * (C_NT * gd + cR * C_T * C_LT)              # (5.20)
    else:
        cc1 = F(d["cc1"])
        C_xi0 = sT * max(C_NT * gd + cR * C_T * C_LT, gd + cR * cc1 * C_N * C_LT)   # (6.29), sigma_Tc = sT
        C_xiw = C_xi0                                           # (6.29)
        C_om = F(d["sigom"]) * F(d["omstar"])                   # (6.30)
        C_Dw = C_om * C_xi0                                     # (6.31)
    C_xiN = C_xi0 + cR * C_LT                                   # (5.21)
    C_xiL = cR * (C_NT * gd + C_T * C_xiN)                      # (5.22)
    C_xi = max(C_xiL, C_xiN * gd)                               # (5.23)
    C_DK = C_L * C_xiL + C_N * C_xiN * gd                       # (5.24)
    C_LxiN = C_LT                                               # (5.26)
    C_LxiL = C_NT * gd + C_T * C_xiN + (C_om * C_xiw if iso else 0)   # (5.27) / (6.33)
    C_Lxi = max(C_LxiL, C_LxiN * gd)                            # (5.28)
    C_lin = C_red * C_xi + C_sym * C_Lxi * gd                   # (5.29)
    if iso:
        C_lin += max(C_A, F(1)) * C_OmL * C_om * C_xiw          # (6.34)
    C_LDK = C_LL * C_xiL + (C_L * C_LxiL + C_LN * C_xiN) * gd + C_N * C_LxiN * gd ** 2   # (5.51) / (6.36)
    C_E = 2 * (C_L + C_N) * C_lin * g * delta ** (t - 1) + cX2 * C_DK ** 2 / 2   # (5.32)
    if iso:
        C_E += C_xiw * C_LDK * gd                               # (6.37)
        C_linw = dn * cR * cc1 * C_xiL                          # (6.35)
        C_Ew = C_linw * g * delta ** (t - 1) + F(d["cc2"]) * C_DK ** 2 / 2   # (6.38)
        C_E = max(C_E, C_Ew)                                    # (6.39)
    C_DL = dn * C_DK                                            # (5.36)
    C_DLT = 2 * n * C_DK                                        # (5.37)
    C_DGL = C_LT * C_DL + C_DLT * C_L                           # (5.39), C_DG = c_{G,1} C_DK = 0
    C_DB = 2 * sB ** 2 * C_DGL                                  # (5.41)
    C_DA = F(0)                                                 # (5.44)*
    C_DN0 = C_DL                                                # (5.47): c_{J,0} C_DL + C_DJ C_L delta, C_DJ = 0
    C_DN0T = C_DLT                                              # (5.48)
    C_DN = C_L * C_DA + C_DL * C_A + C_N0 * C_DB + C_DN0 * sB   # (5.49)
    C_DNT = C_A * C_DLT + C_DA * C_LT + C_DB * C_N0T + sB * C_DN0T   # (5.50)
    C_DLK = C_LDK                                               # (5.51)
    if iso:
        C_DLK = F(d["sigom"]) * C_xiw * C_LK * gd + C_LDK       # (6.42)
    C_DLL = dn * C_DLK                                          # (5.52)
    C_DLLT = 2 * n * C_DLK                                      # (5.53)
    C_DLGL = C_LLT * C_DL + C_DLLT * C_L + C_LT * C_DLL + C_DLT * C_LL   # (5.56), c_{G,1} = c_{G,2} = 0
    C_DLB = 2 * sB * C_LGL * C_DB + sB ** 2 * C_DLGL            # (5.57)
    C_DLN0 = C_DLL                                              # (5.62)
    C_DLN = C_LN0 * C_DB + C_DLN0 * sB + C_N0 * C_DLB + C_DN0 * C_LB   # (5.63), exact transcription (C_LN0 = C_LL, C_N0 = C_L)
    C_DXN = cX1 * C_DN + cX2 * C_DK * C_N * delta + C_DLN       # (5.64)
    C_DT = C_NT * C_DXN + C_DNT * C_XN                          # (5.65), c_{Om,1} = 0
    if iso:
        C_DT = max(C_DT + C_Dw * g * delta ** (t + 1), F(d["cc1"]) * C_DN + F(d["cc2"]) * C_DK * C_N * delta)  # (6.43)
    C_DTinv = 2 * sT ** 2 * C_DT                                # (5.67) / (6.44)
    # ---- Table 3 / Table 5 ----
    C_D1 = max(dn * C_DK / (sK - F(d["DK"])), 2 * n * C_DK / (sKT - F(d["DKT"])),
               C_DB / (sB - F(d["Bact"])), C_DTinv / (sT - F(d["Tinv"])))          # (5.75) / (6.46)
    C_D2 = C_DK * delta / F(d["dist"])                          # (5.76) / (6.47)
    branches = {"nu": g ** 2 * delta ** (2 * t) / nu, "sym": 2 * C_sym * gd,
                "D1": C_D1 / (1 - a1 ** (1 - 2 * t)), "D2": C_D2 / (1 - a1 ** (-2 * t))}
    if iso:
        C_D3 = C_Dw * g * delta ** (t + 1) / F(d["distom"])     # (6.48)
        branches["D3"] = C_D3 / (1 - a1 ** (-3 * t))            # (6.49)
    # The entry gamma^2 delta^{2 tau}/nu_HL of (5.77) encodes (4.40), ||E||/delta < nu_HL; nu_HL is free and is chosen
    # just above e/delta_0 (best_hl19), so that entry holds by construction and is left out of the max here.
    branches.pop("nu")
    C_Delta = max(branches.values())                            # (5.77) / (6.49)
    C1 = max((a1 * a3) ** (4 * t) * C_E, a3 ** (2 * t + 1) * g ** 2 * rho ** (2 * t - 1) * C_Delta)   # (5.74) / (6.45)
    C2 = a3 ** (2 * t) * C_DK / (1 - a1 ** (-2 * t))            # (5.78) / (6.50)
    out = dict(C1=C1, C2=C2, threshold=g ** 4 * rho ** (4 * t) / C1, a1=a1, a3=a3, delta0=delta,
               C_T=C_T, C_DK=C_DK, C_E=C_E, C_DT=C_DT, C_Delta=C_Delta,
               E_branch=(a1 * a3) ** (4 * t) * C_E,
               Delta_branch=a3 ** (2 * t + 1) * g ** 2 * rho ** (2 * t - 1) * C_Delta,
               Delta_active=max(branches, key=branches.get))
    if iso:
        out["C3"] = a3 ** t * C_Dw / (1 - a1 ** (-3 * t))       # (6.51): |omega_inf - omega| < C3 e/(gamma rho^tau)
        out["C_Dw"] = C_Dw
    return out


def best_hl19(d, cR, iso=False, grid=None):
    """Optimise a1 on a grid; nu_HL self-consistent (nu_HL = (1 + 1e-9) e*/delta0, fixed-point iteration)."""
    grid = grid or [F(k, 100) for k in range(110, 401, 5)]
    best = None
    for a1 in grid:
        nu = F(1, 10 ** 6)
        for _ in range(3):
            r = hl19(d, cR, a1, nu, iso)
            nu = r["threshold"] / r["delta0"] * (1 + F(1, 10 ** 9))   # (4.40) holds for every e below the threshold
        r = hl19(d, cR, a1, nu, iso)
        assert r["threshold"] < r["delta0"] * nu
        if best is None or r["threshold"] > best["threshold"]:
            best = r
    return best


def r1_data(mode, finer=False, iso=False):
    """Package R1 in HL19's variables.  mode: 'stated' or 'normalised' (see module docstring).
    finer=False: v1's information (one size M; sigma_K^T = 2n sigma_K; c_{Xh^T,1} = M).
    finer=True: the measured separate majorants (scripts/apost_sharp/r1_norms.py, sampled sup x 1.05 (+ mu where
    the frozen hypothesis carries the margin)): M0 = M1 = 1.05 * 1.75, M2 = 1.05 * 1.0342, |Dh| = 1.05 * 1.8228,
    |D^2 h| = 1.05 * 1.8323 (all scaled by c = 7/4), sigma_K^T = 1.05 * 1.3268 + mu."""
    p, gamma = v1.package_R1()
    mu = p["mu"]
    n = 2
    if finer:
        M0 = M1 = F(105, 100) * F(175, 100)
        M2 = F(105, 100) * F(10342, 10000)
        Mh1, Mh2 = F(105, 100) * F(18228, 10000), F(105, 100) * F(18323, 10000)
        sKT = F(105, 100) * F(13268, 10000) + mu
    else:
        M0 = M1 = M2 = Mh1 = Mh2 = p["M"]
        sKT = 2 * n * p["sK"]
    sh = mu / 2 if mode == "normalised" else F(0)
    d = dict(n=n, tau=1, rho=p["rho"], rhoinf=p["rhoinf"], gamma=gamma, cX0=M0, cX1=M1, cX2=M2, cXT1=M1,
             sK=p["sK"] - sh, sKT=sKT - sh, sB=p["sB"] - sh, sT=p["sT"] - sh,
             DK=p["sK"] - mu, DKT=sKT - (2 * n * mu if not finer else mu), Bact=p["sB"] - mu, Tinv=p["sT"] - mu,
             dist=mu - sh)
    if iso:
        c = F(7, 4); s = 1 + F(1, 10 ** 6)
        d.update(cc1=Mh1, cc2=Mh2, omstar=c / s, sigom=F(2), distom=p["nu"])   # |omega*| = c/s (max norm), sigma_omega = 2
    return d


def main():
    cRs = [("cohConstR 2 1 (v1 headline data)", v1.cohConstR_lean(2, 1))]
    p, gamma = v1.package_R1()
    rows = []
    # our theorems (v1 mirror)
    m = F(39, 20)
    base = dict(n=2, tau=1, mu=p["mu"], rho=p["rho"], rhoinf=p["rhoinf"], gbar=p["gbar"])
    cur = {False: v1.current_fixed(M=m, sK=m, sB=m, sT=m, **base),
           True: v1.current_iso(M=m, sK=m, sB=m, sT=m, nu=p["nu"], **base)}
    sep = dict(M=p["M"], sK=p["sK"], sB=p["sB"], sT=p["sT"])
    sh = {iso: v1.sharp(kappa=1, cR=v1.cohConstR_lean(2, 1), nu=p["nu"], iso=iso, **base, **sep)
          for iso in (False, True)}
    print("HL19 (arXiv:1711.05515v1) on package R1, canonical case d = n = 2, Case III; c_R = cohConstR 2 1 = %.5f"
          % float(v1.cohConstR_lean(2, 1)))
    print()
    print("| theorem | form | data | log10 threshold | log10 C2-type closeness coeff. | note |")
    print("|---|---|---|---:|---:|---|")
    for iso in (False, True):
        form = "iso (Thm 3.6)" if iso else "fixed (Thm 3.1)"
        k = cur[iso]
        rows.append(dict(theorem="sealed g1_explicit (current)", form=form, data="v1",
                         log10_threshold=round(lg(v1.threshold(k, gamma)), 2)))
        k = sh[iso]
        rows.append(dict(theorem="v1 sharp design (Russmann data)", form=form, data="v1",
                         log10_threshold=round(lg(v1.threshold(k, gamma)), 2),
                         log10_C2=round(lg(2 * k["C_DK"] / k["delta0"] ** int(k["a"])), 2)))
        for finer in (False, True):
            for mode in ("stated", "normalised"):
                r = best_hl19(r1_data(mode, finer, iso), v1.cohConstR_lean(2, 1), iso)
                rows.append(dict(theorem="HL19 %s" % ("Thm 3.6" if iso else "Thm 3.1"), form=form,
                                 data=("finer" if finer else "v1") + ", " + mode,
                                 log10_threshold=round(lg(r["threshold"]), 2),
                                 log10_C2=round(lg(r["C2"] / p["rho"] ** 2), 2),
                                 a1=float(r["a1"]), C_T=float(r["C_T"]), C_DK=float(r["C_DK"]),
                                 log10_C_E=round(lg(r["C_E"]), 2),
                                 active="E" if r["E_branch"] >= r["Delta_branch"] else "Delta:" + r["Delta_active"]))
    for r in rows:
        note = ""
        if "a1" in r:
            note = "a1 = %.2f, C_T = %.4g, C_DK = %.4g, log10 C_E = %.2f, active %s" % (
                r["a1"], r["C_T"], r["C_DK"], r["log10_C_E"], r["active"])
        print("| %s | %s | %s | %.2f | %s | %s |" % (r["theorem"], r["form"], r["data"], r["log10_threshold"],
              ("%.2f" % r["log10_C2"]) if "log10_C2" in r else "-", note))
    print()
    print("closeness coefficient: the factor K in |K_inf - K| <= K e (C2/(gamma^2 rho^2) without the 1/gamma^2 for")
    print("HL19 and for v1: log10 of C2 rho^{-2 tau}; same normalisation for both).")
    if len(sys.argv) > 2 and sys.argv[1] == "--json":
        json.dump(dict(rows=rows), open(sys.argv[2], "w"), indent=1)


if __name__ == "__main__":
    main()
