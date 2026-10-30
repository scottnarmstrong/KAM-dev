#!/usr/bin/env python3
"""Dominance check of the v2 design against the explicit a-posteriori KAM theorems for flows (APOST-SHARP-V2.md, 6).

Untrusted tooling (design numbers).  On a grid of data covering realistic certificates and on the packages R1, H50,
compare the threshold (largest admissible invariance error e) and the closeness coefficient of
  v2       the better of route A (additive, v1 + levers) and route B (modified step) of thresholds_v2.py, using ONLY
           the information the competitors use (one size M = sigma's, sigma_K^T = 2n sigma_K, sigma_N = sigma_K sigma_B,
           sigma_N^T = 2n sigma_K sigma_B, derived torsion, the classical small-divisor constant, no measured objects);
  HL19     Haro-Luque 2019 Theorem 3.1 (benchmark_hl19.py), a1 optimised;
  FH24     Figueras-Haro 2024 Theorem 2.18 (benchmark_fh24.py), delta, nu and the two control constants optimised,
           as printed and with erratum E2 corrected (the printed (3.72) is not a valid bound in general).
Every competitor receives the same small-divisor constant as v2 (the classical constant c^natural(n, tau), which is
smaller than FH24's printed hat c_R) and the like-for-like margin reading ("normalised": sigma - mu/2, so that its
conclusion implies the frozen one).  A competitor "wins" at a point if its threshold exceeds v2's by more than
0.005 orders.

Usage:  python3 -I scripts/apost_sharp/dominance.py [--quick] [--json OUT]
"""
from fractions import Fraction as F
import json, math, os, sys, time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import thresholds as v1          # noqa: E402
import thresholds_v2 as T2       # noqa: E402
import benchmark_hl19 as HL      # noqa: E402
import benchmark_fh24 as FH      # noqa: E402
import smalldiv as sd            # noqa: E402

lg = v1.lg


def grid_data(n, tau, gamma, rho, size, mu=F(1, 16)):
    s = F(size)
    return dict(n=n, tau=tau, kappa=tau, rho=F(rho), rhoinf=F(rho) / 1000, gamma=F(gamma), gbar=F(gamma), mu=mu,
                nu=F(1, 10 ** 6), M=s, sK=s, sB=s, sT=s,
                M0=s, M1=s, M2=s, Mh1=s, Mh2=s, sLt=2 * n * s, sN=s * s, sNt=2 * n * s * s,
                Tsup=4 * n * s ** 5 + 1, Theta_omega=2 * n * s * s * (s + 1), omega_star=None)


def v2_same_data(D):
    """v2 with the competitors' information only (levers that need no extra data)."""
    n, tau = D["n"], int(D["tau"])
    c_cl = lambda d: v1.up(sd.c_classical(n, tau, float(d)))
    lam = 3
    delta0 = min(F(1), (D["rho"] - D["rhoinf"]) / (2 * lam))

    def st(s):
        ds = delta0 / 2 ** s
        r = D["rho"] - 2 * lam * delta0 * (1 - F(1, 2 ** s))
        return c_cl(ds), c_cl(ds / 2), c_cl(min(r, F(1)))
    ct = c_cl(1)                                    # route A tail: absorbed constants, every bite <= 1
    ctB = c_cl(delta0 / 2 ** 5)                     # route B tail: constants valid for every bite <= delta_k (monotone)
    oA = dict(omega_eta=True, avg_full_bite=True, keep_delta=True, caps_tilde=True)
    lA, _, wA = T2.thresholdA(D, oA, False, k=5, c_stage=st, c_tail=ct)
    lB = -1e9
    for th in (F(1, 16), F(1, 8)):                  # the Neumann ratio is a free parameter of the design
        oB = dict(L1=False, keep_delta=True, avg_full_bite=True, aniso=True, theta=th)
        lB = max(lB, T2.thresholdB(D, oB, False, 5, st, ctB)[0])
    return max(lA, lB), ("A" if lA >= lB else "B"), lA, lB


def comp_data_hl(D):
    n = D["n"]; s = D["sK"]; mu = D["mu"]; sh = mu / 2
    return dict(n=n, tau=D["tau"], rho=D["rho"], rhoinf=D["rhoinf"], gamma=D["gamma"], cX0=D["M"], cX1=D["M"],
                cX2=D["M"], cXT1=D["M"], sK=D["sK"] - sh, sKT=2 * n * D["sK"] - sh, sB=D["sB"] - sh,
                sT=D["sT"] - sh, DK=D["sK"] - mu, DKT=2 * n * (D["sK"] - mu), Bact=D["sB"] - mu, Tinv=D["sT"] - mu,
                dist=mu - sh)


def comp_data_fh(D):
    n = D["n"]; mu = D["mu"]; sh = mu / 2
    sK, sB = D["sK"], D["sB"]
    return dict(n=n, tau=D["tau"], rho=D["rho"], rhoinf=D["rhoinf"], gamma=D["gamma"],
                c_Xh=D["M"], c_DXh=D["M"], c_DXhT=D["M"], c_D2Xh=D["M"], c_Th=2 * D["M"], c_DTh=2 * D["M"],
                s_DK=sK - sh, s_DKT=2 * n * sK - sh, s_B=sB - sh, s_N=sK * sB - sh, s_NT=2 * n * sK * sB - sh,
                s_Tinv=D["sT"] - sh, DK=sK - mu, DKT=2 * n * (sK - mu), B=sB - mu, N=(sK - mu) * (sB - mu),
                NT=2 * n * (sK - mu) * (sB - mu), Tinv=D["sT"] - mu, dist=mu - sh)


def compare(D):
    n, tau = D["n"], int(D["tau"])
    c = v1.up(sd.c_classical(n, tau, 1.0))
    lv2, route, lA, lB = v2_same_data(D)
    hl = HL.best_hl19(comp_data_hl(D), c, False)
    fh = FH.best_fh24(comp_data_fh(D), c, FH.cR1_fh24(c, tau))
    fhc = FH.best_fh24(comp_data_fh(D), c, FH.cR1_fh24(c, tau), errata=True)
    return dict(v2=lv2, route=route, A=lA, B=lB, HL19=lg(hl["threshold"]), FH24=lg(fh["threshold_e"]),
                FH24_corr=lg(fhc["threshold_e"]))


def main():
    quick = "--quick" in sys.argv
    pts = []
    ns = [(2, 1), (2, 2), (3, 2), (4, 3)] if not quick else [(2, 1), (3, 2)]
    gammas = [F(1, 1000), F(1, 100), F(1, 10)]
    rhos = [F(1, 1000), F(1, 100), F(1, 10)]
    sizes = [1, 3, 10] if not quick else [1, 10]
    t0 = time.time()
    print("| n | tau | gamma | rho | size | v2 (route) | HL19 | FH24 printed | FH24 corrected | margin |")
    print("|---|---|---|---|---|---:|---:|---:|---:|---:|")
    wins = []
    for (n, tau) in ns:
        for g in gammas:
            for r in rhos:
                for s in sizes:
                    D = grid_data(n, tau, g, r, s)
                    try:
                        res = compare(D)
                    except AssertionError as ex:            # e.g. a competitor's margin assertion
                        print("| %d | %d | %s | %s | %d | skipped (%s) |" % (n, tau, g, r, s, ex))
                        continue
                    best_comp = max(res["HL19"], res["FH24_corr"])
                    margin = res["v2"] - best_comp
                    row = dict(n=n, tau=tau, gamma=float(g), rho=float(r), size=s, **res, margin=margin)
                    pts.append(row)
                    flag = ""
                    if res["HL19"] > res["v2"] + 0.005 or res["FH24_corr"] > res["v2"] + 0.005:
                        wins.append(row); flag = " **competitor wins**"
                    print("| %d | %d | %g | %g | %d | %.2f (%s) | %.2f | %.2f | %.2f | %+.2f%s |" % (
                        n, tau, g, r, s, res["v2"], res["route"], res["HL19"], res["FH24"], res["FH24_corr"],
                        margin, flag))
                    sys.stdout.flush()
    print()
    print("points: %d, competitor wins (vs corrected FH24 or HL19): %d, printed-FH24 wins: %d, time %.0f s" % (
        len(pts), len(wins), sum(1 for p in pts if p["FH24"] > p["v2"] + 0.005), time.time() - t0))
    if pts:
        print("min margin v2 - best competitor: %.2f orders; median %.2f" % (
            min(p["margin"] for p in pts), sorted(p["margin"] for p in pts)[len(pts) // 2]))
    if len(sys.argv) > 2 and "--json" in sys.argv:
        json.dump(dict(points=pts, wins=wins), open(sys.argv[sys.argv.index("--json") + 1], "w"), indent=1)


if __name__ == "__main__" and "--plasmalean" not in sys.argv and "--fh25" not in sys.argv:
    main()


# ---------------------------------------------------------------------------------------------------------------
# PlasmaLean's example (owner directive 3).  PlasmaLean (github.com/siddhartha-gadgil/PlasmaLean, KamTorusAExact.lean,
# notes/theory/after-kam.md, as summarised in docs/explorations/striking-applications.md section 8 on branch apps-scout):
# field-line flow of a divergence-free field on T^2 (1 1/2 degrees of freedom), Newton in weighted l^1 coefficient norms,
# 2 unknown functions; proved tolerance delta0^4/(32 kappa) = 5.7e-19 at gamma = 0.0687, strip 0.1257 rad (rho = 0.02
# turns), delta0 = r/7.  Not like for like: our theorem is for canonical Hamiltonian flows (n = 2 with the clock
# frequency omega = (iota, 1)), sup norms on a 2n-dimensional phase space; the exact field of PlasmaLean has a
# non-canonical area form and no closed-form canonical chart.  What is compared: our threshold on e (sup norm of the
# invariance error) at PlasmaLean's gamma, strip and frame/torsion bounds (two norm guesses of run_mag.py), against its
# proved tolerance on its own error norm.
# ---------------------------------------------------------------------------------------------------------------

PLASMALEAN = dict(log10_tolerance=math.log10(5.7e-19), gamma=0.0687, rho_rad=0.1257, iota=(75 + math.sqrt(5)) / 562)


def plasmalean_data(tag):
    sK, sB, M, T = {"cA-like": (3.1, 2.0, 3.0, 19.84), "R1-like": (1.37, 1.93, 1.9, 3.3)}[tag]
    mu = F(1, 160)
    sK, sB, M = F(str(sK)), F(str(sB)), F(str(M))
    D = grid_data(2, 1, F(687, 10000), v1.up(0.1257 / (2 * math.pi)), 1)
    D.update(M=M, M0=M, M1=M, M2=M, Mh1=M, Mh2=M, sK=sK, sB=sB, sT=1 / F(22, 100) + mu, mu=mu,
             sLt=2 * 2 * sK, sN=sK * sB, sNt=2 * 2 * sK * sB, Tsup=F(str(T)), cTh=2 * M,
             omega_star=(PLASMALEAN["iota"], 1.0))
    for k_, base in (("B", D["sB"]), ("Tinv", D["sT"]), ("Lt", D["sLt"]), ("N", D["sN"]), ("Nt", D["sNt"]),
                     ("Tsup", D["Tsup"])):
        D["bud_" + k_] = base / 10
    # floating point (as for FH25): exact rationals make the 5-stage bisection very slow here
    return {k: (float(v) if isinstance(v, F) else v) for k, v in D.items()}


def plasmalean():
    print("PlasmaLean's example: its proved tolerance 10^%.2f (l^1 norms, its own theorem)." % PLASMALEAN["log10_tolerance"])
    print("| norms | small divisors | v2 route A | v2 route B | best | vs PlasmaLean |")
    print("|---|---|---:|---:|---:|---:|")
    rows = []
    for tag in ("cA-like", "R1-like"):
        D = plasmalean_data(tag)
        lam = 3
        delta0 = (D["rho"] - D["rhoinf"]) / (2 * lam)
        om = D["omega_star"]; gam = float(D["gamma"])
        for which in ("classical", "freq", "l1-freq (L9)"):
            if which == "classical":
                st, ct = T2.c_stages(D, "classical")
                pen = 0.0
            elif which == "freq":                       # flat in delta (as measured for R1/H50): the value at delta0
                cf = sd.c_freq(om, gam, 1, float(delta0))[0]
                cr_ = sd.c_freq(om, gam, 1, float(D["rho"]))[0]
                st = lambda s, cf=cf, cr_=cr_: (cf, cf, cr_)
                ct = float(T2.Fr(sd.c_classical(2, 1, float(delta0) / 32)))
                pen = 0.0
            else:                                       # L9: SHARP-L9's certified c_inf = Gamma_inf gamma delta^tau, flat
                cinf = 0.00123                          # (docs/campaign/handoffs/SHARP-L9.md, PlasmaLean's frequency)
                st = lambda s, cinf=cinf: (cinf, cinf, cinf)
                ct = sd.c_inf_classical(1)
                pen = math.log10(3.6)                  # l^1/sup of E (CERTIFIER-SHARPNESS 1.2, worst R1 value)
            oA = dict(L1=True, torsion_cap=D["Tsup"], torsion_real=D["Tsup"], omega_eta=True, avg_full_bite=True,
                      keep_delta=True, caps_tilde=True, free_budgets=True)
            Dv = T2.with_caps(D, F(1, 20))
            oA["torsion_cap"] = Dv["Tsup_cap"]; oA["torsion_real"] = Dv["Tsup_cap"]
            lA = T2.thresholdA(Dv, oA, False, k=5, c_stage=st, c_tail=ct)[0] - pen
            lB = -1e9
            for th in (F(1, 16), F(1, 8)):
                oB = dict(L1=True, keep_delta=True, avg_full_bite=True, aniso=True, theta=th, cTh=Dv["cTh"],
                          free_budgets=True)
                lB = max(lB, T2.thresholdB(Dv, oB, False, 5, st, ct)[0] - pen)
            best = max(lA, lB)
            rows.append(dict(norms=tag, small_divisors=which, A=lA, B=lB, best=best,
                             margin=best - PLASMALEAN["log10_tolerance"]))
            print("| %s | %s | %.2f | %.2f | %.2f | %+.2f |" % (tag, which, lA, lB, best,
                                                               best - PLASMALEAN["log10_tolerance"]))
            sys.stdout.flush()
    return rows


if __name__ == "__main__" and "--plasmalean" in sys.argv:
    plasmalean()


# ---------------------------------------------------------------------------------------------------------------
# Figueras-Haro 2025 (J. Nonlinear Sci. 35 (2025) 13, arXiv:2403.10152, section 5): planar Sun-Jupiter-Saturn, a 3-torus,
# FH24 with one first integral (d = 3), tau = 2.4, gamma = 1.69e-6, rho = 0.1, delta = rho/6; c_Xh = 0.09, c_DXh = c_(DXh)^T
# = 129, c_D2Xh = 5e10; ||DK|| = 4.7812, ||DK^T|| = 6.8756, ||B|| = 7.3581, ||N|| = 3.5704, ||N^T|| = 2.8621,
# |<T>^-1| = 354.08; sigma = norm (1 + 1e-10).  Their check: the Iterative Lemma iterated numerically for 10 steps, then
# the KAM theorem, closes for ||eta^DK|| = 1e-38, ||eta^N|| = 1e-44 (numerically checked, not interval arithmetic).
# Mapping: v2 is a d = n canonical theorem; we use their norms as the caps of a d = n = 3 problem (the first integral and
# the moment flow are dropped: c_Xp = 0), the same uniform small-divisor constant structure (classical, our c^natural),
# c_Th = 2 c_DXh, c_DTh = 2 c_D2Xh, margins 1e-10 x norm for the internal caps and the frame, and a prefix of 10 exact
# stages (their 10 numerical steps).  Compared: whether (1e-38, 1e-44) is admissible, and the margin in orders.
# ---------------------------------------------------------------------------------------------------------------

FH25 = dict(etaL=1e-38, etaN=1e-44)


def fh25_data(mu_rel=1e-10):
    n = 3
    norms = dict(sK=4.7811815833, sLt=6.8755882886, sB=7.35806411265, sN=3.5704498717, sNt=2.8621242724, sT=354.07743243)
    D = dict(n=n, tau=2.4, kappa=2.4, rho=0.1, rhoinf=0.1 / 1000, gamma=1.69e-6, gbar=1.69e-6,
             M=5e10, M0=0.09, M1=129.0, M2=5e10, Mh1=129.0, Mh2=5e10, cTh=2 * 129.0, Tsup=None,
             Theta_omega=None, omega_star=None, nu=1e-6)
    for k_, v in norms.items():
        D[k_] = v * (1 + mu_rel)
    D["mu"] = 2 * mu_rel * norms["sK"]                     # so that the |DK| budget mu/2 equals their margin
    for k_, nm in (("B", "sB"), ("Tinv", "sT"), ("Lt", "sLt"), ("N", "sN"), ("Nt", "sNt")):
        D["bud_" + k_] = norms[nm] * mu_rel
    return D


def fh25(kpre=10):
    D = fh25_data()
    n, tau = D["n"], D["tau"]
    lam = 3
    delta0 = (D["rho"] - D["rhoinf"]) / (2 * lam)
    ccl = lambda d: sd.c_classical(n, tau, float(d))

    def st(s):
        ds = delta0 / 2 ** s
        r = D["rho"] - 2 * lam * delta0 * (1 - 0.5 ** s)
        return ccl(ds), ccl(ds / 2), ccl(min(r, 1.0))
    ct = ccl(delta0 / 2 ** kpre)
    gd0 = D["gamma"] * delta0 ** tau
    mu0 = max(FH25["etaL"], FH25["etaN"] / gd0)             # their errors, isotropic weight
    X0 = mu0 / (D["gamma"] * delta0 ** (tau + 1))
    out = {}
    stg = lambda ds, r: (ccl(ds), ccl(ds / 2), ccl(min(r, 1.0)))
    for aniso, ratio, cDTh in ((False, 2, None), (True, 2, None), (True, 3, None), (True, 4, None), (True, 3, 2 * 129.0)):
        o = dict(L1=True, keep_delta=True, avg_full_bite=True, theta=F(1, 16), cTh=D["cTh"], free_budgets=True,
                 aniso=aniso, eta_measured=(FH25["etaL"], FH25["etaN"]), no_e=True, ratio=ratio)
        if cDTh:
            o["cDTh"] = cDTh
        st_use = st if ratio == 2 else stg
        le, _, why = T2.thresholdB(D, o, False, kpre, st_use, ct)
        tag = "%s, ratio %s%s" % ("anisotropic" if aniso else "FH24 weight", ratio,
                                   ", c_DTh = 2 c_DXh (hypothetical)" if cDTh else ", c_DTh = 2 c_D2Xh")
        out[tag] = dict(log10_scale=le, binding=why)
        print("FH25 data, v2 route B (k = %d, classical c, %s): admissible scale of (1e-38, 1e-44) = 10^%.2f; binding %s"
              % (kpre, tag, le, ", ".join(why)))
    return out
    for aniso in ():
        o = dict(L1=True, keep_delta=True, avg_full_bite=True, theta=F(1, 16), cTh=D["cTh"], free_budgets=True,
                 aniso=aniso, eta_measured=(FH25["etaL"], FH25["etaN"]), no_e=True)
        # admissible X at stage 0 (bisection inside thresholdB returns log10 e for mu_0 = per_e e; recover log10 X*)
        le, _, why = T2.thresholdB(D, o, False, kpre, st, ct)
        per_e = max(FH25["etaL"], FH25["etaN"] / gd0) / 1.0
        # thresholdB uses per_e = max{etaL, etaN/(gamma delta0^kappa)} with the measured eta's per unit e; e* is the
        # scale factor on (etaL, etaN): admissible iff e* >= 1
        out["aniso" if aniso else "iso-weight"] = dict(log10_scale=le, binding=why)
        print("FH25 data, v2 route B (k = %d, classical c, %s): admissible scale of (1e-38, 1e-44) = 10^%.2f; binding %s"
              % (kpre, "anisotropic stage-0 weight" if aniso else "FH24 weight", le, ", ".join(why)))
    return out


if __name__ == "__main__" and "--fh25" in sys.argv:
    fh25()
