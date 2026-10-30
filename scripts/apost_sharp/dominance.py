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
    ct = c_cl(1)
    oA = dict(omega_eta=True, avg_full_bite=True, keep_delta=True, caps_tilde=True)
    lA, _, wA = T2.thresholdA(D, oA, False, k=5, c_stage=st, c_tail=ct)
    oB = dict(L1=False, keep_delta=True, avg_full_bite=True, aniso=True)
    lB, _, wB = T2.thresholdB(D, oB, False, 5, st, ct)
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


if __name__ == "__main__":
    main()
