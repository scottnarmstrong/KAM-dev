#!/usr/bin/env python3
"""SJS-X1: the plan's cost model (sjs_plan_cost.py) re-run with the measured support S(L) instead of its extrapolation.

Untrusted design tooling; every number is a model with named inputs.
  S(L)      measured here (x1_spectrum.py JSON, 'reg' components, strip 0.02, the set of SJS-PLAN's table 1.3), L <= Lfit;
            extrapolated to the certificate's L by S^(1/3) = S(Lfit)^(1/3) + a (L - Lfit), with a between the mean slope over
            the last 8 measured digits (low) and the largest single-digit increment measured (high); a third, conservative
            scenario ('rise') lets the slope resume the rise it had between L = 10 and 20 (d a / d L from the mean increments of
            L = 9..11 and 18..20), although it measured flat from L = 19 to 24;
  beta      box / S of the best frame, measured (robust frame search, 99.5 % per axis);
  L, bits   the plan's: L = 45 (T_raw = 10^-38.0 plus 7 of headroom), bits = 3.33 L + 24;
  packed    sjs_plan_cost.packed (E1/E2 laws) for the arithmetic;
  literals  V2-PACKED (landed on main 1 Nov) measured the input side: 36-47 bytes of charged kernel memory per literal bit with
            288-bit chunks (one 4 GB declaration ingests 75-100 Mbit), about 6 bytes per bit with long-line chunks (owner
            question Q1 of the V2-PACKED handoff), and 0.9-1.3 us of elaboration per literal bit; input = the six components of K
            on the box at p = bits(L) per slot (the product-ready width w = 2p + log2 S + 2 is needed only for products, which
            stay GMP-resident and are never literals).
Usage: x1_cost.py SPEC.json [--Lfit 24] [--json OUT]
"""
import argparse, json, math, os, sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "plan"))
import sjs_plan_cost as PC
sys.path.pop(0)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("spec")
    ap.add_argument("--Lfit", type=int, default=24)
    ap.add_argument("--L", type=float, default=45.0)
    ap.add_argument("--beta", type=float)
    ap.add_argument("--json")
    a = ap.parse_args()
    r = json.load(open(a.spec))
    Ls = r["Ls"]
    S = dict(zip(Ls, r["reg"]["S"]["0.02"]))
    cube = {L: S[L] ** (1 / 3) for L in Ls if S[L] > 0}
    inc = {L: cube[L] - cube[L - 1] for L in Ls if L - 1 in cube and L in cube}
    Lf = a.Lfit
    slope_lo = (cube[Lf] - cube[Lf - 8]) / 8
    slope_hi = max(inc[L] for L in inc if Lf - 8 < L <= Lf)
    L = a.L
    S_lo = (cube[Lf] + slope_lo * (L - Lf)) ** 3
    S_hi = (cube[Lf] + slope_hi * (L - Lf)) ** 3
    rise = (sum(inc[x] for x in (18, 19, 20)) / 3 - sum(inc[x] for x in (9, 10, 11)) / 3) / 9
    S_rise = (cube[Lf] + slope_hi * (L - Lf) + 0.5 * rise * (L - Lf) ** 2) ** 3
    beta = a.beta
    if beta is None:
        fr = r.get("frames", {})
        beta = min(v["best"][0][0] for v in fr.values()) if fr else 3.0
    out = dict(Lfit=Lf, S_fit=S[Lf], slope_lo=slope_lo, slope_hi=slope_hi, rise_per_digit=rise, S_rise=S_rise, increments={str(k): v for k, v in inc.items()},
               L=L, S_lo=S_lo, S_hi=S_hi, beta=beta, plan=dict(S_lo=PC.S_full(L, "syn", False), S_hi=PC.S_full(L, "syn", True)))
    print("measured S(L), reg components, strip 0.02:", {k: S[k] for k in Ls if k % 2 == 0})
    print("S^(1/3) increments per digit:", " ".join("%d:%.2f" % (k, v) for k, v in sorted(inc.items())))
    print("extrapolation from L = %d: slope %.2f .. %.2f per digit -> S(%.0f) = %.2e .. %.2e; slope rising %.3f per digit -> %.2e "
          "(plan: %.2e .. %.2e)" % (Lf, slope_lo, slope_hi, L, S_lo, S_hi, rise, S_rise, out["plan"]["S_lo"], out["plan"]["S_hi"]))
    rows = []
    for tag, Sx in (("lo", S_lo), ("hi", S_hi), ("rise", S_rise)):
        rec = dict(S=Sx)
        for Nname, Nf, Nadd in (("rev", 252, 660), ("fwd", 657, 500)):
            for mode in ("one", "gb", "default"):
                rec["packed_%s_%s" % (Nname, mode)] = [PC.packed(Sx, beta, L, Nf, Nadd, k, mode) for k in PC.KAPPA]
        p = rec["packed_rev_one"][0]
        lit_bits = 6 * p["box"] * PC.bits(L)
        rec["literal_bits"] = lit_bits
        rec["literal_GB_288bit"] = [lit_bits * b / 1e9 for b in (36, 47)]
        rec["literal_GB_longline"] = lit_bits * 6 / 1e9
        rec["literal_elab_cpu_h"] = [lit_bits * t / 3600 for t in (0.9e-6, 1.3e-6)]
        rows.append((tag, rec))
        out[tag] = rec
        print("  %s: S %.2e, box %.2e, w %.0f bits, F %.2f GB | packed one Nat: %.0f-%.0f CPU-h | 8 GB shards: %.0f-%.0f CPU-h | "
              "default limit: %.0f-%.0f CPU-h | input literals %.2e bits: %.0f-%.0f GB charged at 288-bit chunks, %.0f GB long-line, "
              "%.1f-%.1f CPU-h of elaboration" % (
                  tag, Sx, p["box"], p["w"], p["F_GB"], rec["packed_rev_one"][0]["cpu_h"], rec["packed_fwd_one"][1]["cpu_h"],
                  rec["packed_rev_gb"][0]["cpu_h"], rec["packed_fwd_gb"][1]["cpu_h"], rec["packed_rev_default"][0]["cpu_h"],
                  rec["packed_fwd_default"][1]["cpu_h"], lit_bits, rec["literal_GB_288bit"][0], rec["literal_GB_288bit"][1],
                  rec["literal_GB_longline"], rec["literal_elab_cpu_h"][0], rec["literal_elab_cpu_h"][1]))
    if a.json:
        json.dump(out, open(a.json, "w"), indent=1, default=float)


if __name__ == "__main__":
    main()
