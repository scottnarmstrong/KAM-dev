#!/usr/bin/env python3
"""SJS-PLAN items 2-4: kernel and numerical cost of one planar SJS torus, calibrated on the lunar receipts and E1/E2.

Untrusted design tooling; every number is a model with named inputs.
Inputs (receipts):
  thresholds     results/thresholds_*.json (sjs_plan_thresholds.py), T in the certificate's chart;
  L              -log10 T_raw + HEAD, T_raw = T 2 pi / c: the residual in FH's units; a truncation at L digits leaves
                 E_ang = amp(L) 10^-L in FH's units, with amp = 226, 561, 1180, 2220 at L = 5..8 (sjs_hybrid.py), the sum over
                 the dropped shell, amp ~ L^3 .. L^4.5 beyond: amp(45) = 4e5 .. 5e6; HEAD = 5.6 .. 6.7 + 0.7 of headroom = 7;
  S_full(L)      full-lattice support at strip 0.02: S^(1/3) = slope (L - L0), measured on L = 6..10 (spectrum128.json);
                 slope range: last measured increment (rising) .. the cross-polytope value of the measured per-axis rates;
  beta           box / S in the best unimodular frame (robust_frames, 99.5 % per axis), range;
  N_full         252 (reverse mode) / 657 (forward jets) real model products, sjs_ops.py;
  add/scal       502 / 85+417, sjs_ops.py;
  today's checker  SO-CSPLIT gates: 484 x 498 product shards 42 s (7 x 1312 slots: 4.6 ms per advice slot), decode 3 ms per
                 target slot, 23 calls per term per live op (census: 2.40 M calls / (215 slots x 488 terms)), 0.15 ms per call
                 (0.3-0.6 calibrated, gates 2-4 x below), nu = 13.5 beta advice slots per factor term in 3-D (SJS-FEAS);
  packed         E1/E2 (results/packed_probes.jsonl): 8 ns per operand bit for one Nat.mul (7.6-9 at load 20+), peak
                 0.45 GB + 10 F for one mul, cycle = mul + round + range + abs + norm = kappa x mul, kappa 2-3, peak 0.45 GB + 16 F when
                 the cycle is split in 2-3 declarations; operand F bits = 2.25 w box (Kronecker with 1.5 padding on two axes);
                 default kernel limit 2^30 bits per Nat, so F <= 2^29 (LEAN_NAT_MAX_SIZE, bytes).
Usage: python3 -I scripts/sjs/plan/sjs_plan_cost.py [--json OUT]
"""
import json, math, os, sys

HEAD = 7.0
C_SLOT, C_DEC, CALLS, C_CALL = 4.6e-3, 3e-3, 23, 0.15e-3
NU3 = 13.5
T_MUL = 8e-9
KAPPA = (2.0, 3.0)
LIMIT_BITS = 2 ** 29
THEOREM_S = 5.0                   # import + write per theorem (lunar: 4-10 s, estimate)


def bits(L):
    return 3.33 * L + 24


def S_full(L, chart, hi):
    if chart == "syn":
        a = 5.3 if hi else 3.7
        return (a * (L - 1.06)) ** 3
    a = 6.1 if hi else 5.6
    return (a * (L - 1.96)) ** 3


def strip_factor(rho, chart):
    r = (0.618, 0.511, 0.353) if chart == "syn" else (0.618, 0.504, 0.391)
    return float(math.prod((x - 0.02) / (x - rho) for x in r))


def today(S, beta, Nfull, Nops):
    """the landed checker (post D34, CSPLIT), per torus"""
    nu = NU3 * beta
    slots = nu * S
    box = beta * S
    prod = slots * C_SLOT + box * C_DEC
    ops = CALLS * C_CALL * S
    t = Nfull * prod + Nops * ops
    theorems = Nfull * (slots / (7 * 1312) + 1)
    return dict(cpu_h=(t + theorems * THEOREM_S) / 3600, theorems=theorems, advice_TB=Nfull * slots * 25 / 1e12)


def packed(S, beta, L, Nfull, Nadd, kappa, mode, limit_gb=8.0):
    """mode 'one': one Nat per model; 'gb': blocks with peak <= limit_gb; 'default': blocks under the kernel's 2^30 limit."""
    p = bits(L)
    w = 2 * p + math.log2(S) + 2
    box = beta * S
    F = 2.25 * w * box
    FB = F / 8e9
    if mode == "one":
        nb, Fb = 1, F
    elif mode == "default":
        nb = max(1, math.ceil(F / LIMIT_BITS))
        Fb = F / nb
    else:
        Fmax = (limit_gb - 0.45) / 16 * 8e9
        nb = max(1, math.ceil(F / Fmax))
        Fb = F / nb
    subs = max(1.0, 0.75 * nb * nb)           # output truncated to the central box
    t_prod = subs * kappa * T_MUL * Fb
    t = Nfull * t_prod + Nadd * nb * 0.3e-9 * Fb * 2
    decl = Nfull * subs / (6 if nb > 1 else 1)     # up to 6 sub-products per declaration, to bound the kernel caches
    peak = 0.45 + 16 * Fb / 8e9
    led = (Nfull + 25) * box * p / 8e9
    return dict(F_GB=FB, nb=nb, Fb_MB=Fb / 8e6, cpu_h=(t + decl * THEOREM_S) / 3600, t_prod_min=t_prod / 60, peak_GB=peak, decl=decl,
                ledger_GB=led, w=w, box=box)


def numerics(S, beta, L):
    """FH-style multiprecision FFT Newton, scaled from FH25: 1 step = 1 week on 8 cores at 1024^3, 76 digits, 194 GB (one complex grid)"""
    box = beta * S
    N = box * 3.375                            # 1.5 per axis
    t = 1344.0 * (N / 1.07e9) * (math.log(N) / math.log(1.07e9)) * (L / 76.0) ** 1.6
    mem = 194.0 * (N / 1.07e9) * (max(L, 40) / 76.0)
    return dict(grid=N, cpu_h_step=t, ram_GB=mem, ram_rev_GB=mem / 2)


def lunar_check():
    """the constants of `today` on the real L = 20 lunar torus (SO-CSPLIT census): 667 shards of 1312 slots, 351 k target slots,
    10.7 M calls, about 470 theorems.  The gates measured 1.6-2.5 CPU-h."""
    t = 667 * 1312 * C_SLOT + 351e3 * C_DEC + 10.7e6 * C_CALL + 470 * THEOREM_S
    return t / 3600


def hardware(rec, tag):
    """wall clock of the kernel check: CPU-h / concurrency, concurrency = min(cores, RAM / peak, DAG width for unblocked products)"""
    r = rec[tag]
    rows = []
    for name, cores, ram, usd_h, mode in (("lemma.farm, default limit", 8, 32, 0, "default"), ("lemma.farm, 8 GB shards", 8, 32, 0, "gb"),
                                          ("48 cores, 256 GB, one Nat per model", 48, 240, 0.33, "one"),
                                          ("48 cores, 256 GB, 8 GB shards", 48, 240, 0.33, "gb"),
                                          ("48 cores, 768 GB, one Nat per model", 48, 740, 6.35, "one"),
                                          ("48 cores, 768 GB, 8 GB shards", 48, 740, 6.35, "gb")):
        lo, hi = r["packed_rev_" + mode][0], r["packed_fwd_" + mode][1]
        conc = max(1, min(cores, int(ram / lo["peak_GB"])))
        if mode == "one":
            conc = min(conc, 6)                # the program's DAG: about 252 products in 40 levels
        rows.append((name, mode, lo["peak_GB"], conc, lo["cpu_h"] / conc, hi["cpu_h"] / conc, usd_h * lo["cpu_h"] / conc, usd_h * hi["cpu_h"] / conc))
    return rows


def fmt(x):
    if x >= 1e4:
        return "%.1e" % x
    return "%.0f" % x if x >= 10 else "%.1f" % x


def main():
    here = os.path.dirname(os.path.abspath(__file__))
    scen = json.load(open(os.path.join(here, "results", "scenarios.json")))
    out = []
    print("| scenario | T_raw | L | bits | S_full | box | F GB | peak one Nat GB |")
    print("|---|---:|---:|---:|---:|---:|---:|---:|")
    for sc in scen:
        chart, T_raw, rho, beta = sc["chart"], sc["logT_raw"], sc["rho"], sc["beta"]
        L = -T_raw + HEAD
        rec = dict(sc, L=L, bits=bits(L))
        for hi in (False, True):
            S = S_full(L, chart, hi) * strip_factor(rho, chart)
            tag = "hi" if hi else "lo"
            res = dict(S=S)
            for Nname, Nf, Nadd, Nops in (("rev", 252, 660, 800), ("fwd", 657, 500, 500)):
                res["today_" + Nname] = today(S, beta, Nf, Nops)
                for mode in ("one", "gb", "default"):
                    res["packed_%s_%s" % (Nname, mode)] = [packed(S, beta, L, Nf, Nadd, k, mode) for k in KAPPA]
            res["numerics"] = numerics(S, beta, L)
            rec[tag] = res
        out.append(rec)
        for tag in ("lo", "hi"):
            r = rec[tag]; p = r["packed_rev_one"][0]
            print("| %s (%s) | %.1f | %.0f | %.0f | %s | %s | %.2f | %.0f |" % (
                sc["name"], tag, T_raw, L, bits(L), fmt(r["S"]), fmt(p["box"]), p["F_GB"], 0.45 + 10 * p["F_GB"]))
    print("\n| scenario | S | today's checker CPU-h (rev/fwd) | theorems | advice TB | packed, one Nat per model: CPU-h, peak | packed, 8 GB shards (needs LEAN_NAT_MAX_SIZE): CPU-h, blocks | packed, default limit: CPU-h, blocks, peak |")
    print("|---|---|---:|---:|---:|---:|---:|---:|")
    for rec in out:
        for tag in ("lo", "hi"):
            r = rec[tag]
            a, b = r["packed_rev_one"], r["packed_fwd_one"]
            g, g2 = r["packed_rev_gb"], r["packed_fwd_gb"]
            d, d2 = r["packed_rev_default"], r["packed_fwd_default"]
            print("| %s | %s | %s / %s | %s | %.1f | %s-%s, %.0f GB | %s-%s, nb %d | %s-%s, nb %d, %.1f GB |" % (
                rec["name"], tag, fmt(r["today_rev"]["cpu_h"]), fmt(r["today_fwd"]["cpu_h"]), fmt(r["today_rev"]["theorems"]),
                r["today_rev"]["advice_TB"], fmt(a[0]["cpu_h"]), fmt(b[1]["cpu_h"]), a[0]["peak_GB"], fmt(g[0]["cpu_h"]), fmt(g2[1]["cpu_h"]), g[0]["nb"],
                fmt(d[0]["cpu_h"]), fmt(d2[1]["cpu_h"]), d[0]["nb"], d[0]["peak_GB"]))
    print("\n| scenario | S | FFT grid (points) | FH-style mpfr Newton step, CPU-h | RAM GB (reversible half) | packed Newton step (native GMP), CPU-h | ledger GB |")
    print("|---|---|---:|---:|---:|---:|---:|")
    for rec in out:
        for tag in ("lo", "hi"):
            r = rec[tag]; n = r["numerics"]
            pn = 1.3 * r["packed_rev_one"][0]["cpu_h"]
            print("| %s | %s | %s | %s | %.0f | %s | %.0f-%.0f |" % (rec["name"], tag, fmt(n["grid"]), fmt(n["cpu_h_step"]), n["ram_rev_GB"], fmt(pn),
                                                                  r["packed_rev_one"][0]["ledger_GB"], r["packed_fwd_one"][0]["ledger_GB"]))
    print("\nCalibration: the constants of 'today' price the real lunar torus (L = 20, N = 65) at %.1f CPU-h; the gates measured 1.6-2.5." % lunar_check())
    print("\n| plan scenario | hardware | mode | peak GB | concurrent | wall h (reverse, kappa 2 .. forward, kappa 3) | USD on-demand |")
    print("|---|---|---|---:|---:|---:|---:|")
    plan = [r for r in out if r.get("plan")]
    for rec in plan:
        for tag in ("lo", "hi"):
            for h in hardware(rec, tag):
                print("| %s %s | %s | %s | %.1f | %d | %s .. %s | %s .. %s |" % (rec["name"], tag, h[0], h[1], h[2], h[3], fmt(h[4]), fmt(h[5]), fmt(h[6]), fmt(h[7])))
    print("\nHybrid (SHARP2-HYBRID), plan scenario; A = 2-5 in FH's units (sjs_hybrid.py):")
    for rec in plan:
        for A in (2.0, 5.0):
            e = 0.5 * (rec["logT_raw"] - math.log10(A))
            Lc = -e + 5.0 + 0.7                 # amp(20) = 3e4 .. 1.4e5
            print("  candidate residual 10^%.1f, L_cand %.0f, %.0f bits, S_cand %s .. %s (the composition stays at L = %.0f, S as in the table)" % (
                e, Lc, bits(Lc), fmt(S_full(Lc, "syn", False)), fmt(S_full(Lc, "syn", True)), rec["L"]))
    if "--json" in sys.argv:
        json.dump(out, open(sys.argv[sys.argv.index("--json") + 1], "w"), indent=1, default=float)


if __name__ == "__main__":
    main()
