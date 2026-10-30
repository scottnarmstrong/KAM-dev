#!/usr/bin/env python3
"""SJS-FEAS item 5: kernel compute for one SJS torus certificate, from the measured kernel constants.

Untrusted design tooling; every number is a model.  Inputs:
- support: `sjs_support.py` (cross-polytope "product model" from FH25's per-angle decay, strip-optimized), divided by
  the d'Alembert factor of `sjs_model_support.py` (true support / product model, 1/7 .. 1/14) and by 2 for the
  reversible half lattice;
- thresholds: `sjs_thresholds.py` (log10 at FH's strip rho = 0.1; route B = SHARP-PLUS's mirror) and the hybrid
  estimate (L6, measured step 0: log10 T halved, by analogy with R1, 10^-12 -> 10^-4.5);
- kernel constants: `results/kernel_probes.md` (single runs, +-30 %):
    per-slot route (D34-like prototype): 1.0 ms and 82 kB per advice slot, 1.4 ms and 260 kB per factor term packed,
      advice slots per factor term nu = 13.5 beta in 3-D (beta = layout box / support; 13.5 measured for a box);
    model op (scalar route, add): 1.26 ms and 220 kB per term;
    GMP-resident redesign (hypothetical: models kept packed, O(1) big-integer ops per model op): 3.4e-8 s per factor
      bit per product (measured 6.6 ns/bit mul, x 5.1 for the product's size and the checks, the probe's estimate),
      factor bits = 3.375 w beta S in 3-D, peak memory 4-8 x factor bytes; an add/mask op 0.04-0.17 ns per bit;
    process baseline 3.1 GB (Mathlib import); a 32 GB slice leaves 29 GB to the kernel;
    data elaboration 0.18 ms (packed Int literals) .. 0.6 ms (key, coefficient lists) per element;
- operation counts per torus (ranges; the jet mirror `jet_counts.py` gives the lunar and planetary-toy shapes, the SJS
  counts are hand estimates for a reduced Cartesian-type chart with inv/sqrt witnesses): full-precision model x model
  products N_full, scalar/add model ops N_ops on the full support, and the Gram/torsion stage (N_low products,
  N_low_ops ops) on the support at L_low = 17 digits (lunar cfgLow).
- the applications study's projection (`scripts/apps_scout/costmodel.py`, tier P) for the baseline.

Usage: python3 -I scripts/sjs/sjs_cost.py [--json OUT]
"""
import os, sys, json, math

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from sjs_support import best_rho, support                      # noqa: E402
sys.path.pop(0)

# ---- measured kernel constants (results/kernel_probes.md)
C_SLOT, M_SLOT = 1.0e-3, 82e3          # s, bytes per advice slot (packing 0.6-0.95 + decode 0.2-0.34 ms)
C_TERM, M_TERM = 1.4e-3, 260e3         # per factor term packed
NU_BOX3 = 13.5                         # advice slots per factor term, 3-D box layout
C_OP, M_OP = 1.26e-3, 220e3            # per term per model op
GMP_S_PER_BIT = 3.4e-8                 # per factor bit per product (734 s at 2.16e10 bits)
GMP_FBITS = 3.375                      # factor bits per (w * box slot) in 3-D
GMP_MEM = (4, 8)                       # peak memory / factor bytes
GMP_OP_S_PER_BIT = (0.04e-9, 0.17e-9)  # add / land / shift: 4-17 ms per 1e8 bits
KERNEL_GB = 29.0                       # 32 GB slice - 3.1 GB baseline
ELAB = (0.18e-3, 0.6e-3)               # s per data element
CORES_HERE = 16
L_LOW = 17.0


def bits(L):
    return 3.33 * L + 24


def slot_width(L):
    return 2 * bits(L) + 40


def true_support(logT01, dalembert, p=5.8):
    rho, S_pm, L, A, box, lt = best_rho(logT01, p)
    return dict(rho=rho, L=L, S_pm=S_pm, S=S_pm / dalembert / 2, logT=lt)


def low_support(rho, dalembert):
    S_pm, _, _ = support(L_LOW, rho)
    return S_pm / dalembert / 2


def per_slot(S, L, S_low, ops, beta):
    """D34-like per-slot route; returns CPU-h and advice slots and data elements."""
    nu = NU_BOX3 * beta
    prod = lambda s: s * (2 * C_TERM + nu * C_SLOT)
    t = ops["N_full"] * prod(S) + ops["N_ops"] * S * C_OP + ops["N_low"] * prod(S_low) + ops["N_low_ops"] * S_low * C_OP
    slots = nu * (ops["N_full"] * S + ops["N_low"] * S_low)
    op_terms = ops["N_ops"] * S + ops["N_low_ops"] * S_low       # intermediates supplied as data (memory forces it)
    per_decl_slots = KERNEL_GB * 1e9 / M_SLOT                    # factors pre-packed as certificate data
    per_decl_opterms = KERNEL_GB * 1e9 / M_OP
    decls = slots / per_decl_slots + op_terms / per_decl_opterms
    data_bits = slots * slot_width(L) * 0.5 + op_terms * bits(L)  # advice ~ half a slot of significant bits
    return dict(cpu_h=t / 3600, decls=decls, shard_s=per_decl_slots * C_SLOT, data_GB=data_bits / 8e9,
                elab_cpu_h=tuple((slots + op_terms) * e / 3600 for e in ELAB))


def gmp(S, L, S_low, ops, beta):
    """hypothetical GMP-resident packed algebra: O(1) big-integer ops per model op, dense Kronecker layout (beta =
    box/support of the best unimodular frame).  A product whose peak exceeds the slice is blocked: both factors split
    into nb blocks, nb^2 sub-products of 1/nb^2 the bits each (time x nb, peak / nb)."""
    fb = lambda s, l: GMP_FBITS * slot_width(l) * beta * s
    peak = [m * fb(S, L) / 8e9 for m in GMP_MEM]
    nb = [max(1, math.ceil(pk / KERNEL_GB)) for pk in peak]
    t = [(ops["N_full"] * fb(S, L) * n + ops["N_low"] * fb(S_low, L_LOW)) * GMP_S_PER_BIT for n in nb]
    t_ops = [(ops["N_ops"] * fb(S, L) + ops["N_low_ops"] * fb(S_low, L_LOW)) * c for c in GMP_OP_S_PER_BIT]
    data_bits = 30 * S * bits(L)                                  # K (6 components) + ~24 witness series
    return dict(cpu_h=(t[0] + t_ops[0]) / 3600, cpu_h_hi=(t[1] + t_ops[1]) / 3600, prod_s=fb(S, L) * GMP_S_PER_BIT,
                peak_GB=peak, blocks=nb, factor_bits=fb(S, L), data_GB=data_bits / 8e9)


def apps_projection(S, L, Nfull, box_factor):
    sys.path.insert(0, os.path.join(HERE, "..", "apps_scout"))
    import costmodel                                              # noqa: E402  (read-only use)
    sys.path.pop(0)
    return costmodel.project(S, L, Nfull, box_factor=box_factor)


OPS = dict(lo=dict(N_full=60, N_ops=500, N_low=300, N_low_ops=1000),
           hi=dict(N_full=150, N_ops=2000, N_low=600, N_low_ops=3000))
BETA_BOX, BETA_IDEAL = 10.0, 1.0       # box/support: adapted unimodular frame (model, L 12; 10-17 at small L), ideal

# (label, log10 T at rho = 0.1 or None = the applications study's numbers, d'Alembert factor, delta power p)
SCEN = [
    ("apps baseline (L 85, S 1e8, box/support 6)", None, 1.0, None),
    ("v1, tau 2.4 interpolated (-130)", -130.0, 7.0, 9.6),
    ("v2 route B, tau 2, numerical gamma (-46.5)", -46.5, 7.0, 5.8),
    ("v2 route B, tau 3, FH gamma (-52.1)", -52.1, 7.0, 5.8),
    ("v2 hybrid L6 estimate (-23.3)", -23.3, 7.0, 5.8),
    ("v2 hybrid L6 estimate (-26.1)", -26.1, 7.0, 5.8),
]


def fmt(x):
    return "%.1e" % x if (x >= 1e4 or x < 1e-1) else ("%.0f" % x if x >= 10 else "%.1f" % x)


def rng(a, b):
    return "%s–%s" % (fmt(a), fmt(b))


def main():
    out = {}
    print("Per torus.  CPU-h = single-thread kernel time (the kernel is sequential per declaration; declarations run in\n"
          "parallel).  Ranges: operation counts lo .. hi (and memory factor 4 .. 8 for GMP).  This machine: %d cores,"
          " 124 GB.\n" % CORES_HERE)
    print("| scenario | rho | L | bits | S (true) | S_low | per-slot CPU-h, box layout | same, ideal layout "
          "| declarations (box) | advice TB (box) | data elaboration CPU-h (box) | GMP CPU-h | GMP min/product, peak GB "
          "| apps tier P CPU-h |")
    print("|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|")
    for name, lt, dal, p in SCEN:
        if lt is None:
            sup = dict(rho=0.1, L=85.0, S_pm=1e8, S=1e8, logT=-79.0)
            bbox, bideal = 6.0, 6.0
        else:
            sup = true_support(lt, dal, p)
            bbox, bideal = BETA_BOX, BETA_IDEAL
        S, L = sup["S"], sup["L"]
        S_low = low_support(sup["rho"], dal)
        r = {k: per_slot(S, L, S_low, o, bbox) for k, o in OPS.items()}
        ri = {k: per_slot(S, L, S_low, o, bideal) for k, o in OPS.items()}
        g = {k: gmp(S, L, S_low, o, bbox) for k, o in OPS.items()}
        ap = apps_projection(S, L, 100, box_factor=bbox / 2.0)
        print("| %s | %.2f | %.0f | %.0f | %s | %s | %s | %s | %s | %.2f–%.2f | %s | %s | %.0f, %.0f–%.0f (%d–%d blocks) | %s |" % (
            name, sup["rho"], L, bits(L), fmt(S), fmt(S_low), rng(r["lo"]["cpu_h"], r["hi"]["cpu_h"]),
            rng(ri["lo"]["cpu_h"], ri["hi"]["cpu_h"]), rng(r["lo"]["decls"], r["hi"]["decls"]),
            r["lo"]["data_GB"] / 1e3, r["hi"]["data_GB"] / 1e3, rng(r["lo"]["elab_cpu_h"][0], r["hi"]["elab_cpu_h"][1]),
            rng(g["lo"]["cpu_h"], g["hi"]["cpu_h_hi"]), g["lo"]["prod_s"] / 60, g["lo"]["peak_GB"][0],
            g["lo"]["peak_GB"][1], g["lo"]["blocks"][0], g["lo"]["blocks"][1],
            rng(ap["cpuh"]["P"][0], ap["cpuh"]["P"][1])))
        out[name] = dict(support=sup, S_low=S_low, beta_box=bbox, per_slot_box=r, per_slot_ideal=ri, gmp=g,
                         apps_tierP=ap["cpuh"]["P"])
    # calibration: the lunar unit (R1: S0 8400, 2-D diamond nu = 15.5, 3 full products, 140 shared model ops,
    # torsion stage 273 ops + 125 products on the cfgLow support S0 (17/88)^2 / 2) by the same per-term constants
    s0, slow = 8400.0, 8400.0 * (17 / 88.0) ** 2 / 2
    lun = (3 * s0 * (2 * C_TERM + 15.5 * C_SLOT) + 140 * s0 * C_OP + 125 * slow * (2 * C_TERM + 15.5 * C_SLOT)
           + 273 * slow * C_OP) / 3600
    print("\nCalibration: the lunar unit by these per-term constants (only demanded ops, trimmed cfgLow factors) is"
          " %.2f CPU-h,\nagainst 7.5-14.5 CPU-h for tier P (projected for the landed certificate, which evaluates every jet slot\nand"
          " untrimmed cfgLow factors, SHARP-CERTSIDE): ratio %.0f-%.0f, not resolved here.  The per-slot and GMP columns"
          " assume\nthe demanded-work design and may be optimistic by that ratio; the apps column is the landed one." % (
              lun, 7.5 / lun, 14.5 / lun))
    out["lunar_calibration_cpu_h"] = lun
    print("\nShard limits in a 32 GB slice (29 GB to the kernel):")
    print("  landed packed product (fit 6.8e-4 S^1.28 GB): S <= %.0f terms (2-D), one declaration" % (
        (KERNEL_GB / 6.8e-4) ** (1 / 1.28)))
    ns = KERNEL_GB * 1e9 / M_SLOT
    print("  per-slot route: <= %.1e advice slots per declaration (factors pre-packed as data), %.0f s kernel;"
          " model ops <= %.1e term-ops per declaration (%.0f s)" % (ns, ns * C_SLOT, KERNEL_GB * 1e9 / M_OP,
                                                                    KERNEL_GB * 1e9 / M_OP * C_OP))
    for L, beta in ((59, 10), (59, 6), (34, 10)):
        mx = [KERNEL_GB * 8e9 / m / (GMP_FBITS * slot_width(L) * beta) for m in GMP_MEM]
        print("  GMP-resident: one whole product per declaration up to S = %.1e .. %.1e (L %d, beta %d), %.0f .. %.0f s" % (
            mx[1], mx[0], L, beta, mx[1] * GMP_FBITS * slot_width(L) * beta * GMP_S_PER_BIT,
            mx[0] * GMP_FBITS * slot_width(L) * beta * GMP_S_PER_BIT))
    print("\nWall time = CPU-h / concurrent declarations.  Here: 124 GB allow 3 concurrent 32 GB declarations (about 12"
          " at 8 GB);\na 1000-core cluster with 32 GB per core runs 1000.")
    if "--json" in sys.argv:
        json.dump(out, open(sys.argv[sys.argv.index("--json") + 1], "w"), indent=1, default=float)


if __name__ == "__main__":
    main()
