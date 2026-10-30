#!/usr/bin/env python3
"""SJS-FEAS: summarize the kernel probes (scripts/sjs/results/kernel_probes_raw.jsonl) into fitted laws and the
extrapolation to S = 1e7 / 1e8 Fourier coefficients.

usage: kernel_probe_summary.py   (writes scripts/sjs/results/kernel_probes.json and kernel_probes.md)

Every number in the "measured" tables is a probe record (Lean profiler "type checking took" of the probe's one
theorem = kernel time; RSS = /usr/bin/time peak of the whole `lake env lean` process, including the ~3.1 GB
Mathlib import baseline; machine load 12-14 on 16 cores, so +-30 %). Fits are least squares on these points;
the extrapolations are MODEL estimates (stated formulas), not measurements. Untrusted tooling.
"""
import json
import math
import os

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
RES = os.path.join(HERE, "results")
BASE_RSS = 3.11          # GB: Mathlib-importing probe with tiny data (packed_data_d2b_K15: 3.12, model_data_K15: 3.11)
BASE_RSS_NOMATH = 0.78   # GB: probes without Mathlib (floor, gmp)


def load():
    recs = {}
    with open(os.path.join(RES, "kernel_probes_raw.jsonl")) as f:
        for ln in f:
            r = json.loads(ln)
            recs[r["tag"]] = r          # later runs of the same tag win (the K15 literal re-run)
    return recs


def powfit(xs, ys):
    lx, ly = np.log(np.array(xs, float)), np.log(np.array(ys, float))
    A = np.vstack([lx, np.ones_like(lx)]).T
    coef, res, *_ = np.linalg.lstsq(A, ly, rcond=None)
    p, c = coef
    resid = ly - A @ coef
    dof = max(1, len(xs) - 2)
    s2 = float(resid @ resid) / dof
    cov = s2 * np.linalg.inv(A.T @ A)
    return dict(p=float(p), p_se=float(math.sqrt(cov[0, 0])), a=float(math.exp(c)), n=len(xs))


def linfit(X, y):
    X, y = np.array(X, float), np.array(y, float)
    coef, *_ = np.linalg.lstsq(X, y, rcond=None)
    resid = y - X @ coef
    dof = max(1, len(y) - X.shape[1])
    s2 = float(resid @ resid) / dof
    cov = s2 * np.linalg.pinv(X.T @ X)
    return [float(c) for c in coef], [float(math.sqrt(max(0.0, cov[i, i]))) for i in range(X.shape[1])], \
        float(math.sqrt(s2))


def k(recs, tag, key="kernel_s"):
    r = recs.get(tag)
    return None if r is None else r.get(key)


def main():
    R = load()
    out = dict(measured={}, fits={}, extrapolation={}, notes=[])
    M = out["measured"]

    # ---- A. landed checkPackedProduct (2-D box, B = 200, blockRows 1)
    A = []
    for K in (7, 10, 15):
        r = R["packed_full_d2b_K%d_b200_r1" % K]
        m = r["meta"]
        A.append(dict(K=K, S=m["S"], denseLen=m["denseLen"], prodLen=m["prodLen"], shards=m["shards"],
                      window=2 * m["blockLen"] - 1, advice_slots=m["advice_slots"], w=m["w"],
                      kernel_s=r["kernel_s"], rss_gb=round(r["rss_gb"], 2)))
    M["landed_full_2d_box_b200_r1"] = A
    out["fits"]["landed_full_time_vs_S"] = powfit([a["S"] for a in A], [a["kernel_s"] for a in A])
    out["fits"]["landed_full_extra_rss_vs_S"] = powfit([a["S"] for a in A], [a["rss_gb"] - BASE_RSS for a in A])
    M["landed_parts_S961"] = {v: dict(kernel_s=k(R, "packed_%s_d2b_K15_b200_r1" % v),
                                      rss_gb=round(k(R, "packed_%s_d2b_K15_b200_r1" % v, "rss_gb"), 2))
                              for v in ("dense", "pack", "mul", "shape", "guards", "fits", "decode", "full", "prr")}
    M["landed_variations"] = {t: dict(kernel_s=k(R, t), rss_gb=round(k(R, t, "rss_gb"), 2), S=R[t]["meta"]["S"])
                              for t in ("packed_full_d2b_K10_b100_r1", "packed_full_d2b_K10_b200_r1",
                                        "packed_full_d2b_K10_b300_r1", "packed_full_d2b_K15_b200_r4",
                                        "packed_full_d3b_K3_b200_r1", "packed_Lshard_d2b_K50_b200_r4")}

    # ---- B. prototype fixed route (sparse term packing, offset shift-tree advice packing, D&C decode / mask)
    B = []
    for t, r in R.items():
        if t.startswith("packed_F") and r["exit"] == 0:
            m = r["meta"]
            B.append(dict(tag=t, variant=m["variant"], dim=m["dim"], shape=m["shape"], S=m["S"], rows=m["rows"],
                          blockLen=m["blockLen"], shards=m["shards"], advice_slots=m["advice_slots"],
                          denseLen=m["denseLen"], prodLen=m["prodLen"], kernel_s=r["kernel_s"],
                          rss_gb=round(r["rss_gb"], 2)))
    M["prototype_fixed_route"] = sorted(B, key=lambda x: (x["variant"], x["S"]))
    dec = [b for b in B if b["variant"] == "Fdec"]
    coef, se, sd = linfit([[b["advice_slots"], 2 * b["S"]] for b in dec], [b["kernel_s"] for b in dec])
    out["fits"]["Fdec_time"] = dict(model="t = c_slot * advice_slots + c_term * (2 S)", c_slot_ms=coef[0] * 1e3,
                                    c_slot_se_ms=se[0] * 1e3, c_term_ms=coef[1] * 1e3, c_term_se_ms=se[1] * 1e3,
                                    resid_sd_s=sd, n=len(dec))
    coef, se, sd = linfit([[b["advice_slots"], 2 * b["S"]] for b in dec], [b["rss_gb"] - BASE_RSS for b in dec])
    out["fits"]["Fdec_extra_rss"] = dict(model="GB = m_slot * advice_slots + m_term * (2 S)", m_slot_kb=coef[0] * 1e6,
                                         m_term_kb=coef[1] * 1e6, resid_sd_gb=sd, n=len(dec))
    pk = [b for b in B if b["variant"] in ("Fpack",)]
    out["fits"]["Fpack_ms_per_term"] = [b["kernel_s"] / (2 * b["S"]) * 1e3 for b in pk]
    ad = [b for b in B if b["variant"] == "Fadv"]
    out["fits"]["Fadv_ms_per_advice_slot"] = [b["kernel_s"] / b["advice_slots"] * 1e3 for b in ad]

    # ---- C. micro primitives (in-kernel data, w = 2B + log n + 3, B = 200)
    C = {}
    for t, r in R.items():
        if t.startswith("micro_"):
            m = r.get("meta", {})
            C[t] = dict(n=m.get("n"), w=m.get("w"), kernel_s=r["kernel_s"], rss_gb=round(r["rss_gb"], 2),
                        exit=r["exit"])
    M["micro"] = C
    dslot = {}
    for n in (1000, 3000, 10000):
        a, b = k(R, "micro_Pdec_n%d_b200" % n), k(R, "micro_Pmul_n%d_b200" % n)
        if a and b:
            dslot["Pdec_n%d_ms_per_slot" % n] = (a - b) / (2 * n - 1) * 1e3
    for n in (1000, 2000, 3000):
        a, b = k(R, "micro_Ldec_n%d_b200" % n), k(R, "micro_Lmul_n%d_b200" % n) or None
        if a:
            base = b if b else 2 * (k(R, "micro_Lpack_n%d_b200" % n) or 0)
            dslot["Ldec_n%d_ms_per_slot" % n] = (a - (base or 0)) / (2 * n - 1) * 1e3
    out["fits"]["decode_per_slot"] = dslot

    # ---- D. GMP in the kernel
    G = {}
    for n in (100000000, 400000000):
        base = k(R, "gmp_base_n%d" % n)
        for op in ("add", "mul", "land", "shr", "rep"):
            G["%s_%dbits" % (op, n)] = dict(kernel_s=k(R, "gmp_%s_n%d" % (op, n)),
                                            net_s=k(R, "gmp_%s_n%d" % (op, n)) - base)
    M["gmp"] = G
    out["fits"]["gmp_mul_ns_per_bit"] = {"1e8": G["mul_100000000bits"]["net_s"] / 1e8 * 1e9,
                                         "4e8": G["mul_400000000bits"]["net_s"] / 4e8 * 1e9}

    # ---- E. per-element floor of kernel evaluation
    M["floor"] = {t: dict(kernel_s=k(R, t), rss_gb=round(k(R, t, "rss_gb"), 2))
                  for t in ("floor_kp_floor_n10000", "floor_kp_floor_n30000", "floor_kp_floorI_n30000",
                            "floor2_range", "floor2_rangeF", "floor2_length", "floor2_forced")}
    out["fits"]["floor_us_per_element"] = dict(
        literal_list_walk=k(R, "floor2_length") / 3e4 * 1e6,
        literal_list_sum=k(R, "floor_kp_floor_n30000") / 3e4 * 1e6,
        literal_int_abs_sum=k(R, "floor_kp_floorI_n30000") / 3e4 * 1e6,
        range_sum_forced=k(R, "floor2_rangeF") / 3e4 * 1e6,
        memory_kb_per_element_walk=(k(R, "floor2_length", "rss_gb") - k(R, "floor2_data", "rss_gb")) / 3e4 * 1e6)

    # ---- F. per-coefficient model passes (CertFixed P, production weight w ~ 1.094, 2-D box)
    F = []
    for t, r in R.items():
        if t.startswith("model_") and "_data_" not in t and "_length_" not in t:
            m = r["meta"]
            F.append(dict(tag=t, variant=m["variant"], dim=m["dim"], S=m["S"], prec=m["prec"], weight=m["weight"],
                          exit=r["exit"], kernel_s=r["kernel_s"] if r["exit"] == 0 else None,
                          ms_per_term=(r["kernel_s"] / m["S"] * 1e3) if r["exit"] == 0 and r["kernel_s"] else None,
                          rss_gb=round(r["rss_gb"], 2)))
    M["model_passes"] = sorted(F, key=lambda x: (x["variant"], x["S"], x["prec"]))

    # ---- G. compose experiment
    Gc = {}
    for t, r in R.items():
        if t.startswith("compose_") and t != "compose_test":
            m = r["meta"]
            Gc[t] = dict(S=m["S"], ops=m["ops"], kernel_s=r["kernel_s"], rss_gb=round(r["rss_gb"], 2))
    M["compose_experiment"] = Gc
    for K, S in ((10, 441), (15, 961)):
        g = lambda v: Gc["compose_%s_K%d" % (v, K)]["kernel_s"]
        out["fits"]["compose_K%d" % K] = dict(
            S=S, separate_E_plus_I=g("E") + g("I"), one_decl_two_composes=g("EI"), one_compose_shared=g("shared"),
            pruned=g("pruned"), all_slots_forced=g("all"),
            dead_op_cost_s=(g("all") - g("shared")) / 8, ms_per_term_op=(g("all") - g("shared")) / 8 / S * 1e3,
            extra_rss_kb_per_live_term_op=(Gc["compose_shared_K%d" % K]["rss_gb"] - BASE_RSS) * 1e6 / (14 * S))
    M["prune_cost"] = {t: dict(kernel_s=k(R, t), rss_gb=round(k(R, t, "rss_gb"), 2), exit=R[t]["exit"],
                               ops=R[t]["meta"]["ops"]) for t in R if t.startswith("prune_")}
    try:
        with open(os.path.join(RES, "jet_counts.json")) as f:
            M["jet_counts"] = json.load(f)
    except OSError:
        pass

    # ---- extrapolation (model)
    fd = out["fits"]["Fdec_time"]
    fm = out["fits"]["Fdec_extra_rss"]
    # component constants (direct measurements, preferred over the collinear 2-parameter fit):
    # advice packing 0.61-0.95 ms/slot (Fadv) + D&C decode 0.20-0.34 ms/slot (Pdec - Pmul) ~ 1.0 ms per advice slot;
    # term-driven factor packing 1.25-1.48 ms per factor term (Fpack), two factors.
    c_slot, c_term = 1.0e-3, 1.4e-3
    m_slot = fm["m_slot_kb"] * 1e3       # bytes
    term_op = out["fits"]["compose_K15"]["ms_per_term_op"] / 1e3
    gm = out["fits"]["gmp_mul_ns_per_bit"]["4e8"] * 1e-9
    nu = {"2d box": 7.7, "3d box": 13.5, "2d diamond": 15.5, "3d diamond (asymptotic 2*48)": 96.0,
          "4d box": 32.0, "4d diamond (asymptotic 2*384)": 768.0}
    E = {}
    for S in (1e7, 1e8):
        for bits, w in ((300, 2 * 300 + 40), (170, 2 * 170 + 40)):
            row = {}
            for shape, v in nu.items():
                slots = v * S
                t = c_slot * slots + c_term * 2 * S
                memb = m_slot * slots
                dense = slots / 4.0           # ~ denseLen (the advice covers ~2 x prodLen ~ 4 x denseLen)
                F_bits = dense * w
                gmp_floor = gm * 2 * F_bits * (1 + 0.1 * math.log2(max(1.0, 2 * F_bits / 4e8))) + 10 * 0.6e-9 * 2 * F_bits
                row[shape] = dict(advice_slots=slots, per_real_product_cpu_h_prototype=t / 3600,
                                  per_real_product_decl_memory_gb_unsharded=memb / 1e9,
                                  min_declarations_at_29GB=math.ceil(memb / 29e9),
                                  factor_bits=F_bits, gmp_floor_s_per_product=gmp_floor,
                                  gmp_floor_peak_gb=8 * F_bits / 8 / 1e9)
            E["S=%.0e, B=%d (w~%d)" % (S, bits, w)] = row
        E["model_op_per_term_pass S=%.0e" % S] = dict(cpu_h_per_op=term_op * S / 3600,
                                                      lunar_shared_inv_energy_140_ops_cpu_h=140 * term_op * S / 3600,
                                                      planetary_toy_M64_shared_1989_ops_cpu_h=1989 * term_op * S / 3600)
    lf = out["fits"]["landed_full_time_vs_S"]
    lm = out["fits"]["landed_full_extra_rss_vs_S"]
    E["landed_checkPackedProduct_2d_box (power law of 3 points, S <= 961; decode cliff beyond ~4000-slot windows)"] = {
        "S=%.0e" % S: dict(cpu_h=lf["a"] * S ** lf["p"] / 3600, memory_gb=lm["a"] * S ** lm["p"]) for S in (1e4, 1e7, 1e8)}
    E["constants_used"] = dict(c_slot_ms=c_slot * 1e3, c_term_ms=c_term * 1e3, m_slot_kb=m_slot / 1e3,
                               term_op_ms=term_op * 1e3, gmp_mul_ns_per_bit=gm * 1e9, nu_advice_slots_per_term=nu)
    out["extrapolation"] = E
    out["notes"] = [
        "Landed checker = this worktree's KAM/Certificate/Poly (pre-D34). The D34 fix (sparse blocks, mask/shift "
        "decode; branch inp-sopackfixl on the farm) is NOT in this worktree; the F* probes are prototypes of the "
        "same ideas (no soundness proofs), used as its stand-in.",
        "Kernel times are 'type checking took' of the probe theorem; RSS includes the 3.1 GB Mathlib import.",
        "Machine load 12-14 on 16 cores throughout: +-30 % on every timing.",
    ]
    with open(os.path.join(RES, "kernel_probes.json"), "w") as f:
        json.dump(out, f, indent=1, default=float)
    print(json.dumps(out["fits"], indent=1, default=float))
    print(json.dumps(out["extrapolation"], indent=1, default=float)[:6000])


if __name__ == "__main__":
    main()
