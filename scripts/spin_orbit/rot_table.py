#!/usr/bin/env python3
"""SO-GEN2 truncation tables from rot_scan output (absolute-threshold mode, SO-GEN witness E).

usage: rot_table.py SCAN_lower.jsonl SCAN_upper.jsonl OUTDIR  c m  c_alt m_alt
Writes OUTDIR/{lower,upper}_rot_truncation.json: per level L (= Lv = LE = LJ) the support, bits and the
enclosed errors at time scale 1 and c, with eta_c/threshold for the primary (l1 Gram bound) and the
alternative (grid Gram bound) package.  Untrusted tooling.
"""
import sys, json, math
from fractions import Fraction as F
from exact_constants import package_R1, threshold_of


def thr(c, m):
    p, x = package_R1(F(c), F(m))
    t, _, _ = threshold_of(p, x["gamma"])
    return float(t)


def main(sl, su, outdir, c, m, ca, ma):
    T = thr(c, m); Ta = thr(ca, ma)
    cf, caf = float(F(c)), float(F(ma) * 0 + F(ca))
    for which, path in (("lower", sl), ("upper", su)):
        rows = {}
        for line in open(path):
            r = json.loads(line)
            if r.get("mode", "") or not (r["Lv"] == r["LE"] == r["LJ"]):
                continue
            eta = max(r["eta1_unscaled"], r["eta3_unscaled"], r["eta4_unscaled"], r["energy_unscaled"])
            rows[r["Lv"]] = dict(L=r["Lv"], bits=r["S"], v_terms_half=r["nv_half"], v_terms_full=r["nv_full"],
                                 E_terms=r["nE"], p_terms_half=r["np_half"], J_terms_full=r["nJ_full"],
                                 product_pairs_vE=r["nv_full"] * r["nE"],
                                 eta_unscaled=eta, Delta=r["Delta"], B0=r["B0"], B1_unscaled=r["B1_unscaled"],
                                 B2=r["B2"], eta_c_over_threshold_R1=cf * eta / T,
                                 eta_c_over_threshold_R1grid=caf * eta / Ta)
        out = dict(which=which, threshold_R1=T, c_R1=c, m_R1=m, threshold_R1grid=Ta, c_R1grid=ca, m_R1grid=ma,
                   rule="drop |coefficient| < 10^-L in v, E (SO-GEN witness) and J; round to `bits`",
                   levels=[rows[k] for k in sorted(rows)])
        json.dump(out, open("%s/%s_rot_truncation.json" % (outdir, which), "w"), indent=1)
        for k in sorted(rows):
            x = rows[k]
            print(which, k, x["bits"], x["v_terms_half"], x["E_terms"], x["J_terms_full"],
                  "eta %.2e  eta_c/thr R1 %.2e  R1grid %.2e" % (x["eta_unscaled"], x["eta_c_over_threshold_R1"],
                                                               x["eta_c_over_threshold_R1grid"]))


if __name__ == "__main__":
    main(*sys.argv[1:])
