#!/usr/bin/env python3
"""V2-TOOLS #3: snapshot the inputs of route selection into fixtures (untrusted tooling; numbers with provenance).

    python3 -I scripts/certifier/route_profiles.py [--lg00 /path/to/lg00-cert/worktree]

Writes scripts/certifier/fixtures/route-select/:
  lunar65.json  the lunar R2 package (N = 65, lower torus): CertParams and refined claim of scripts/spin_orbit/
                v2_r2.py (`package`, `R65`), the achieved residual against the truncation L at ρ = 1/140 and its ρ
                dependence at L = 20 (docs/tracks/SO/studies/SO-V2PKG.md §3, §4.6: checker err = emitter e / 2), the
                support (v half-terms) per L, the measured kernel cost at the hand choice (SO-CSPLIT-GATE: 1.6–2.5
                CPU-h per torus at L = 20, CertFixed 96), the certified-bite costs (SHARP2-C6: l = 8..12), the hand
                choice (refined route A, d01b sites, kp = 3, L = 20, ρ = 1/140, P = 96, one-order rule);
  lg00.json     the LG00 package (Locatelli–Giorgilli secular SJS): CertParams of the L = 20 dry run, the frequency
                box, the refined claim (LG00-CERT handoff), err against L (LG00-PREP §5 table, anchored at the fixed
                torus' 7.2e-16 at L = 18 and 8.1e-18 at L = 20), the support per L, the run20e ledger total and its
                split by module kind, the hand choice (refined route A, classical sites, L = 20, P = 128);
  ledger_fit.json  the LG00 ledger aggregated by module kind (CPU-h, modules, max RSS).
The LG00 numbers are read from the lg00-cert worktree once (path argument); the selection tool then depends only on
the fixtures.
"""
import argparse
import collections
import json
import math
import os
import sys
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))
OUT = os.path.join(HERE, "fixtures", "route-select")
sys.path.insert(0, os.path.join(ROOT, "scripts", "spin_orbit"))
sys.path.insert(1, os.path.join(ROOT, "scripts", "apost_sharp"))


def js(x):
    if isinstance(x, F):
        return str(x)
    if isinstance(x, dict):
        return {str(k): js(v) for k, v in x.items()}
    if isinstance(x, (list, tuple)):
        return [js(v) for v in x]
    return x


def lunar65():
    import v2_r2 as R2
    p = R2.package(65)
    box = R2.box_of(p, "lower")
    prof = dict(
        name="lunar65", title="lunar spin-orbit band, N = 65, lower torus (package R2)",
        params={k: v for k, v in p.items() if k not in ("kappa", "N", "c")}, kappa=p["kappa"], N=65,
        box=box, R=R2.R65["lower"], rho_fixed=False,
        rho_grid=["1/280", "1/140", "1/100", "1/70"],
        # checker err (emitter e / 2) against L at rho = 1/140 (SO-V2PKG §3)
        err_L={"14": "3.75e-11", "16": "6e-13", "18": "1.5e-14", "20": "1.6e-16", "22": "2.15e-18",
               "26": "7e-22", "40": "3.4e-35"},
        # emitter e at L = 20 against rho (SO-V2PKG §4.6), as factors of the rho = 1/140 value
        err_rho_factor={"1/280": str(F(18, 32)), "1/140": "1", "1/100": str(F(53, 32)), "1/70": str(F(80, 32))},
        support_L={"14": 108, "16": 146, "18": 191, "20": 251, "22": 305, "26": 439, "40": 1180},
        P_grid=[96, 128], P_ref=96,
        cost_ref=dict(cpu_h="2.0", range="1.6-2.5", L=20, P=96, source="SO-CSPLIT-GATE.md (v2 at L = 20)"),
        site_cost_s={"8": 2.4, "9": 6.1, "10": 10.8, "11": 34.3, "12": 85.2},
        site_l_rule=dict(delta="2.4", b="1.8", source="SO-V2PKG §2.2: 2^l · bite ≈ 2.4 (δ sites), 1.8 (b sites)"),
        site_l_max=12, A_meas="7.28e-4", A_meas_source="thresholds_v2.A_MEAS_R1 (step0_actual.py, R1 package)",
        hand=dict(route="A.refined.certified", kp=3, L=20, rho="1/140", P=96, margin=1.53,
                  note="d01b: certified δ0, δ1 and b0..b2 (l = 8..12); SO-V2PKG §2, §3"),
        margin_rule=1.0)
    return prof


def lg00(path):
    rep = json.load(open(os.path.join(path, "scripts", "sjs", "lg00", "results", "lg00_dryrun_sqrt_L20.json")))
    sys.path.insert(0, os.path.join(path, "scripts", "sjs", "lg00"))
    import lg00_gen as G
    p = {k: F(v) for k, v in rep["params"].items()}
    kappa = F(160000)
    box = [(F(c), F(r)) for c, r in G.freq_box(kappa / p["s"])]
    led = os.path.join(path, "docs", "campaign", "handoffs", "LG00-CERT-ledger", "run20e.tsv")
    agg = collections.defaultdict(lambda: [0, 0.0, 0])
    for ln in open(led):
        f = ln.rstrip("\n").split("\t")
        if len(f) < 7:
            continue
        kind = f[0].split(".")[2]
        a = agg[kind]
        a[0] += 1
        a[1] += float(f[1]) + float(f[2])
        a[2] = max(a[2], int(f[4]))
    fit = {k: dict(modules=a[0], cpu_h=round(a[1] / 3600, 3), max_rss_gb=round(a[2] / 1e6, 2)) for k, a in agg.items()}
    total = sum(a[1] for a in agg.values()) / 3600
    prof = dict(
        name="lg00", title="LG00: Locatelli–Giorgilli secular Sun–Jupiter–Saturn torus (route A refined)",
        params={k: v for k, v in p.items()}, kappa=kappa, box=box,
        R=dict(dh=F("82.7"), dx=F(249), d2x=F(5170), d2h=F(559), bL=F("1.37"), bN=F("1.21"), bNt=F("1.45"),
               bT=F(118)),
        rho_fixed=True, rho_grid=[str(p["rho"])],
        err_L={"12": "2.6e-10", "18": "7.2e-16", "20": "8.1e-18", "24": "1.4e-21", "30": "1.9e-27", "36": "2.7e-33",
               "40": "3.3e-37"},
        support_L={"8": 110, "12": 250, "18": 550, "20": 683, "24": 986, "30": 1556, "36": 2306, "40": 2840},
        P_grid=[96, 128], P_ref=128,
        cost_ref=dict(cpu_h=str(round(total, 2)), L=20, P=128, source="LG00-CERT run20e ledger (passing set)"),
        site_cost_s={"8": 2.4, "9": 6.1, "10": 10.8, "11": 34.3, "12": 85.2},
        site_l_rule=dict(delta="2.4", b="1.8", source="SO-V2PKG §2.2 rule, transferred"),
        site_l_max=12, A_meas=None, A_meas_source="not measured for LG00",
        hand=dict(route="A.refined.classical", kp=3, L=20, rho=str(p["rho"]), P=128, margin=2.0,
                  note="LG00-CERT: route A refined, classical sites, err 8.1e-18 vs 7.9e-16"),
        margin_rule=1.0, ledger=fit, ledger_total_cpu_h=round(total, 2),
        # the L = 8 pilot (LG00-CERT handoff, status (2)): torsion 64 modules 2311 s; Gram packed 8 modules,
        # 22-40 s each (31 s taken); support 110 at L = 8, 683 at L = 20
        pilot_L8=dict(support=110, torsion_s=2311, gram_s=248, source="LG00-CERT.md, status (2)"),
        provenance=dict(report="lg00-cert scripts/sjs/lg00/results/lg00_dryrun_sqrt_L20.json",
                        box="lg00_gen.freq_box(160000/s)", claim="LG00-CERT.md §Route and threshold",
                        err_table="docs/explorations/lg00-prep.md §5 and LG00-CERT.md (fixed torus)"))
    return prof, fit


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--lg00", default="/home/scott/KAM-dev-worktrees/lg00-cert")
    a = ap.parse_args()
    os.makedirs(OUT, exist_ok=True)
    with open(os.path.join(OUT, "lunar65.json"), "w") as fh:
        json.dump(js(lunar65()), fh, indent=1, sort_keys=True)
    if os.path.isdir(a.lg00):
        prof, fit = lg00(a.lg00)
        with open(os.path.join(OUT, "lg00.json"), "w") as fh:
            json.dump(js(prof), fh, indent=1, sort_keys=True)
        with open(os.path.join(OUT, "ledger_fit.json"), "w") as fh:
            json.dump(dict(lg00_run20e=fit), fh, indent=1, sort_keys=True)
    print("wrote", sorted(os.listdir(OUT)))


if __name__ == "__main__":
    main()
