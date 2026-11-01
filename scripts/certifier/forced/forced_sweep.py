#!/usr/bin/env python3
"""V2-TOOLS #6: variations of the forced toy through the mirror (frequency separation, twist, support, precision,
perturbation size, time scale).  Untrusted tooling; numbers for the regression report, not certificates.

    python3 -I scripts/certifier/forced/forced_sweep.py [--out scripts/certifier/fixtures/forced-toy/sweep.json]

For every variant of the Tiny spec: generate (forced_cert.generate), run every landed sub-check in the mirror,
and report err, M, the σ's, the support sizes, the genuine product pairs of the composition, Gram and torsion
(the kernel-cost driver: about 1 ms per pair, measured on Tiny), the producer time, and the threshold and margin
log10(e*/err) of the sharp engine (sharp_q), frozen route A (v2_q) and refined route A with classical site
constants (certified sites, as in forced_witness.py, need a built data module; they only raise the threshold).  A variant whose base checks fail in the mirror,
or whose err exceeds a route's threshold, is reported as rejected for that route; nothing here is a kernel claim.
"""
import argparse
import json
import math
import os
import sys
import time
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(1, os.path.join(HERE, "..", "..", "spin_orbit"))
sys.setrecursionlimit(100000)

import forced_build as FB          # noqa: E402
import forced_cert as FC           # noqa: E402
import forced_witness as FW        # noqa: E402
import sharp_q as SQ               # noqa: E402
import v2_r2 as R2                 # noqa: E402

ROOT = os.path.abspath(os.path.join(HERE, "..", "..", ".."))
TINY = FB.SPECS["Tiny"]

VARIANTS = [
    ("base (Tiny)", {}),
    ("separation N=10", dict(N=10)),
    ("separation N=14", dict(N=14)),
    ("separation N=24", dict(N=24)),
    ("twist β=1/4", dict(beta="1/4")),
    ("twist β=4", dict(beta="4")),
    ("support prune 1e-9", dict(prune_digits=9)),
    ("support prune 1e-11", dict(prune_digits=11)),
    ("support prune 1e-15", dict(prune_digits=15, char_tol="1/10000000000")),
    ("precision P=40", dict(P=40)),
    ("precision P=64", dict(P=64)),
    ("precision P=128", dict(P=128)),
    ("perturbation ε×10", dict(modes=[[[1, 0], "1/1000000"], [[1, 1], "1/500000"]])),
    ("time scale c=2", dict(c="2", s="1000001/1000000")),
]


def product_pairs(c):
    import sofx_check as C
    cf, cl = FC.make_cfgs(c.spec, c.books)
    c.cfgFull, c.cfgLow = cf, cl
    tot = {}
    for nm in ("checkEnergy", "checkGram", "checkTorsion"):
        cf.products.clear()
        cl.products.clear()
        dict(C.SUBCHECKS)[nm](c.B, c, {})
        tot[nm] = sum(a * b for _, r, a, b, _ in cf.products + cl.products if r != "scalar")
    return tot


def lg(x):
    return math.log10(float(x)) if x > 0 else float("-inf")


def run_variant(label, over, tag="Sweep", sites=True):
    spec = dict(TINY, **over)
    spec["name"] = tag
    t0 = time.time()
    try:
        c = FC.generate(spec, log=lambda *a: None)
    except Exception as e:                     # noqa: BLE001  (a producer failure is a reported outcome)
        return dict(label=label, spec=over, producer_error=repr(e)[:300])
    gen_s = time.time() - t0
    r = c.report
    p = dict(c.params)
    out = dict(label=label, spec=over, passes_base=r["passes_base"], producer_seconds=round(gen_s, 1),
               err=float(p["err"]), M=float(p["M"]), sK=float(p["sK"]), sB=float(p["sB"]), sT=float(p["sT"]),
               sizes=r["sizes"], N=c.toy.N, gamma=float(p["gamma"]))
    if not r["passes_base"]:
        out["failing"] = [k for k, v in r["checks"].items() if not v["ok"]]
        return out
    out["product_pairs"] = product_pairs(c)
    th = {}
    th["sharp"] = float(SQ.sharp(dict(p))["threshold"])
    box = c.freqBox
    d0 = min(F(1), (p["rho"] - p["rhoInf"]) / 6)
    Xs = R2.max_Xs("frozen", p, box, 5, F(1, 8), 20, lo=-30.0, hi=8.0, steps=36)
    th["frozenA"] = float(Xs * p["gamma"] ** 4 * d0 ** 4)
    if sites:
        # certified sites need the compiled Lean oracle on a built data module of the variant; the sweep uses
        # the classical site constants instead (a lower bound of the refined threshold)
        try:
            R, _ = FW.refined_claim(c)
            Q0 = FW.V.Num(n=2, tau=1, rho=p["rho"], rhoInf=p["rhoInf"], kp=3)
            sd = {}
            for s in range(3):
                sd[("d", s)] = FW.V.classical_c(2, 1, 20, Q0.delta(s))
                sd[("b", s)] = FW.V.classical_c(2, 1, 20, Q0.b(s))
            Xr = R2.max_Xs("refined", p, box, 3, F(1, 8), 20, R, sd, lo=-30.0, hi=8.0, steps=36)
            th["refinedA_classicalSites"] = float(Xr * p["gamma"] ** 4 * d0 ** 4)
        except AssertionError as e:
            th["refinedA_classicalSites"] = None
            out["refined_note"] = repr(e)[:200]
    out["thresholds"] = th
    out["margins_log10"] = {k: (round(lg(F(v)) - lg(p["err"]), 2) if v else None) for k, v in th.items()}
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", default=os.path.join(ROOT, "scripts", "certifier", "fixtures", "forced-toy",
                                                   "sweep.json"))
    a = ap.parse_args()
    rows = []
    for label, over in VARIANTS:
        row = run_variant(label, over)
        rows.append(row)
        print(json.dumps({k: row.get(k) for k in ("label", "passes_base", "err", "M", "sT", "margins_log10",
                                                    "product_pairs", "producer_seconds", "failing",
                                                    "producer_error")}, default=str), flush=True)
    with open(a.out, "w") as fh:
        json.dump(rows, fh, indent=1, default=str)


if __name__ == "__main__":
    main()
