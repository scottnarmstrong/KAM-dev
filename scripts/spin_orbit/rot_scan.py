#!/usr/bin/env python3
"""SO-GEN2 truncation scan: build the rotated candidate at several truncation levels and record the exact bounds.

usage: rot_scan.py which OUT.jsonl  [mode:]Lv,LE,LJ[,S]  ...      (S defaults to ceil(3.33 Lv) + 24)
mode: (none) absolute thresholds 10^-L on the SO-GEN witness E; n = absolute, E recomputed from v;
      w = importance-weighted thresholds (rot_build.IMP_*), SO-GEN E;  wn = weighted, E recomputed.
Each line of OUT.jsonl: the level, the support counts and every bound of rot_build.bounds (time scale c = 1).
"""
import sys, json, math, time
from rot_build import build


def default_bits(Lv):
    return int(math.ceil(3.33 * Lv)) + 24


def main(which, out, *specs):
    for sp in specs:
        mode = ""
        if ":" in sp:
            mode, sp = sp.split(":")
        a = [int(x) for x in sp.split(",")]
        Lv, LE, LJ = a[:3]
        S = a[3] if len(a) > 3 else default_bits(Lv)
        t0 = time.time()
        r = build(which, Lv, LE, LJ, S, weighted="w" in mode, newE="n" in mode)
        b = dict(r["bounds"])
        rec = dict(which=which, mode=mode, Lv=Lv, LE=LE, LJ=LJ, S=S, nv_half=r["nv_half"], nv_full=2 * r["nv_half"],
                   nE=r["nE"], np_half=r["np_half"], nJ_full=r["nJ_full"], seconds=round(time.time() - t0, 1), **b)
        with open(out, "a") as f:
            f.write(json.dumps(rec) + "\n")


if __name__ == "__main__":
    main(*sys.argv[1:])
