#!/usr/bin/env python3
"""HD11964 phase 2 (COVER-D): the sampled range of F_i - Lam_i on R(d), against the range over the whole cell box
(float64, untrusted, Apache-2.0).

The cover's cells are boxes that only have to meet R(d); the b-squares' corners reach outside it.  For every cell of
one xi_c interval (default: the lowest, xi_c = 0.03, which carries the global F_b - Lam_b bound), this samples the
F - Lam polynomial of `cover2.run_cell` (same producer, grid and S) at random box points, and at random points of
R(d) (box points with Gam_c + Gam_b <= Cmax, plus points on the rim Gam_b = Cmax - Gam_c), each on the full angle
grid.  Sampled minima and maxima only: no bound.

Usage: python3 -I cover2_inregion.py OUT.jsonl --d=2e-3 --hb=0.04 [--xic=0.03] [--procs=2] [--npts=600]
       python3 -I cover2_inregion.py --summary OUT.jsonl SUMMARY.json
Run under the 8 GB cap (each process <= 2.1 GB).
"""
import json
import math
import multiprocessing as mpr
import os
import sys
import time

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import cover2 as C  # noqa: E402
import hd11964_model as HM  # noqa: E402


def gam(x, y):
    return (x * x + y * y) / 2


def evalJ(pr, J, xs):
    lo, hi = np.inf, -np.inf
    mons = pr.S6.mons[: pr.S6.M(J.deg)]
    for x in xs:
        wv = np.array([np.prod([x[j] ** e for j, e in enumerate(mon)]) for mon in mons])
        v = np.tensordot(wv, J.c, axes=(0, 0))
        lo, hi = min(lo, float(np.min(v))), max(hi, float(np.max(v)))
    return lo, hi


def run(task):
    from prod2 import Prod2
    cell, nu, mu, npts = task
    t0 = time.time()
    a = [(cell["Lam"][i] / nu[i]) ** 2 for i in range(2)]
    N1, N2 = C.gate.grid_for(cell["emax"][0], cell["emax"][1], a)
    N1, N2 = max(N1, 256), max(N2, 64)
    pr = Prod2(nu, mu, N1=N1, N2=N2, N=4, K1solve=C.KC, K2solve=C.KB)
    pr.setup(cell["Lam"], cell["xi"], cell["eta"])
    pr.run2()
    H = np.asarray(cell["h"])
    rng = np.random.default_rng(7 + cell["id"])
    box = rng.uniform(-1, 1, size=(npts, 6)) * H
    inside, rim = [], []
    for x in box:
        gc = gam(cell["xi"][0] + x[2], cell["eta"][0] + x[3])
        gb = gam(cell["xi"][1] + x[4], cell["eta"][1] + x[5])
        if gc + gb <= C.GMAX:
            inside.append(x)
    # rim points: Gam_b = GMAX - Gam_c exactly, inside the b square
    tries = 0
    while len(rim) < npts // 3 and tries < 50 * npts:
        tries += 1
        x = rng.uniform(-1, 1, size=6) * H
        gc = gam(cell["xi"][0] + x[2], cell["eta"][0] + x[3])
        Rb = math.sqrt(max(0.0, 2 * (C.GMAX - gc)))
        ph = rng.uniform(0, 2 * math.pi)
        xb, yb = Rb * math.cos(ph) - cell["xi"][1], Rb * math.sin(ph) - cell["eta"][1]
        if abs(xb) <= H[4] and abs(yb) <= H[5]:
            x[4], x[5] = xb, yb
            rim.append(x)
    res = dict(id=cell["id"], xi=cell["xi"], eta=cell["eta"], h=cell["h"], n_in=len(inside), n_rim=len(rim))
    for i, name in enumerate(("c", "b")):
        FmL = pr.terms[i][1]
        res[name] = dict(box=evalJ(pr, FmL, box), region=evalJ(pr, FmL, inside + rim) if inside + rim else None)
    res["seconds"] = time.time() - t0
    return res


def summary(path, out):
    rows = sorted((json.loads(x) for x in open(path)), key=lambda r: r["id"])
    res = dict(d=C.D_DRIFT, Cmax=C.GMAX, cells=len(rows), planets={})
    for p in ("c", "b"):
        blo, bhi = min(r[p]["box"][0] for r in rows), max(r[p]["box"][1] for r in rows)
        rr = [r for r in rows if r[p]["region"]]
        rlo, rhi = min(r[p]["region"][0] for r in rr), max(r[p]["region"][1] for r in rr)
        res["planets"][p] = dict(box_sampled=[blo, bhi], box_width=bhi - blo,
                                 region_sampled=[rlo, rhi], region_width=rhi - rlo)
    res["per_cell"] = [dict(id=r["id"], xi=r["xi"], eta=r["eta"], n_in=r["n_in"], n_rim=r["n_rim"],
                            b_box=[float("%.4g" % x) for x in r["b"]["box"]],
                            b_region=[float("%.4g" % x) for x in r["b"]["region"]] if r["b"]["region"] else None,
                            seconds=round(r["seconds"], 1)) for r in rows]
    with open(out, "w") as fh:
        json.dump(res, fh, indent=1)
    print(json.dumps({k: v for k, v in res.items() if k != "per_cell"}, indent=1))


def main():
    if "--summary" in sys.argv:
        args = [x for x in sys.argv[1:] if not x.startswith("--")]
        summary(args[0], args[1])
        return
    out = sys.argv[1]
    xic = float(C.opt("xic", "0.03"))
    npts = int(C.opt("npts", "600"))
    m = HM.Model()
    nu = [float(HM.R(x)) for x in m.nu]
    mu = float(HM.R(m.mu))
    cells, _ = C.plan(m)
    sel = [c for c in cells if abs(c["xi"][0] - xic) < 1e-6]
    print("d", C.D_DRIFT, "cells", len(sel), flush=True)
    with mpr.get_context("fork").Pool(int(C.opt("procs", "2")), maxtasksperchild=1) as pool, open(out, "w") as fh:
        for r in pool.imap_unordered(run, [(c, nu, mu, npts) for c in sel]):
            fh.write(json.dumps(r) + "\n")
            fh.flush()
            print(r["id"], r["xi"], r["eta"], r["n_in"], r["n_rim"], "b box %.3g %.3g region %s  %.0fs" % (
                *r["b"]["box"], r["b"]["region"], r["seconds"]), flush=True)


if __name__ == "__main__":
    main()
