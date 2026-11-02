#!/usr/bin/env python3
"""HD11964-HOLO: the per-cell strip from the all-cells evaluations (estimated; Apache-2.0).

Inputs: `radius2a.py` records `radius2a-cK.json` (one per cell; the (2b) radius at rho = 0.01 and the T1 tail bounds
on the anisotropic grid rho_c in {0.02, 0.025, 0.03, 0.035} x rho_b in {0.1, 0.15, 0.2, 0.25}, sigma = 0.98 rho) and
`holo_margin.py` records `kepler-all-R.json` (the Kepler slack of planet c per cell at rho_c = R, rho_b = 0.15, and
min Re d2). For every cell the admissible strips are those with Kepler slack >= SLACK (default 0.04); among them the
strip minimising max(T_c, T_b) of T1 is chosen, with rho_b <= 0.15 (where the margins of planet b and of Re d2
were measured), or rho_b = RHOB exactly with --rhob=RHOB. Prints the table and the worst cell per slab, and writes a
JSON summary.
Usage: python3 -I allcells_summary.py --radius=DIR --kepler=DIR [--slack=0.04] [--rhob=0.15] [--out=F.json]
"""
import glob
import json
import os
import sys


def opt(name, default):
    return next((x.split("=", 1)[1] for x in sys.argv if x.startswith("--%s=" % name)), default)


def main():
    rdir, kdir = opt("radius", "."), opt("kepler", ".")
    slack = float(opt("slack", "0.04"))
    rhob = opt("rhob", "")
    kep = {}
    for f in glob.glob(os.path.join(kdir, "kepler-all-*.json")):
        d = json.load(open(f))
        kep[round(d["rho"][0], 4)] = {c["cell"]: (c["planet_c"]["slack"], c["d2_re_min"]) for c in d["cells"]}
    rows = []
    for f in sorted(glob.glob(os.path.join(rdir, "radius2a-c*.json")), key=lambda p: int(p.split("-c")[-1][:-5])):
        d = json.load(open(f))
        K = d["cell"]
        r = d["rho"]["0.01"]
        b0, bh = r["radius_2b_rho'=0"], r["radius_2b_rho'=0.005"]
        best = None
        for t in d["tails"]:
            rc, rb = round(t["rho_c"], 4), round(t["rho_b"], 4)
            if rc == rb or rb > 0.15 or rc not in kep or kep[rc][K][0] < slack:
                continue
            if rhob and rb != round(float(rhob), 4):
                continue
            m = max(t["T_bound"])
            if best is None or m < best[0]:
                best = (m, rc, rb, t["T_bound"], kep[rc][K])
        rows.append(dict(cell=K, slab=d["slab"], ratio=r["ratio"], r2b_real=b0["total"] / b0["chi1_norm"],
                         r2b_strip=bh["total"] / bh["chi1_norm"], strip=None if best is None else best[1:3],
                         T1=None if best is None else best[3], kepler_slack=None if best is None else best[4][0],
                         d2_min=None if best is None else best[4][1]))
    for x in rows:
        print("cell %2d  ratio %.3f  (2b) %5.1f%% / %5.1f%%  strip %s  T1 (c, b) %s  Kepler slack %s  min Re d2 %s" % (
            x["cell"], x["ratio"], 100 * x["r2b_real"], 100 * x["r2b_strip"], x["strip"],
            None if x["T1"] is None else "(%.2e, %.2e)" % tuple(x["T1"]),
            None if x["kepler_slack"] is None else "%.3f" % x["kepler_slack"],
            None if x["d2_min"] is None else "%.2f" % x["d2_min"]))
    for sl in sorted({x["slab"] for x in rows}):
        g = [x for x in rows if x["slab"] == sl and x["T1"] is not None]
        if g:
            w = max(g, key=lambda x: max(x["T1"]))
            print("slab %d: cells %d-%d, strips %s, worst T1 cell %d %s, max (2b) on the strip %.1f%%" % (
                sl, min(x["cell"] for x in g), max(x["cell"] for x in g), sorted({tuple(x["strip"]) for x in g}),
                w["cell"], "(%.2e, %.2e)" % tuple(w["T1"]), 100 * max(x["r2b_strip"] for x in g)))
    ok = [x for x in rows if x["T1"] is not None]
    worst = max(ok, key=lambda x: max(x["T1"])) if ok else None
    summ = dict(cells=len(rows), slack=slack, rhob=rhob or "<= 0.15", rows=rows,
                worst_T1=None if worst is None else dict(cell=worst["cell"], T1=worst["T1"], strip=worst["strip"]),
                worst_2b=max(rows, key=lambda x: x["r2b_strip"])["cell"] if rows else None)
    print("cells %d; worst T1 %s; worst (2b) on the strip: cell %s" % (len(rows), summ["worst_T1"], summ["worst_2b"]))
    path = opt("out", "")
    if path:
        with open(path, "w") as fh:
            json.dump(summ, fh, indent=1)


if __name__ == "__main__":
    main()
