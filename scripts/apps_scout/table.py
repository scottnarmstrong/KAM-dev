#!/usr/bin/env python3
"""Assemble results/*.json into the tables of docs/explorations/striking-applications.md.  Writes results/table.md and prints it."""
import json
import math
import os

import costmodel as cm
import pipeline as pl

RES = pl.RES


def load(name):
    p = os.path.join(RES, name)
    return json.load(open(p)) if os.path.exists(p) else {}


# full-precision products per torus: traced by count_products.py, except where a hand count with witness sharing is stated in the study
NF = {"Moon rot": 3, "Moon lib": 15, "Mercury": 3, "Kepler": 9, "Saturn": 3, "CC07": 79, "PCR3BP": 50, "Trojan": 86, "Hill": 36, "tokamak": 12}


def row(label, a, nf, tori=1, nlow=125):
    b, v, c = a["best"], a["best_v2"], a["best_cur"]
    S = dict(current=c["S"]["current"], v1=b["S"]["v1"], v2=v["S"]["v2"])
    L = dict(current=c["L"]["current"], v1=b["L"]["v1"], v2=v["L"]["v2"])
    cost = {k: cm.project(S[k], L[k], nf, Nlow=nlow, tori=tori) for k in S}
    return dict(label=label, gamma=a["gamma"], width=a["width"], decay=a["decay"], alpha=a["alpha"],
                thr=(c["current"], b["v1"], v["v2"]), rho=(c["rho"], b["rho"], v["rho"]), L=L, S=S, nf=nf, tori=tori,
                norms=(b["M"], b["sK"], b["sB"], b["sT"]), c=b["c"], lam=b["lam"],
                cost={k: cost[k]["cpuh"]["P"] for k in S}, adv={k: cost[k]["advice_MB"] for k in S}, ell1=b["ell1"], v2p=b.get("v2+"))


def fmt(r):
    def ch(x):
        return "%.0f–%.0f" % (x[0], x[1]) if x[0] >= 10 else "%.1f–%.1f" % (x[0], x[1])
    return ("| %s | %.4f | %.3f, %.3f | %.2g | %.0f / %.1f / %.1f | %.0f / %.0f / %.0f | %.0f / %.0f / %.0f | %d | %s / %s / %s | %.0f / %.1f |"
            % (r["label"], r["gamma"], r["width"][0], r["width"][1], r["rho"][1], r["thr"][0], r["thr"][1], r["thr"][2], r["L"]["current"], r["L"]["v1"], r["L"]["v2"],
               r["S"]["current"], r["S"]["v1"], r["S"]["v2"], r["nf"], ch(r["cost"]["current"]), ch(r["cost"]["v1"]), ch(r["cost"]["v2"]), r["adv"]["current"], r["adv"]["v1"]))


HEAD = ("| candidate (per torus unless noted) | γ | width θ₁, θ₂ | ρ (v1) | log₁₀ threshold cur / v1 / v2 est. | digits L cur / v1 / v2 | support S cur / v1 / v2 | N_full | CPU-h tier P cur / v1 / v2 | advice MB cur / v1 |\n"
        "|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|")


def main():
    rows = []
    moon = load("moon_rot.json")
    for N in (40, 50, 60, 80, 100, 120):
        a = moon.get("moon N=%d lower" % N)
        if a and "best" in a:
            r = row("Moon rotational N=%d, band %.2f %%" % (N, 100 * a["pmax"]), a, NF["Moon rot"])
            rows.append(r)
    lib = load("moon_lib.json")
    for k, a in lib.items():
        if "best" in a:
            rows.append(row("Moon librational, amplitude %.1f°" % a["amp_deg"], a, NF["Moon lib"]))
    sp = load("spin_bodies.json")
    for k, a in sp.items():
        if "best" in a and "lower" in k:
            rows.append(row("%s, band %.4f (sep. %.4f)" % (k.replace(" lower", ""), a["pmax"], a["sep"]), a, NF["Mercury"]))
    rh = load("rhea_lib.json")
    for k, a in rh.items():
        if "best" in a:
            rows.append(row("Rhea librational, amplitude %.1f°" % a["amp_deg"], a, NF["Moon lib"]))
    ke = load("spin_kepler.json")
    for k, a in ke.items():
        if "best" in a:
            rows.append(row("%s, band %.4f" % (k.replace(" lower", ""), a["pmax"]), a, NF["Kepler"]))
    cc = load("cc07.json")
    for k, a in cc.items():
        if "best" in a:
            rows.append(row("CC07 truncated Victoria %s" % k, a, NF["CC07"]))
    for f in ("polar.json", "polar2.json"):
        po = load(f)
        for k, a in po.items():
            if "best" in a:
                rows.append(row("Exact PCR3BP %s" % k.replace("polar ", ""), a, NF["PCR3BP"]))
    tr = load("trojan.json")
    for k, a in tr.items():
        if "best" in a:
            rows.append(row(k, a, NF["Trojan"]))
    hi = load("hill.json")
    for k, a in hi.items():
        if "best" in a:
            rows.append(row(k, a, NF["Hill"]))
    to = load("tokamak.json")
    for k, d in to.items():
        for t, a in d.items():
            if "best" in a:
                rows.append(row("tokamak %s ε=%.5f" % (k, a["eps"]), a, NF["tokamak"]))
    out = [HEAD] + [fmt(r) for r in rows]
    txt = "\n".join(out)
    open(os.path.join(RES, "table.md"), "w").write(txt + "\n")
    json.dump(rows, open(os.path.join(RES, "table.json"), "w"), indent=1, default=float)
    print(txt)


if __name__ == "__main__":
    main()
