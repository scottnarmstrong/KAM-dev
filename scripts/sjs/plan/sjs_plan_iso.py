#!/usr/bin/env python3
"""SJS-PLAN item 1: the isoenergetic form (the form the v2 certifier checks) at chosen chart points of sjs_plan_thresholds.py.
Usage: python3 -I scripts/sjs/plan/sjs_plan_iso.py TORUS.npz chart rho ell c mu [gamma-name ...]"""
import json, math, sys
import numpy as np
from fractions import Fraction as F
args = sys.argv[1:]
sys.argv = sys.argv[:1]
import os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import sjs_plan_thresholds as P
import sjs_chart as CH
import sjs_torus as ST
sys.path.pop(0)


def main():
    d = np.load(args[0])
    chart = args[1]
    rho, ell, c, mu = [float(x) for x in args[2:6]]
    u = d["u"]
    Pm, Fm, phi, gr = CH.periodic_data(u, chart)
    new = (64, 64, 64)
    Pc = P.crop(Pm, new)
    gr_c = ST.Grid(new)
    pts, info = CH.box_points(Pm, Fm, gr, rho, 1e-3, 1e-5, 4000)
    tn = CH.tensors(chart, pts, phi)
    t1 = CH.torsion_grid(chart, Pm, Fm, phi, gr, step=2, c=c, ell=ell)
    geo = CH.frames_on_strip(Pc, Fm, gr_c, rho, ell)
    Mx = {k: v * P.SAFE for k, v in CH.majorants(tn, c, ell).items()}
    Mx["Th"] = t1["Th"] * P.SAFE
    om_t = c * (Fm @ P.OM) / P.TP
    for gname, gam in P.GAMMAS.items():
        for iso in (False, True):
            tor = dict(tinv=t1["tinv_iso"] if iso else t1["tinv"], Tsup=t1["Tsup"], Th=t1["Th"])
            D = P.package(geo, tor, Mx, rho / P.TP, mu, c, ell, gam, om_t)
            le, why = P.route_b(D, iso=iso)
            print("%s %s rho %.3f ell %.3g c %.3g mu %.0e %s: tinv %.3g, route B %.2f (raw %.2f) %s" % (
                chart, gname, rho, ell, c, mu, "iso" if iso else "fixed", tor["tinv"], le, le + math.log10(P.TP / c), why), flush=True)


if __name__ == "__main__":
    main()
