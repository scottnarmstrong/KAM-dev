#!/usr/bin/env python3
"""SJS-PLAN item 1: the majorants in FH's own normalization, per chart, and the sensitivity of route B to the enclosure ratio SAFE.
Usage: python3 -I scripts/sjs/plan/sjs_plan_sens.py TORUS.npz [--json OUT]"""
import json, math, os, sys
import numpy as np
args = sys.argv[1:]
sys.argv = sys.argv[:1]
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import sjs_plan_thresholds as P
import sjs_chart as CH
import sjs_torus as ST
sys.path.pop(0)


def raw(Tn):
    """sup |X|, |DX|, |D^2 X|: 2 pi angles, unit prefactor, max norm and row sums (FH's c_Xh, c_DXh, c_D2Xh)"""
    a1 = np.abs(Tn["D1"]); a2 = np.abs(Tn["D2"]); a3 = np.abs(Tn["D3"])
    return float(a1.max()), float(a2.sum(axis=1).max()), float(a3.sum(axis=(1, 2)).max())


def main():
    d = np.load(args[0])
    u = d["u"]
    out = dict(raw={}, sens=[])
    print("| chart | rho | domain | c_Xh | c_DXh | c_D2Xh |")
    print("|---|---:|---|---:|---:|---:|")
    print("| FH25 (published) | 0.10 | their tube | 0.09 | 129 | 5e10 |")
    for chart in ("del", "reg", "syn"):
        Pm, Fm, phi, gr = CH.periodic_data(u, chart)
        for rho in (0.02, 0.1):
            for dom, (pts) in (("tube", CH.tube_points(Pm, Fm, gr, rho, 1e-3, 1e-5, 8000)), ("box", CH.box_points(Pm, Fm, gr, rho, 1e-3, 1e-5, 8000)[0])):
                r = raw(CH.tensors(chart, pts, phi))
                out["raw"]["%s/%g/%s" % (chart, rho, dom)] = r
                print("| %s | %.2f | %s | %.3g | %.3g | %.3g |" % (chart, rho, dom, *r), flush=True)
    chart, rho, ell, c, mu = "syn", 0.02, 0.1, 3000.0, 1e-4
    Pm, Fm, phi, gr = CH.periodic_data(u, chart)
    new = (64, 64, 64)
    Pc = P.crop(Pm, new)
    gr_c = ST.Grid(new)
    pts, info = CH.box_points(Pm, Fm, gr, rho, 1e-3, 1e-5, 4000)
    tn = CH.tensors(chart, pts, phi)
    t1 = CH.torsion_grid(chart, Pm, Fm, phi, gr, step=2, c=c, ell=ell)
    geo = CH.frames_on_strip(Pc, Fm, gr_c, rho, ell)
    om_t = c * (Fm @ P.OM) / P.TP
    tor = dict(tinv=t1["tinv_iso"], Tsup=t1["Tsup"], Th=t1["Th"])
    print("\nsensitivity, synodic chart, iso, certified gamma, rho 0.02, ell 0.1, c 3000")
    print("| enclosure / sample | route B log T | raw |")
    print("|---:|---:|---:|")
    for safe in (1.0, 2.0, 20.0, 200.0, 2000.0):
        Mx = {k: v * safe for k, v in CH.majorants(tn, c, ell).items()}
        Mx["Th"] = t1["Th"] * safe
        D = P.package(geo, tor, Mx, rho / P.TP, mu, c, ell, P.GAMMAS["cert8"], om_t)
        le, why = P.route_b(D, iso=True)
        out["sens"].append((safe, le))
        print("| %g | %.2f | %.2f | %s" % (safe, le, le + math.log10(P.TP / c), why), flush=True)
    if len(args) > 2:
        json.dump(out, open(args[2], "w"), indent=1)


if __name__ == "__main__":
    main()
