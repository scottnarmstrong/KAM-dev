#!/usr/bin/env python3
"""V2-SITES-SIGN: LG00 T' at each dry run, with classical and certified sites, in exact rationals.

Untrusted tooling.  For every dry run docs/campaign/studies/v2-sites-data/dry_tp_L*.json: the err of that L, the largest
X* of the exact route-A mirror (v2_r2.max_Xs), the margin e*/err, and the whole numerical test `refinedCore` of the mirror
at a concrete witness (X* = 2 err/scale, three digits up; disp the exact minimum, rounded up), for kp = 3 and 4.  The sites
are the certified constants of sites_tp.json (bite_sign.py), whose witnesses `biteOk` accepts in the kernel.

Usage: python3 -B -I scripts/certifier/lg00_margins.py [--json OUT]
"""
import glob, json, math, os, sys
from fractions import Fraction as F

sys.dont_write_bytecode = True
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(ROOT, "scripts", "apost_sharp"))
sys.path.insert(0, os.path.join(ROOT, "scripts", "spin_orbit"))
import lg00_sites as LS            # noqa: E402
import structured_b as SB          # noqa: E402
import v2_r2 as VR                 # noqa: E402
import v2_q as V                   # noqa: E402

DATA = os.path.join(ROOT, "docs/campaign/studies/v2-sites-data")
TH, J = F(1, 8), 20


def one(pkg, sites, name, KP):
    p, box, R = pkg["p"], pkg["box"], pkg["R"]
    d0 = min(F(1), (p["rho"] - p["rhoInf"]) / 6)
    sc = p["gamma"] ** 4 * d0 ** 4
    g2r2 = p["gamma"] ** 2 * p["rho"] ** 2
    err = p["err"]
    Xmax = VR.max_Xs("refined", p, box, KP, TH, J, R, sites)
    e = Xmax * sc
    out = dict(sites=name, log10_e=VR.lg(e), margin=float(e / err))
    Xs = V.up(float(2 * err / sc), 3)
    if Xs > Xmax:
        return dict(out, core=False, why="2 err above the threshold")
    ok, why, w = VR.okB_at("refined", p, box, KP, TH, J, Xs, R, sites, detail=True)
    Q = V.refined_num(w, 2, p, box)
    C = V.disp_coefs(Q, 2, p, Xs, False)[0]
    disp = V.up(float(C * err / g2r2) * (1 + 1e-9), 3)
    while C * err > disp * g2r2:
        disp = V.up(float(disp) * 1.001, 3)
    fin = V.refinedCore(2, dict(p, disp=disp), box, dict(w), detail=True)
    return dict(out, Xs=str(Xs), disp=float(disp), core=fin[0], parts=fin[1])


def main():
    d = json.load(open(os.path.join(DATA, "sites_tp.json")))
    cert = {(k[0], int(k[1])): F(v["c"]) for k, v in d["sites"].items()}
    cut = lambda kp: {k: v for k, v in cert.items() if k[1] < kp}
    res = {}
    for path in sorted(glob.glob(os.path.join(DATA, "dry_tp_L*.json"))):
        rep = json.load(open(path))
        pkg = LS.package(path)
        clas = SB.classical_sites(pkg["p"], 3)
        L = rep["L"]
        row = dict(L=L, support=rep["support"], err=float(F(rep["params"]["err"])), slots=rep["jet_slots"],
                   checks={k: v.get("ok") for k, v in rep["checks"].items() if k != "sharpTest"})
        row["classical"] = one(pkg, clas, "classical", 3)
        row["certified kp 3"] = one(pkg, cut(3), "certified kp 3", 3)
        row["certified kp 4"] = one(pkg, cut(4), "certified kp 4", 4)
        res[L] = row
        print("L=%d support %d err %.3g landed checks %s" % (L, row["support"], row["err"], all(row["checks"].values())))
        for k in ("classical", "certified kp 3", "certified kp 4"):
            r = row[k]
            print("   %-14s log10 e* %8.3f  margin %10.1f  X* %s  disp %s  refinedCore %s" % (
                k, r["log10_e"], r["margin"], r.get("Xs"), r.get("disp"), r.get("core")), flush=True)
    if "--json" in sys.argv:
        json.dump(res, open(sys.argv[sys.argv.index("--json") + 1], "w"), indent=1, default=str)
    return 0


if __name__ == "__main__":
    sys.exit(main())
