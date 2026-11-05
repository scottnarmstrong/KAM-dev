#!/usr/bin/env python3
"""HD11964 phase 2 (CELLS): the order-2 cover of R(d) with b-cells fitted to the region, float64 (untrusted,
Apache-2.0).

`cover2.py` covers planet b's disc {Gam_b <= Cmax - Gam_c} by axis squares that only have to meet it; their far corners
reach outside R(d), and the F_b - Lam_b range bound grows with them.  The l1 bound of a cell behaves like
k (|centre_b| + h_1 + h_2) (k ~ 1.7e-3 at d = 2e-3): the oscillation of Lam_b is linear in (xi_b, eta_b), and the l1 norm
adds the two half-widths.  Here the b-disc of each xi_c interval [a, b] (radius R = sqrt(2 Cmax - a^2)) is cut into
  - rings rho in [rho_in, rho_out] of n annular sectors (a wedge when rho_in = 0), each carried by the smallest box
    in its own radial/tangential frame: radial [rho_in cos al, rho_out], tangential +-rho_out sin al (al = pi/n);
    its effective radius is rho_out (1 + sin al);
  - or one square at the origin when the disc is small (effective radius 2R).
Every cell is an affine box w = centre + M u, |u|_inf <= 1, with M diagonal except a rotation in (xi_b, eta_b).  n and
the rings are chosen so that every cell's effective radius is at most rho* = R_max (1 + kappa) (R_max the disc radius at
xi_c = 0), with half-widths <= hmax (the Taylor convergence range of the h_b = 0.08 cover).

Per cell: the producer of `cover2.run_cell` (same S, grid rule, degree) at the cell centre; the jets of the five terms
and of F - Lam are rotated into the cell frame (x_b = cos phi r - sin phi t, y_b = sin phi r + cos phi t, exact
linear substitution) before the l1 bounds.  Also the sampled range of F - Lam over the box and over box points inside
R(d).

Usage: python3 -I cover2_fit.py OUT.jsonl --d=2e-3 [--kappa=0.2] [--hmax=0.085] [--nmult=1] [--procs=2] [--xic=X]
       [--plan-only]
       python3 -I cover2_fit.py --summary OUT.jsonl SUMMARY.json --d=2e-3
Run under the 8 GB cap (each process <= 3.5 GB).
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

KAPPA = float(C.opt("kappa", "0.2"))
HMAX = float(C.opt("hmax", "0.085"))
NMULT = int(C.opt("nmult", "1"))       # sector counts restricted to multiples of NMULT (4: quadrant split)


def ring(rho_in, rho_out, rho_star):
    """The fewest sectors n of the ring with rho_out (1 + sin(pi/n)) <= rho_star and box half-widths <= HMAX."""
    for n in range(3, 400):
        if n % NMULT:
            continue
        al = math.pi / n
        hr = (rho_out - rho_in * math.cos(al)) / 2
        ht = rho_out * math.sin(al)
        if rho_out * (1 + math.sin(al)) <= rho_star * (1 + 1e-12) and hr <= HMAX and ht <= HMAX:
            return n, al, hr, ht
    return None


def b_cells(R, rho_star):
    """Cells covering the disc of radius R: list of dict(phi, rc, h=(h_r, h_t), sector=(rho_in, rho_out, al))."""
    best = None
    if 2 * R <= rho_star and R <= HMAX:
        best = [dict(phi=0.0, rc=0.0, h=(R, R), sector=None, kind="square")]
    # rings: try the split radii on a grid, at most 3 rings, keep the fewest cells
    for k in range(1, 4):
        for frac in np.linspace(0.3, 0.95, 27) if k > 1 else [1.0]:
            radii = [0.0]
            ok = True
            for j in range(1, k):
                radii.append(R * frac ** (k - j))
            radii.append(R)
            cells = []
            for r0, r1 in zip(radii[:-1], radii[1:]):
                g = ring(r0, r1, rho_star)
                if g is None:
                    ok = False
                    break
                n, al, hr, ht = g
                rc = (r1 + r0 * math.cos(al)) / 2
                for j in range(n):
                    cells.append(dict(phi=2 * math.pi * (j + 0.5) / n, rc=rc, h=(hr, ht), sector=(r0, r1, al),
                                      kind="wedge" if r0 == 0 else "sector"))
            if ok and (best is None or len(cells) < len(best)):
                best = cells
    return best


def plan(m):
    _, ivs = C.plan(m)
    Lhat = [float(m.Lam(i)) for i in range(2)]
    hL = [C.RHO[0] + C.D_DRIFT, C.RHO[1] + C.D_DRIFT]
    Lmin = [Lhat[i] - hL[i] for i in range(2)]
    rmax = math.sqrt(2 * C.GMAX)
    rho_star = rmax * (1 + KAPPA)
    cells = []
    for (a, b) in ivs:
        xc, hx = (a + b) / 2, (b - a) / 2
        R = math.sqrt(max(0.0, 2 * C.GMAX - a * a))
        for bc in b_cells(R, rho_star):
            cx, cy = bc["rc"] * math.cos(bc["phi"]), bc["rc"] * math.sin(bc["phi"])
            corner = math.hypot(bc["rc"] + bc["h"][0], bc["h"][1])
            cells.append(dict(Lam=Lhat, xi=[xc, cx], eta=[0.0, cy], phi=bc["phi"], kind=bc["kind"],
                              sector=bc["sector"], R=R, h=[hL[0], hL[1], hx, C.H_ETA, bc["h"][0], bc["h"][1]],
                              emax=[C.ecc_of_xi(min(b, 0.2), Lmin[0]), C.ecc_of_xi(min(corner, 0.2), Lmin[1])],
                              reff=bc["rc"] + bc["h"][0] + bc["h"][1]))
    for k, c in enumerate(cells):
        c["id"] = k
    return cells, ivs, rho_star


_ROT = {}


def rot_matrix(S6, deg, phi):
    """L with p(x) = q(y): coefficients of q = L @ coefficients of p, x_b = c r - s t, y_b = s r + c t."""
    key = (deg, round(phi, 15))
    if key in _ROT:
        return _ROT[key]
    c, s = math.cos(phi), math.sin(phi)
    M = S6.M(deg)
    L = np.zeros((M, M))
    for i, mon in enumerate(S6.mons[:M]):
        poly = {(0, 0): 1.0}
        for fac in [((1, 0), c, (0, 1), -s)] * mon[4] + [((1, 0), s, (0, 1), c)] * mon[5]:
            new = {}
            for (p, q), v in poly.items():
                new[(p + 1, q)] = new.get((p + 1, q), 0.0) + v * fac[1]
                new[(p, q + 1)] = new.get((p, q + 1), 0.0) + v * fac[3]
            poly = new
        for (p, q), v in poly.items():
            e = list(mon)
            e[4], e[5] = p, q
            L[S6.idx[tuple(e)], i] += v
    _ROT[key] = L
    return L


def rotate(J, phi):
    from jets import Jet
    if phi == 0.0:
        return J
    L = rot_matrix(J.S, J.deg, phi)
    sh = J.c.shape
    return Jet(J.S, (L @ J.c.reshape(sh[0], -1)).reshape(sh), J.deg)


def run_cell(task):
    from prod2 import Prod2
    cell, nu, mu = task
    t0 = time.time()
    a = [(cell["Lam"][i] / nu[i]) ** 2 for i in range(2)]
    N1, N2 = C.gate.grid_for(cell["emax"][0], cell["emax"][1], a)
    N1, N2 = max(N1, 256), max(N2, 64)
    pr = Prod2(nu, mu, N1=N1, N2=N2, N=4, K1solve=C.KC, K2solve=C.KB)
    pr.setup(cell["Lam"], cell["xi"], cell["eta"])
    pr.run2()
    H = cell["h"]
    rng = np.random.default_rng(1000 + cell["id"])
    samples = [np.zeros(6)] + [np.array([(b >> j) & 1 for j in range(6)]) * 2.0 - 1.0 for b in range(64)]
    samples += list(rng.uniform(-1, 1, size=(40, 6)))
    # box points inside R(d), in the cell frame (u-coordinates)
    cph, sph = math.cos(cell["phi"]), math.sin(cell["phi"])
    inside = []
    for u in rng.uniform(-1, 1, size=(600, 6)):
        x = u * np.asarray(H)
        xc, yc = cell["xi"][0] + x[2], x[3]
        xb = cell["xi"][1] + cph * x[4] - sph * x[5]
        yb = cell["eta"][1] + sph * x[4] + cph * x[5]
        if (xc * xc + yc * yc + xb * xb + yb * yb) / 2 <= C.GMAX:
            inside.append(u)
    direct = pr.residual(2)
    res = dict(id=cell["id"], cell=cell, grid=[N1, N2], planets={})
    for i, name in enumerate(("c", "b")):
        T, FmL = pr.terms[i]
        st = {k: pr.stats(rotate(v, cell["phi"]), samples, H) for k, v in T.items()}
        a5 = [st["T%d" % j]["a"] for j in range(1, 6)]
        rhs0 = -T["T1"].at0() - T["T2"].at0() + T["T3"].at0() + T["T4"].at0() - 0.5 * T["T5"].at0()
        rate, _ = direct[i]
        FmLr = rotate(FmL, cell["phi"])
        fs = pr.stats(FmLr, samples, H)
        fin = pr.stats(FmLr, inside, H) if inside else None
        c0 = float(np.mean(FmLr.c[0]))
        spread = fs["l1"] - abs(c0) + fs["rem"]
        q = {k: (st[k]["deg_l1"][3] / st[k]["deg_l1"][2] if st[k]["deg_l1"][2] > 0 else 0.0) for k in ("T4", "T5")}
        res["planets"][name] = dict(
            a=a5, eta=a5[0] + a5[1] + a5[2] + a5[3] + a5[4] / 2,
            sup_sampled=[st["T%d" % j]["sup_sampled"] for j in range(1, 6)],
            q=q, rate_centre=float(np.max(np.abs(rate))), identity_diff=float(np.max(np.abs(rate - rhs0))),
            FmL_sampled=[fs["min_sampled"], fs["max_sampled"]], FmL_bound=[c0 - spread, c0 + spread],
            FmL_region_sampled=[fin["min_sampled"], fin["max_sampled"]] if fin else None, n_region=len(inside))
    res["seconds"] = time.time() - t0
    return res


def main():
    if "--summary" in sys.argv:
        args = [x for x in sys.argv[1:] if not x.startswith("--")]
        C.summary(args[0], args[1])
        s = json.load(open(args[1]))
        rows = [json.loads(x) for x in open(args[0])]
        for p in ("c", "b"):
            rr = [r["planets"][p]["FmL_region_sampled"] for r in rows if r["planets"][p]["FmL_region_sampled"]]
            s["planets"][p]["FmL_region_sampled"] = [min(x[0] for x in rr), max(x[1] for x in rr)]
        kinds = {}
        for r in rows:
            kinds[r["cell"]["kind"]] = kinds.get(r["cell"]["kind"], 0) + 1
        s["fit"] = dict(kappa=KAPPA, hmax=HMAX, nmult=NMULT, rho_star=math.sqrt(2 * C.GMAX) * (1 + KAPPA), kinds=kinds,
                        reff_max=max(r["cell"]["reff"] for r in rows))
        for c, r in zip(s["per_cell"], sorted(rows, key=lambda r: r["id"])):
            c.update(phi=round(r["cell"]["phi"], 6), kind=r["cell"]["kind"], reff=round(r["cell"]["reff"], 4))
        with open(args[1], "w") as fh:
            json.dump(s, fh, indent=1)
        print(json.dumps(dict(fit=s["fit"], region_sampled={p: s["planets"][p]["FmL_region_sampled"]
                                                            for p in ("c", "b")}), indent=1))
        return
    out = sys.argv[1]
    m = HM.Model()
    nu = [float(HM.R(x)) for x in m.nu]
    mu = float(HM.R(m.mu))
    cells, ivs, rho_star = plan(m)
    xic = C.opt("xic", None)
    if xic is not None:
        cells = [c for c in cells if abs(c["xi"][0] - float(xic)) < 1e-6]
    print("d", C.D_DRIFT, "kappa", KAPPA, "rho*", round(rho_star, 4), "cells", len(cells), flush=True)
    for (a, b) in ivs:
        cs = [c for c in cells if abs(c["xi"][0] - (a + b) / 2) < 1e-9]
        if cs:
            kinds = {}
            for c in cs:
                kinds[(c["kind"], round(c["sector"][1], 3) if c["sector"] else None)] = \
                    kinds.get((c["kind"], round(c["sector"][1], 3) if c["sector"] else None), 0) + 1
            print("  xi_c [%.4f, %.4f] R %.4f cells %d reff<=%.4f %s" % (
                a, b, cs[0]["R"], len(cs), max(c["reff"] for c in cs), kinds), flush=True)
    if "--plan-only" in sys.argv:
        return
    done = set()
    if os.path.exists(out):
        done = {json.loads(x)["id"] for x in open(out)}
    todo = sorted([c for c in cells if c["id"] not in done], key=lambda c: -c["emax"][0])
    t0 = time.time()
    with mpr.get_context("fork").Pool(int(C.opt("procs", "2")), maxtasksperchild=1) as pool, open(out, "a") as fh:
        for r in pool.imap_unordered(run_cell, [(c, nu, mu) for c in todo]):
            fh.write(json.dumps(r) + "\n")
            fh.flush()
            pc, pb = r["planets"]["c"], r["planets"]["b"]
            print("cell %3d %-6s xi_c %.4f phi %6.3f rc %.3f h %.3f %.3f grid %s %5.1fs eta_c %.2e eta_b %.2e "
                  "FmL_b +-%.3g region %s q_c %.2f" % (
                      r["id"], r["cell"]["kind"], r["cell"]["xi"][0], r["cell"]["phi"], r["cell"]["reff"]
                      - r["cell"]["h"][4] - r["cell"]["h"][5], r["cell"]["h"][4], r["cell"]["h"][5], r["grid"],
                      r["seconds"], pc["eta"], pb["eta"], (pb["FmL_bound"][1] - pb["FmL_bound"][0]) / 2,
                      pb["FmL_region_sampled"], max(pc["q"].values())), flush=True)
    print("total %.0fs" % (time.time() - t0))


if __name__ == "__main__":
    main()
