#!/usr/bin/env python3
"""HD11964 phase 2: the order-2 cover of the region R(d) modulo rotation, float64 (untrusted, Apache-2.0).

Region R(d) (design section 3, `HD11964.region`): Lam in [Lamlo - d, Lamhi + d], Gam_c + Gam_b <= Cbar + 2d = 0.012,
every angle.  Rotation (`KAM.Application.LambdaDrift.bracket_bound_of_rotation`): every chart state rotates to one
with eta_c = 0, xi_c >= 0 (planet c's eccentricity vector along +xi), so the cover needs only the representatives

    S_rep = {eta_c = 0, 0 <= xi_c <= sqrt(2 * 0.012)} x {(xi_b, eta_b): Gam_c + Gam_b <= 0.012} x Lam-box.

Cells are boxes |u_j| <= 1 in u = (x - centre)/h (the variables of `prod2.py`):
  - Lam_c, Lam_b: one cell each, centre Lamhat, radius rho + d (1.1e-3, 4.0e-3);
  - xi_c: intervals whose half-width follows the e-dependence of the Fourier decay,
    w(xi) = clamp(C_W sigma(e) / |d sigma/d xi|, W_MIN, W_MAX) (sigma the Kepler analyticity strip);
  - eta_c: radius H_ETA around 0 (the representatives have eta_c = 0);
  - (xi_b, eta_b): squares of half-width H_B tiling the disc Gam_b <= 0.012 - Gam_c(min of the interval).
The mode set S is global (|k_c| <= 80, |k_b| <= 20): the Lean F is one function on R(d).

Per cell (`prod2.Prod2` at the cell centre, base degree 5, grid from `gate.grid_for` with N1 >= 256, N2 >= 64):
the five terms' bounds a1..a5 (l1 of the degree <= 3 polynomial on the cell + remainder estimate), eta =
a1 + a2 + a3 + a4 + a5/2, sampled sups, the degree ratios of T4 and T5 (convergence check), the range of F_i - Lam_i
(sampled, and the l1 range bound), the direct rate at the centre and the identity check.  Summary: the worst cell,
the global eta_i and range, and the 10^3 yr rung (margin = d / max_i (eta_i T + hi_i - lo_i), T = 6741.9 units).

Usage: python3 -I cover2.py OUT.jsonl [--procs=2] [--plan-only] [--limit=N] [--hb=0.08]
       python3 -I cover2.py --summary OUT.jsonl SUMMARY.json
Run under the 8 GB cap (each process <= 3 GB).
"""
import json
import math
import multiprocessing as mpr
import os
import sys
import time

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import gate  # noqa: E402
import hd11964_model as HM  # noqa: E402

D_DRIFT, CBAR, RHO = 1e-3, 1e-2, (1e-4, 3e-3)
GMAX = CBAR + 2 * D_DRIFT
KC, KB = 80, 20
C_W, W_MIN, W_MAX = 0.15, 0.004, 0.03
H_ETA = 2e-3
H_B = float(next((x.split('=', 1)[1] for x in sys.argv if x.startswith('--hb=')), '0.08'))
YEARS_PER_UNIT = 0.1483262
T_UNITS = 1e3 / YEARS_PER_UNIT


def opt(name, default):
    return next((x.split("=", 1)[1] for x in sys.argv if x.startswith("--%s=" % name)), default)


def sigma(e):
    if e < 1e-9:
        return 50.0
    s = math.sqrt(1 - e * e)
    return math.log((1 + s) / e) - s


def ecc_of_xi(xi, L):
    G = xi * xi / 2
    return math.sqrt(max(0.0, 1 - (1 - G / L) ** 2))


def half_width(xi, L):
    """Target half-width in xi_c at xi (the e-dependence of the Fourier decay)."""
    e = ecc_of_xi(xi, L)
    if e < 0.2:
        return W_MAX
    dx = 1e-5
    ds = (sigma(ecc_of_xi(xi + dx, L)) - sigma(ecc_of_xi(xi - dx, L))) / (2 * dx)
    return min(W_MAX, max(W_MIN, C_W * sigma(e) / abs(ds)))


def plan(m):
    Lhat = [float(m.Lam(i)) for i in range(2)]
    hL = [RHO[0] + D_DRIFT, RHO[1] + D_DRIFT]
    Lmin = [Lhat[i] - hL[i] for i in range(2)]
    ximax = math.sqrt(2 * GMAX)
    # xi_c intervals, from 0 up: the half-width is the target at the interval's upper end (conservative)
    ivs, a = [], 0.0
    while a < ximax:
        w = W_MAX
        for _ in range(30):
            w = half_width(min(a + 2 * w, ximax), Lmin[0])
        b = min(a + 2 * w, ximax)
        ivs.append((a, b))
        a = b
    cells = []
    for (a, b) in ivs:
        xc, hx = (a + b) / 2, (b - a) / 2
        Rb = math.sqrt(max(0.0, 2 * GMAX - a * a))
        hb = min(H_B, max(Rb, 5e-3))
        n = max(1, int(math.ceil(Rb / hb - 1e-12)))
        for i in range(-n, n):
            for j in range(-n, n):
                cx, cy = (2 * i + 1) * hb, (2 * j + 1) * hb
                # keep the squares that meet the disc of radius Rb
                dxm = max(abs(cx) - hb, 0.0)
                dym = max(abs(cy) - hb, 0.0)
                if dxm * dxm + dym * dym > Rb * Rb:
                    continue
                if n == 1 and Rb <= hb:
                    cx = cy = 0.0
                cells.append(dict(Lam=Lhat, xi=[xc, cx], eta=[0.0, cy],
                                  h=[hL[0], hL[1], hx, H_ETA, hb, hb]))
        # a single square when the disc is smaller than one square
    # de-duplicate the n == 1 case (four squares collapsed to the centre)
    seen, out = set(), []
    for c in cells:
        key = (round(c["xi"][0], 12), round(c["xi"][1], 12), round(c["eta"][1], 12))
        if key in seen:
            continue
        seen.add(key)
        out.append(c)
    for k, c in enumerate(out):
        c["id"] = k
        x_hi = c["xi"][0] + c["h"][2]
        rb = math.hypot(abs(c["xi"][1]) + c["h"][4], abs(c["eta"][1]) + c["h"][5])
        c["emax"] = [ecc_of_xi(min(x_hi, 0.2), Lmin[0]), ecc_of_xi(min(rb, 0.2), Lmin[1])]
    return out, ivs


def run_cell(task):
    from prod2 import Prod2
    cell, nu, mu = task
    t0 = time.time()
    a = [(cell["Lam"][i] / nu[i]) ** 2 for i in range(2)]
    N1, N2 = gate.grid_for(cell["emax"][0], cell["emax"][1], a)
    N1, N2 = max(N1, 256), max(N2, 64)
    pr = Prod2(nu, mu, N1=N1, N2=N2, N=4, K1solve=KC, K2solve=KB)
    pr.setup(cell["Lam"], cell["xi"], cell["eta"])
    pr.run2()
    H = cell["h"]
    rng = np.random.default_rng(1000 + cell["id"])
    samples = [np.zeros(6)] + [np.array([(b >> j) & 1 for j in range(6)]) * 2.0 - 1.0 for b in range(64)]
    samples += list(rng.uniform(-1, 1, size=(40, 6)))
    direct = pr.residual(2)
    res = dict(id=cell["id"], cell=cell, grid=[N1, N2], planets={})
    for i, name in enumerate(("c", "b")):
        T, FmL = pr.terms[i]
        st = {k: pr.stats(v, samples, H) for k, v in T.items()}
        a5 = [st["T%d" % j]["a"] for j in range(1, 6)]
        rhs0 = -T["T1"].at0() - T["T2"].at0() + T["T3"].at0() + T["T4"].at0() - 0.5 * T["T5"].at0()
        rate, _ = direct[i]
        fs = pr.stats(FmL, samples, H)
        c0 = float(np.mean(FmL.c[0]))          # the angle average of the constant Taylor coefficient
        spread = fs["l1"] - abs(c0) + fs["rem"]
        q = {k: (st[k]["deg_l1"][3] / st[k]["deg_l1"][2] if st[k]["deg_l1"][2] > 0 else 0.0) for k in ("T4", "T5")}
        res["planets"][name] = dict(
            a=a5, eta=a5[0] + a5[1] + a5[2] + a5[3] + a5[4] / 2,
            sup_sampled=[st["T%d" % j]["sup_sampled"] for j in range(1, 6)],
            q=q, rate_centre=float(np.max(np.abs(rate))), identity_diff=float(np.max(np.abs(rate - rhs0))),
            FmL_sampled=[fs["min_sampled"], fs["max_sampled"]], FmL_bound=[c0 - spread, c0 + spread])
    res["seconds"] = time.time() - t0
    return res


def summary(path, out):
    rows = [json.loads(x) for x in open(path)]
    rows.sort(key=lambda r: r["id"])
    S = {}
    for p in ("c", "b"):
        eta = max(r["planets"][p]["eta"] for r in rows)
        worst = max(rows, key=lambda r: r["planets"][p]["eta"])
        lo = min(r["planets"][p]["FmL_bound"][0] for r in rows)
        hi = max(r["planets"][p]["FmL_bound"][1] for r in rows)
        los = min(r["planets"][p]["FmL_sampled"][0] for r in rows)
        his = max(r["planets"][p]["FmL_sampled"][1] for r in rows)
        qmax = max(max(r["planets"][p]["q"].values()) for r in rows)
        S[p] = dict(eta=eta, worst_cell=worst["id"], worst_centre=dict(xi=worst["cell"]["xi"], eta=worst["cell"]["eta"]),
                    FmL_bound=[lo, hi], FmL_sampled=[los, his], q_max=qmax,
                    rate_centre_max=max(r["planets"][p]["rate_centre"] for r in rows),
                    identity_diff_max=max(r["planets"][p]["identity_diff"] for r in rows))
    margin = D_DRIFT / max(S[p]["eta"] * T_UNITS + S[p]["FmL_bound"][1] - S[p]["FmL_bound"][0] for p in S)
    margin_s = D_DRIFT / max(S[p]["eta"] * T_UNITS + S[p]["FmL_sampled"][1] - S[p]["FmL_sampled"][0] for p in S)
    per_cell = []
    for r in rows:
        mc = D_DRIFT / max(r["planets"][p]["eta"] * T_UNITS + S[p]["FmL_bound"][1] - S[p]["FmL_bound"][0]
                           for p in S)
        per_cell.append(dict(
            id=r["id"], xi=[round(x, 6) for x in r["cell"]["xi"]], eta=[round(x, 6) for x in r["cell"]["eta"]],
            h=[float("%.4g" % x) for x in r["cell"]["h"]], emax=[round(x, 4) for x in r["cell"]["emax"]],
            grid=r["grid"], seconds=round(r["seconds"], 1),
            **{p: dict(a=[float("%.3g" % x) for x in r["planets"][p]["a"]],
                       eta=float("%.3g" % r["planets"][p]["eta"]),
                       FmL=[float("%.3g" % x) for x in r["planets"][p]["FmL_bound"]],
                       q=[round(r["planets"][p]["q"]["T4"], 3), round(r["planets"][p]["q"]["T5"], 3)])
               for p in ("c", "b")},
            margin=round(mc, 2)))
    res = dict(cells=len(rows), T_units=T_UNITS, d=D_DRIFT, S=dict(Kc=KC, Kb=KB), planets=S,
               rung_1e3=dict(margin_bound=margin, margin_sampled_range=margin_s, closes=margin >= 2,
                             min_cell_margin=min(c["margin"] for c in per_cell)),
               cpu_seconds=sum(r["seconds"] for r in rows), per_cell=per_cell)
    with open(out, "w") as fh:
        json.dump(res, fh, indent=1)
    print(json.dumps({k: v for k, v in res.items() if k != "per_cell"}, indent=1))


def main():
    if "--summary" in sys.argv:
        args = [x for x in sys.argv[1:] if not x.startswith("--")]
        summary(args[0], args[1])
        return
    out = sys.argv[1]
    m = HM.Model()
    nu = [float(HM.R(x)) for x in m.nu]
    mu = float(HM.R(m.mu))
    cells, ivs = plan(m)
    print("xi_c intervals:", len(ivs), [(round(a, 4), round(b, 4)) for a, b in ivs], flush=True)
    print("cells:", len(cells), flush=True)
    if "--plan-only" in sys.argv:
        return
    done = set()
    if os.path.exists(out):
        done = {json.loads(x)["id"] for x in open(out)}
    todo = [c for c in cells if c["id"] not in done]
    lim = int(opt("limit", "0"))
    if lim:
        todo = todo[:lim]
    todo.sort(key=lambda c: -c["emax"][0])
    procs = int(opt("procs", "2"))
    t0 = time.time()
    with mpr.get_context("fork").Pool(procs, maxtasksperchild=1) as pool, open(out, "a") as fh:
        for r in pool.imap_unordered(run_cell, [(c, nu, mu) for c in todo]):
            fh.write(json.dumps(r) + "\n")
            fh.flush()
            pc, pb = r["planets"]["c"], r["planets"]["b"]
            print("cell %3d xi=(%.4f, %.3f) eta_b=%.3f grid %s %5.1fs  eta_c %.2e eta_b %.2e  q_c %.2f %.2f" % (
                r["id"], r["cell"]["xi"][0], r["cell"]["xi"][1], r["cell"]["eta"][1], r["grid"], r["seconds"],
                pc["eta"], pb["eta"], pc["q"]["T4"], pc["q"]["T5"]), flush=True)
    print("total %.0fs" % (time.time() - t0))


if __name__ == "__main__":
    main()
