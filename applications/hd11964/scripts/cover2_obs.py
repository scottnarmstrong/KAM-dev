#!/usr/bin/env python3
"""HD11964 (REDMASS-MARGIN): the observable bridge's cell data on the fitted cover, float64 (untrusted, Apache-2.0).

The observable bridge (`KAM.Application.LambdaDrift.stoppedDrift_of_approxIntegrals_obs`, Lean instance
`HD11964.noCrossing_of_regionBounds_obs_analytic`) drives the first exit by the reduced Delaunay actions

    G_i = keplerAction (redMass nu mu) (Psi w) i,   redMass nu mu i = nu_i / sqrt(1 + mu nu_i),

and needs, on the region R(d + eps) (`HD11964.region`), the bracket bound |{F_i, H}| <= eta_i and the range
lo_i <= F_i - G_i <= hi_i, with eta_i T + (hi_i - lo_i) < d and d + eps <= r/2.  eps bounds the range of G_i - Lam_i on
R(r) (analytically: `HD11964.reducedAction_sub_mem_region`, widths 1.4e-5 (c) and 2.73e-4 (b), so eps = 2.73e-4).

F is the Lean F of `prod2.Prod2` (unchanged: the order-2 approximate integrals of the original H).  Per cell of
`cover2_fit`'s plan this script runs `cover2_fit.run_cell`'s producer (same S, grid, degree, samples and frame rotation)
and adds the jet of G_i - Lam_i, computed from the chart jets of q_i, p_i (`normal_form.chart_planet`) with the frozen
definitions at nu' = redMass nu mu:

    E' = |p|^2/(2 nu') - nu'/|q|,   a' = -nu'/(2 E'),   G = nu' sqrt(a').

Then F_i - G_i = (F_i - Lam_i) - (G_i - Lam_i) gets the same l1 range bound as F_i - Lam_i in `cover2.summary`
([c0 - spread, c0 + spread], c0 the angle average of the constant coefficient, spread = l1 - |c0| + remainder).

Checks per cell: the heliocentric action of the chart jets equals Lam (every coefficient); G - Lam against the closed
form Lam (1/sqrt((1 + k)(1 - k (2a/r - 1))) - 1), k = mu nu (`keplerAction_redMass_eq_div_sqrt`), on the grid at the
centre; the sampled G - Lam inside the analytic bounds loGan, hiGan.

Region parameter: --d is the region's d (as in cover2), i.e. d + eps.  With d + eps = r/2 = 2e-3 the region is R(2e-3)
and the plan is exactly `cover2_fit`'s 50-cell kappa = 0.2 cover; the summary reports the margin at d = r/2 - eps, and
`horizon_years_bound`, the longest time with margin >= 1, 2 (eta and the ranges on the region do not depend on T).

Usage: python3 -I cover2_obs.py OUT.jsonl --d=2e-3 [--kappa=0.2] [--procs=2] [--limit=N] [--xic=X] [--plan-only]
       python3 -I cover2_obs.py --summary OUT.jsonl SUMMARY.json --d=2e-3 [--eps=2.73e-4] [--base=BASE.jsonl]
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
import cover2_fit as CF  # noqa: E402
import hd11964_model as HM  # noqa: E402

EPS = float(C.opt("eps", "2.73e-4"))
R_TUBE = 4e-3                                   # HD11964.rTube = 1/250
LO_GAN = (-2e-6, -117e-6)                       # HD11964.loGan
HI_GAN = (12e-6, 156e-6)                        # HD11964.hiGan


def reduced_minus_lam(pr, i, H):
    """Jets (S3, planet i's grid) of G_i - Lam_i, and of keplerAction(nu)(chart) - Lam_i (the chart check, its
    coefficients normalised by h^m on the cell, h = (h_Lam_i, h_xi_i, h_eta_i); planet b's two slow half-widths are
    replaced by their max, since the check runs before the frame rotation)."""
    from jets import Jet
    from normal_form import chart_planet
    nu, mu = float(pr.nu[i]), float(pr.mu)
    lg = pr.lam1 if i == 0 else pr.lam2
    q, p = chart_planet(pr.S3, nu, lg, pr.Lam0[i], pr.xi0[i], pr.eta0[i], 0, 1, 2)
    P2 = p[0] * p[0] + p[1] * p[1]
    rinv = (q[0] * q[0] + q[1] * q[1]).sqrt().recip()

    def action(m):
        E = P2.scale(1.0 / (2 * m)) - rinv.scale(m)
        return E.recip().scale(-m / 2).sqrt().scale(m)

    Lam = Jet.var(pr.S3, 0, pr.Lam0[i], lg.shape)
    nup = nu / math.sqrt(1 + mu * nu)
    GmL = action(nup) - Lam
    hs = (H[0], H[2], H[3]) if i == 0 else (H[1], max(H[4], H[5]), max(H[4], H[5]))
    hp = np.array([hs[0] ** m[0] * hs[1] ** m[1] * hs[2] ** m[2] for m in pr.S3.mons[: pr.S3.M(pr.S3.D)]])
    err = (action(nu) - Lam).c
    chart_err = float(np.max(np.abs(err) * hp.reshape((-1,) + (1,) * (err.ndim - 1))))
    # closed form at the centre: G = Lam / sqrt((1 + k)(1 - k (2a/r - 1))), a = Lam^2/nu^2
    k = mu * nu
    a = float(pr.Lam0[i]) ** 2 / nu ** 2
    r = 1.0 / rinv.at0()
    X = (1 + k) * (1 - k * (2 * a / r - 1))
    closed = float(pr.Lam0[i]) * (1 / np.sqrt(X) - 1)
    closed_err = float(np.max(np.abs(GmL.at0() - closed)))
    return GmL, chart_err, closed_err


def run_cell(task):
    from jets import embed
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
    # the samples of cover2_fit.run_cell, in the same order (same seed)
    rng = np.random.default_rng(1000 + cell["id"])
    samples = [np.zeros(6)] + [np.array([(b >> j) & 1 for j in range(6)]) * 2.0 - 1.0 for b in range(64)]
    samples += list(rng.uniform(-1, 1, size=(40, 6)))
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

    def rng_of(J):
        Jr = CF.rotate(J, cell["phi"])
        fs = pr.stats(Jr, samples, H)
        fin = pr.stats(Jr, inside, H) if inside else None
        c0 = float(np.mean(Jr.c[0]))
        spread = fs["l1"] - abs(c0) + fs["rem"]
        return dict(bound=[c0 - spread, c0 + spread], sampled=[fs["min_sampled"], fs["max_sampled"]],
                    region_sampled=[fin["min_sampled"], fin["max_sampled"]] if fin else None,
                    l1=fs["l1"], rem=fs["rem"], c0=c0, deg_l1=fs["deg_l1"])

    for i, name in enumerate(("c", "b")):
        T, FmL = pr.terms[i]
        st = {k: pr.stats(CF.rotate(v, cell["phi"]), samples, H) for k, v in T.items()}
        a5 = [st["T%d" % j]["a"] for j in range(1, 6)]
        rhs0 = -T["T1"].at0() - T["T2"].at0() + T["T3"].at0() + T["T4"].at0() - 0.5 * T["T5"].at0()
        rate, _ = direct[i]
        q = {k: (st[k]["deg_l1"][3] / st[k]["deg_l1"][2] if st[k]["deg_l1"][2] > 0 else 0.0) for k in ("T4", "T5")}
        g3, chart_err, closed_err = reduced_minus_lam(pr, i, H)
        GmL = embed(g3, pr.S6, [i, 2 + 2 * i, 3 + 2 * i], (i,), pr.grid)
        FmG = FmL - GmL
        rL, rG, rFG = rng_of(FmL), rng_of(GmL), rng_of(FmG)
        res["planets"][name] = dict(
            a=a5, eta=a5[0] + a5[1] + a5[2] + a5[3] + a5[4] / 2, q=q,
            rate_centre=float(np.max(np.abs(rate))), identity_diff=float(np.max(np.abs(rate - rhs0))),
            FmL=rL, GmL=rG, FmG=rFG, deg=dict(FmL=FmL.deg, GmL=GmL.deg, FmG=FmG.deg),
            checks=dict(chart_action_err=chart_err, closed_form_err=closed_err,
                        GmL_in_analytic=bool(LO_GAN[i] <= rG["sampled"][0] and rG["sampled"][1] <= HI_GAN[i])),
            n_region=len(inside))
    res["seconds"] = time.time() - t0
    return res


def summary(path, out):
    rows = sorted((json.loads(x) for x in open(path)), key=lambda r: r["id"])
    T = C.T_UNITS
    d_reg = C.D_DRIFT                      # the region parameter: d + eps
    d_obs = d_reg - EPS
    base = {}
    bpath = C.opt("base", None)
    if bpath:
        base = {r["id"]: r for r in (json.loads(x) for x in open(bpath))}
    S = {}
    for p in ("c", "b"):
        P = [r["planets"][p] for r in rows]
        S[p] = dict(
            eta=max(x["eta"] for x in P), worst_eta_cell=max(rows, key=lambda r: r["planets"][p]["eta"])["id"],
            **{key: dict(bound=[min(x[key]["bound"][0] for x in P), max(x[key]["bound"][1] for x in P)],
                         sampled=[min(x[key]["sampled"][0] for x in P), max(x[key]["sampled"][1] for x in P)],
                         region_sampled=[min(x[key]["region_sampled"][0] for x in P if x[key]["region_sampled"]),
                                         max(x[key]["region_sampled"][1] for x in P if x[key]["region_sampled"])])
               for key in ("FmL", "GmL", "FmG")},
            q_max=max(max(x["q"].values()) for x in P),
            identity_diff_max=max(x["identity_diff"] for x in P),
            chart_action_err_max=max(x["checks"]["chart_action_err"] for x in P),
            closed_form_err_max=max(x["checks"]["closed_form_err"] for x in P),
            GmL_in_analytic_all=all(x["checks"]["GmL_in_analytic"] for x in P))
        for key in ("FmL", "GmL", "FmG"):
            for kind in ("bound", "sampled", "region_sampled"):
                v = S[p][key][kind]
                S[p][key][kind + "_width"] = v[1] - v[0]

    def margin(d, key, kind):
        return d / max(S[p]["eta"] * T + S[p][key][kind + "_width"] for p in S)

    need = {kind: max(S[p]["eta"] * T + S[p]["FmG"][kind + "_width"] for p in S)
            for kind in ("bound", "sampled", "region_sampled")}

    def horizon(d, key, m):
        # the longest time (years) with margin >= m, from the l1 bounds: eta and the ranges do not depend on T
        return min((d / m - S[p][key]["bound_width"]) / S[p]["eta"] for p in S) * C.YEARS_PER_UNIT

    horizons = dict(baseline={m: horizon(d_reg, "FmL", m) for m in (1, 2)},
                    observable={m: horizon(d_obs, "FmG", m) for m in (1, 2)})
    res = dict(
        cells=len(rows), T_units=T, years=1e3, r=R_TUBE, eps=EPS, region_d=d_reg, d_obs=d_obs,
        constraint=dict(d_plus_eps_le_half_r=d_obs + EPS <= R_TUBE / 2 + 1e-15),
        planets=S,
        rung_1e3=dict(
            baseline=dict(d=d_reg, margin_bound=margin(d_reg, "FmL", "bound"),
                          margin_sampled=margin(d_reg, "FmL", "sampled"),
                          margin_region_sampled=margin(d_reg, "FmL", "region_sampled")),
            observable=dict(d=d_obs, margin_bound=margin(d_obs, "FmG", "bound"),
                            margin_sampled=margin(d_obs, "FmG", "sampled"),
                            margin_region_sampled=margin(d_obs, "FmG", "region_sampled"),
                            d_needed_margin1=need, d_needed_margin2={k: 2 * v for k, v in need.items()})),
        horizon_years_bound=horizons,
        cpu_seconds=sum(r["seconds"] for r in rows))
    if base:
        diffs = []
        for r in rows:
            b = base.get(r["id"])
            if not b:
                continue
            for p in ("c", "b"):
                x, y = r["planets"][p], b["planets"][p]
                diffs.append(dict(id=r["id"], p=p, eta_rel=abs(x["eta"] - y["eta"]) / y["eta"],
                                  FmL_bound=max(abs(u - v) for u, v in zip(x["FmL"]["bound"], y["FmL_bound"]))))
        res["reproduction_vs_base"] = dict(cells=len({d["id"] for d in diffs}),
                                           eta_rel_max=max(d["eta_rel"] for d in diffs),
                                           FmL_bound_absdiff_max=max(d["FmL_bound"] for d in diffs))
    per_cell = []
    for r in rows:
        pc = dict(id=r["id"], kind=r["cell"]["kind"], xi=[round(x, 6) for x in r["cell"]["xi"]],
                  eta=[round(x, 6) for x in r["cell"]["eta"]], phi=round(r["cell"]["phi"], 6),
                  emax=[round(x, 4) for x in r["cell"]["emax"]], grid=r["grid"], seconds=round(r["seconds"], 1))
        for p in ("c", "b"):
            x = r["planets"][p]
            pc[p] = dict(eta=float("%.3g" % x["eta"]),
                         FmL=[float("%.3g" % v) for v in x["FmL"]["bound"]],
                         GmL=[float("%.3g" % v) for v in x["GmL"]["bound"]],
                         FmG=[float("%.3g" % v) for v in x["FmG"]["bound"]],
                         GmL_sampled=[float("%.3g" % v) for v in x["GmL"]["sampled"]])
        pc["margin_local_obs"] = round(d_obs / max(r["planets"][p]["eta"] * T + r["planets"][p]["FmG"]["bound"][1]
                                                   - r["planets"][p]["FmG"]["bound"][0] for p in ("c", "b")), 2)
        pc["margin_local_base"] = round(d_reg / max(r["planets"][p]["eta"] * T + r["planets"][p]["FmL"]["bound"][1]
                                                    - r["planets"][p]["FmL"]["bound"][0] for p in ("c", "b")), 2)
        per_cell.append(pc)
    res["per_cell"] = per_cell
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
    cells, ivs, rho_star = CF.plan(m)
    xic = C.opt("xic", None)
    if xic is not None:
        cells = [c for c in cells if abs(c["xi"][0] - float(xic)) < 1e-3]
    print("d(region)", C.D_DRIFT, "eps", EPS, "kappa", CF.KAPPA, "rho*", round(rho_star, 4), "cells", len(cells),
          "nu", nu, "mu", mu, flush=True)
    if "--plan-only" in sys.argv:
        return
    done = set()
    if os.path.exists(out):
        done = {json.loads(x)["id"] for x in open(out)}
    todo = sorted([c for c in cells if c["id"] not in done], key=lambda c: -c["emax"][0])
    lim = int(C.opt("limit", "0"))
    if lim:
        todo = todo[-lim:]                      # the cheapest cells first when testing
    t0 = time.time()
    with mpr.get_context("fork").Pool(int(C.opt("procs", "2")), maxtasksperchild=1) as pool, open(out, "a") as fh:
        for r in pool.imap_unordered(run_cell, [(c, nu, mu) for c in todo]):
            fh.write(json.dumps(r) + "\n")
            fh.flush()
            pc, pb = r["planets"]["c"], r["planets"]["b"]
            print("cell %3d %-6s xi_c %.4f phi %6.3f grid %s %5.1fs eta_c %.2e eta_b %.2e | F-L_b %s G-L_b %s "
                  "F-G_b %s | F-G_c %s | checks %.1e %.1e %s" % (
                      r["id"], r["cell"]["kind"], r["cell"]["xi"][0], r["cell"]["phi"], r["grid"], r["seconds"],
                      pc["eta"], pb["eta"], ["%.3g" % x for x in pb["FmL"]["bound"]],
                      ["%.3g" % x for x in pb["GmL"]["bound"]], ["%.3g" % x for x in pb["FmG"]["bound"]],
                      ["%.3g" % x for x in pc["FmG"]["bound"]], max(pc["checks"]["chart_action_err"],
                                                                     pb["checks"]["chart_action_err"]),
                      max(pc["checks"]["closed_form_err"], pb["checks"]["closed_form_err"]),
                      pc["checks"]["GmL_in_analytic"] and pb["checks"]["GmL_in_analytic"]), flush=True)
    print("total %.0fs" % (time.time() - t0))


if __name__ == "__main__":
    main()
