#!/usr/bin/env python3
"""LP-QUANT driver: evaluates every system, writes results/<key>.json and results/summary.md.

Usage: nice -n 5 python3 -I scripts/lp_quant/run_all.py [--keys SJ,JSUN,...] [--procs 7]

Untrusted design tooling.  Labels per quantity are given in docs/campaign/studies/LP-QUANT.md section 2.
"""
import argparse
import json
import math
import multiprocessing as mp
import os
import sys
import time
import traceback
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from systems import catalogue, System
import geometry as G
import chart as Ch
import divisors as Dv
import chain as Cn
import lambda_route as LR

RES = os.path.join(HERE, "results")
TARGETS = (1e4, 1e6, 1e9, 5e9)


def jsonable(o):
    if isinstance(o, dict):
        return {str(k): jsonable(v) for k, v in o.items()}
    if isinstance(o, (list, tuple)):
        return [jsonable(v) for v in o]
    if isinstance(o, np.ndarray):
        return o.tolist()
    if isinstance(o, (np.floating, np.integer)):
        return o.item()
    if isinstance(o, float) and not math.isfinite(o):
        return None
    return o


def geometry_block(ctx):
    s = ctx.sys
    I, nu = ctx.I0, ctx.nu
    b, bc, bs, pairs = G.thresholds(I, nu)
    delta = ctx.delta_max
    g = dict(n=s.n, mu=s.mu, nu=nu, a=s.a, e=s.e, inc=s.inc, I0=I, B=b, B_lower=ctx.B0_lb, B_star=bs, C=ctx.C0, beta=ctx.C0 / b,
             delta=delta, strong_stable=bool(delta > 0), active_pair=min(pairs, key=lambda p: p[3])[0],
             contact=[dict(pair=p[0], u=p[1], v=p[2], Bij=p[3]) for p in pairs], gradB=G.grad_B(I, nu),
             source=s.source, note=s.note, years_per_unit=s.years_per_unit)
    if delta > 0:
        bud = G.budgets(I, nu, delta, ctx.omega)
        g["budgets"] = bud
        g["budget_da_over_a"] = float(2 * bud["r_lit_half"] / np.min(I))
        g["dstar_formula"] = G.dstar_formula(I, nu, delta / 2)
        g["dstar_sharp"] = G.dstar_sharp(I, nu, delta / 2)
        g["dpair_sharp"] = G.dpair_sharp(I, nu, delta / 2)
        g["ecc_caps_at_C"] = G.ecc_caps(I, ctx.C0)
        g["ecc_caps_literal_ball"] = G.ecc_caps(I, ctx.B0 - delta / 4)
        g["hill"] = LR.hill_margin(ctx)
    return g


def chain_block(ctx):
    s = ctx.sys
    n = ctx.n
    out = {}
    lnT = {str(t): Cn.ln_years(ctx, t) for t in TARGETS}
    lit = Cn.best_literal(ctx)
    if lit is not None:
        lit = dict(lit)
        lit["constants"] = Cn.lean_output_constants(ctx, lit)
        lit["log10_mu_5Gyr"] = Cn.mu_for_time(lit, lnT["5000000000.0"])
        tt = Cn.theorem_time(lit, s.mu)
        lit["lnT_actual"] = tt
    out["literal"] = lit
    cb = ctx.B0 - ctx.delta_max / 4
    out["rho_holo_literal"] = ctx.rho_holo(cb)
    out["rho_holo_tailored"] = ctx.rho_holo(ctx.C0 * 1.1)
    out["tube_R_literal"] = ctx.tube_R(cb)
    d, Q = Ch.real_gaps(ctx.nu, ctx.I0, cb)
    out["lemma8_d_Q"] = (d, Q)
    if not ctx.spatial:
        out["lemma8_R"] = Ch.lemma8_radius(ctx.nu, ctx.I0, cb, d, Q)
    # choose tau for the arithmetic tier
    taus = [n - 1 + x for x in (0.1, 0.25, 0.5)]
    best_tau, best_val = None, -math.inf
    for t in taus:
        g = ctx.gamma(t)[0]
        r = Cn.engine_mu(ctx, Cn.Opts(tau=t), lnT["5000000000.0"], gamma=g, tau=t)
        if r is not None and r["log10_mu"] > best_val:
            best_tau, best_val = t, r["log10_mu"]
    if best_tau is None:
        best_tau = n - 0.5
    out["tau"] = best_tau
    out["gamma"] = ctx.gamma(best_tau)
    wf, opts = Cn.waterfall(ctx, best_tau, lnT["5000000000.0"])
    out["waterfall_5Gyr"] = wf
    final_key = wf[-2]["step"] if len(wf) >= 2 else wf[-1]["step"]
    best = opts[final_key]  # best tier that the landed engine or a small variant admits, or pair tier for n >= 3
    g = out["gamma"][0]
    tier_engine = [o for name, o in opts.items() if name == "constant subtracted"][0]
    out["engine_targets"] = {}
    for t, l in lnT.items():
        r = Cn.engine_mu(ctx, tier_engine, l, gamma=g, tau=best_tau)
        out["engine_targets"][t] = None if r is None else dict(log10_mu=r["log10_mu"], K=r["K"], s=r["s"], alpha=r["alpha"], r=r["r"])
    r0 = Cn.engine_mu(ctx, tier_engine, -math.inf, gamma=g, tau=best_tau)
    out["engine_mu0"] = None if r0 is None else dict(log10_mu=r0["log10_mu"], K=r0["K"], s=r0["s"], alpha=r0["alpha"])
    at = Cn.engine_time(ctx, tier_engine, s.mu, gamma=g, tau=best_tau)
    out["engine_at_actual"] = None if at is None else dict(lnT=at["lnT"], years=Cn.years(ctx, at["lnT"]), K=at["K"], r=at["r"])
    pm = Cn.paper_mu(ctx, lnT["5000000000.0"], g, best_tau)
    pmt = Cn.paper_mu(ctx, lnT["5000000000.0"], g, best_tau, "tailored")
    out["paper_log10_mu_5Gyr"] = pm
    out["paper_tailored_log10_mu_5Gyr"] = pmt
    pr = Cn.paper_route(ctx, s.mu, g, best_tau)
    out["paper_at_actual"] = pr
    if lit is not None and not ctx.spatial and out.get("lemma8_R", 0) > 0:
        l8 = Cn.lean_literal(ctx, lit["delta"], lit["tau"], out["lemma8_R"], gamma=lit["gamma"])
        out["literal_at_lemma8_R"] = None if l8 is None else dict(log10_mu0=l8["log10_mu0"], s=l8["s"], M=l8["M"])
    return out


def lambda_block(ctx):
    s = ctx.sys
    mu = s.mu
    n = ctx.n
    delta = ctx.delta_max
    bud = G.budgets(ctx.I0, ctx.nu, delta, ctx.omega)
    res = LR.resonance_table(ctx, K=40 if n <= 3 else 24)
    out = dict(resonances=res, r_budget=bud["r_lit_half"])
    # first-order oscillation at the literal budget's ball
    sc0 = LR.scan(ctx, 1e-5, Cball=ctx.C0 * 1.02, N=256, J=30)
    rt0 = LR.rates(ctx, sc0, mu)
    amp = rt0["amp"]
    out["amp"] = amp
    # the resonance-free tube for the modes that matter
    tail = LR.tail_profile(ctx, ctx.C0 * 1.05)
    out["tail_shells"] = tail
    rbud = bud["r_lit_half"]
    out["closure"] = {}
    for yrs in (1e6, 1e9, 5e9):
        T = math.exp(Cn.ln_years(ctx, yrs))
        out["closure"][str(yrs)] = LR.closure(ctx, tail, mu, T)
    T5 = math.exp(Cn.ln_years(ctx, 5e9))
    out["eta_budget_5Gyr"] = rbud / T5
    # Gronwall and first-order averaging, uniform on the AMD ball that the tube implies
    rmid = min(rbud, 3.5 * amp)
    out["rates"] = {}
    for name, r in (("budget", rbud), ("mid", rmid)):
        sc = LR.scan(ctx, r, N=256, J=30)
        rt = LR.rates(ctx, sc, mu)
        rt.update(r=r, Cball=sc["Cball"], T0_yr=r / rt["eta0"] * s.years_per_unit,
                  T1_yr=max(r - 2 * rt["amp"], 0.0) / rt["eta1"] * s.years_per_unit,
                  G=sc["Gi"], parts=sc["parts"], sup_dlam=sc["sup_dlam"], unsolved=sc["unsolved"])
        out["rates"][name] = rt
    # the actual-coefficient normal form, pair by pair, at sampled slow points of the ball the true oscillation reaches
    Cb = ctx.C0 + n * amp
    rng = np.random.default_rng(6)
    pairs = [(i, i + 1) for i in range(n - 1)]
    out["newton"] = {}
    out["series"] = {}
    for (i, j) in pairs:
        rows = []
        zs = Ch._real_slow(rng, 8, n, 1, ctx.I0, Cb)
        zs = zs / np.sqrt(np.sum(zs * zs, axis=1, keepdims=True)) * math.sqrt(2 * Cb)
        for t in range(8):
            z = zs[t]
            nw = LR.fast_newton(ctx, i, j, z[2 * i: 2 * i + 2], z[2 * j: 2 * j + 2], mu, steps=4)
            rows.append(nw["rho"])
        rows = np.array(rows)
        out["newton"][f"{i}-{j}"] = dict(median=np.median(rows, axis=0), worst=rows.max(axis=0))
        z = zs[0]
        out["series"][f"{i}-{j}"] = LR.fast_lie(ctx, i, j, z[2 * i: 2 * i + 2], z[2 * j: 2 * j + 2], Q=4)
    out["secular"] = LR.secular_rate(ctx, mu)
    return out


def low_mass(ctx):
    """T as a function of mu: theorem (literal, when mu <= mu0) and the best engine tier."""
    g_tau = ctx.chain_tau
    g = ctx.gamma(g_tau)[0]
    tier = Cn.Opts(tau=g_tau, lip="sharp", ball="tailored", alpha="direct", fnorm="direct", label="c0")
    rows = []
    for e in list(range(3, 31)):
        mu = 10.0 ** (-e)
        r = Cn.engine_time(ctx, tier, mu, gamma=g, tau=g_tau)
        rows.append(dict(mu=mu, engine_years=None if r is None else Cn.years(ctx, r["lnT"]), K=None if r is None else r["K"],
                         r=None if r is None else r["r"]))
    return rows


def chain_only(key):
    """Recompute the chain block of an existing result, keeping geometry and the Lambda route."""
    t0 = time.time()
    try:
        p = os.path.join(RES, key + ".json")
        d = json.load(open(p))
        s = catalogue()[key]
        ctx = Cn.Ctx(s)
        if ctx.delta_max > 0:
            d["chain"] = chain_block(ctx)
            ctx.chain_tau = d["chain"]["tau"]
            if key in ("SJ", "E3w", "E2c"):
                d["low_mass"] = low_mass(ctx)
        with open(p, "w") as f:
            json.dump(jsonable(d), f, indent=1)
        return key, time.time() - t0, None
    except Exception:
        return key, time.time() - t0, traceback.format_exc()


def run_system(key):
    t0 = time.time()
    try:
        S = catalogue()
        s = S[key]
        ctx = Cn.Ctx(s)
        out = dict(key=key, name=s.name, klass=s.klass, geometry=geometry_block(ctx))
        if ctx.delta_max > 0:
            out["chain"] = chain_block(ctx)
            ctx.chain_tau = out["chain"]["tau"]
            if not ctx.spatial:
                out["lambda"] = lambda_block(ctx)
            if key in ("SJ", "E3w", "E2c"):
                out["low_mass"] = low_mass(ctx)
        out["seconds"] = time.time() - t0
        with open(os.path.join(RES, key + ".json"), "w") as f:
            json.dump(jsonable(out), f, indent=1)
        return key, out["seconds"], None
    except Exception:
        return key, time.time() - t0, traceback.format_exc()


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--keys", default=None)
    ap.add_argument("--procs", type=int, default=7)
    ap.add_argument("--chain-only", action="store_true")
    a = ap.parse_args()
    os.makedirs(RES, exist_ok=True)
    keys = a.keys.split(",") if a.keys else list(catalogue().keys())
    os.environ.setdefault("OMP_NUM_THREADS", "1")
    with mp.Pool(a.procs) as p:
        for key, sec, err in p.imap_unordered(chain_only if a.chain_only else run_system, keys):
            print(f"{key}: {sec:.0f}s" + ("" if err is None else "\nFAILED\n" + err), flush=True)
