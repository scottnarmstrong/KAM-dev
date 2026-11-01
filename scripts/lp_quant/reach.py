#!/usr/bin/env python3
"""LP-QUANT: largest mu reaching 5 Gyr for the two elementary Lambda-only certificates, written to results/reach.json.
 Gronwall:     |dLambda/dt| <= mu G0 on the ball C0 + n r, so T = r/(mu G0), with r the budget (no normal form).
 First order:  J = Lambda + mu d_i chi, rate mu^2 G1 + mu U (U = modes unsolved on the tube), T = (r - 2 mu A)/rate, on a tube
               small enough to keep the nearest low-order resonance outside.
Both are sampled sups (`estimated`) of quantities that a checker could enclose directly."""
import json, math, os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import numpy as np
from systems import catalogue
import chain as Cn
import lambda_route as LR
import geometry as G

RES = os.path.join(HERE, "results")
out = {}
for key in ("SJ", "SJcal", "JSUN", "E2w", "E3w", "E2c", "E3c", "HD109271", "HD1461", "HD11964", "HD69830"):
    s = catalogue()[key]
    ctx = Cn.Ctx(s, Kmax=2000 if s.n == 2 else 100)
    T = math.exp(Cn.ln_years(ctx, 5e9))
    bud = G.budgets(ctx.I0, ctx.nu, ctx.delta_max, ctx.omega)
    r = bud["r_lit_half"]
    sc = LR.scan(ctx, r, N=192, J=24)
    mu_g = r / (T * sc["sup_dlam"])
    rec = LR.resonance_table(ctx, K=12)
    d = min(x["dist"] for x in rec) if rec else r
    r1 = min(r, 0.5 * d)
    sc1 = LR.scan(ctx, r1, N=192, J=24)
    Gm, U, A = float(np.max(sc1["Gi"])), sc1["unsolved"], float(np.max(sc1["amp1"]))
    lo, hi = -30.0, -1.0
    for _ in range(60):
        m = 0.5 * (lo + hi)
        mu = 10 ** m
        gain = r1 - 2 * mu * A
        ok = gain > 0 and gain / (mu * mu * Gm + mu * U) >= T
        lo, hi = (m, hi) if ok else (lo, m)
    out[key] = dict(mu_actual=s.mu, r=r, G0=sc["sup_dlam"], log10_mu_gronwall=math.log10(mu_g), r1=r1, G1=Gm, U=U, A=A,
                    log10_mu_first=lo, nearest_dist=d)
    print(key, {k: (round(v, 2) if k.startswith("log") else v) for k, v in out[key].items()}, flush=True)
with open(os.path.join(RES, "reach.json"), "w") as f:
    json.dump(out, f, indent=1)
