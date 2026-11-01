#!/usr/bin/env python3
"""LP-QUANT: second stage of the Lambda route.  Reads results/<key>.json (run_all.py) and replaces the block "newton" by the staged
solver of lambda_route.fast_newton, adding per-sample convergence and the spread of the normal-form frequencies over the ball,
which is what decides how close a mean-motion resonance really is.  Usage: nice -n 5 python3 -I newton_only.py [--procs 7]
"""
import argparse
import json
import math
import multiprocessing as mp
import os
import sys
import time
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from systems import catalogue
import chain as Cn
import chart as Ch
import lambda_route as LR
from run_all import jsonable

RES = os.path.join(HERE, "results")
SAMPLES = 10
STEPS = 6
YEARS = (1e6, 1e9, 5e9)


def run(key):
    t0 = time.time()
    p = os.path.join(RES, key + ".json")
    d = json.load(open(p))
    if "lambda" not in d:
        return key, 0.0
    s = catalogue()[key]
    ctx = Cn.Ctx(s, Kmax=2000 if s.n == 2 else None)
    l = d["lambda"]
    mu, n = s.mu, s.n
    Cb = ctx.C0 + n * l["amp"]
    rng = np.random.default_rng(6)
    out = {}
    for i in range(n - 1):
        j = i + 1
        rows, freq = [], []
        zs = Ch._real_slow(rng, SAMPLES, n, 1, ctx.I0, Cb)
        # half on the sphere of the ball, half at the actual AMD with random perihelia
        nrm = np.sqrt(np.sum(zs * zs, axis=1, keepdims=True))
        zs[: SAMPLES // 2] = zs[: SAMPLES // 2] / nrm[: SAMPLES // 2] * math.sqrt(2 * Cb)
        Gam = s.I0 * (1 - np.sqrt(1 - s.e ** 2))
        for t in range(SAMPLES // 2, SAMPLES):
            th = rng.uniform(0, 2 * math.pi, n)
            zs[t, 0::2] = np.sqrt(2 * Gam) * np.cos(th)
            zs[t, 1::2] = np.sqrt(2 * Gam) * np.sin(th)
        for t in range(SAMPLES):
            z = zs[t]
            nw = LR.fast_newton(ctx, i, j, z[2 * i: 2 * i + 2], z[2 * j: 2 * j + 2], mu, steps=STEPS)
            rows.append(nw["rho"])
            # Frequencies at t = 0 only (omega + mu d<f>/dI).  Later ones are meaningful only on converged samples: an earlier
            # draft read them at the best step and reported a spurious spread of the divisor over the ball.
            freq.append([[float(x[0]), float(x[1])] for x in nw["freq"]])
        rows = np.array(rows)
        best = np.nanmin(np.where(np.isfinite(rows), rows, np.inf), axis=1)
        sphere = rows[: SAMPLES // 2]
        actual = rows[SAMPLES // 2:]
        out[f"{i}-{j}"] = dict(median=np.median(rows, axis=0), worst=np.max(rows, axis=0), best_rate=best,
                               rows=rows, freq=freq, median_actual=np.median(actual, axis=0),
                               median_sphere=np.median(sphere, axis=0), worst_sphere=np.max(sphere, axis=0),
                               worst_actual=np.max(actual, axis=0))
    l["newton"] = out
    rec = l["resonances"]
    if n == 2 and rec:  # HD 11964 has no record divisor below order 40 apart from the slow outer mean motion
        allf = np.array(out["0-1"]["freq"])  # (sample, step, 2)
        fr = allf[:, 0, :]
        k0 = max(rec, key=lambda x: x["order"])["k"]
        val = np.abs(fr[:, 0] * k0[0] + fr[:, 1] * k0[1])
        # resonance strength: how far the divisor moves once the near-resonant mode is solved, relative to the divisor.  Well
        # below 1 the mode is a perturbation; near 1 its width is comparable to its distance and a plain step fails.
        dv = allf[:, :, 0] * k0[0] + allf[:, :, 1] * k0[1]
        conv = np.array(out["0-1"]["rows"])
        ok = conv[:, -1] <= conv[:, 1]
        strength = np.max(np.abs(dv[:, :3] - dv[:, :1]), axis=1) / val
        act = val[SAMPLES // 2:]
        l["resonance_shift"] = dict(k=k0, nominal=max(rec, key=lambda x: x["order"])["div"], eff_min=float(val.min()),
                                    eff_max=float(val.max()), eff_actual_min=float(act.min()), eff_actual_max=float(act.max()),
                                    strength_sphere=float(np.max(strength[: SAMPLES // 2])),
                                    strength_actual=float(np.max(strength[SAMPLES // 2:])),
                                    converged_sphere=int(np.sum(ok[: SAMPLES // 2])),
                                    converged_actual=int(np.sum(ok[SAMPLES // 2:])), samples_each=SAMPLES // 2)
        om = np.median(fr[SAMPLES // 2:], axis=0)
        l["omega_eff"] = om
        l["closure_eff"] = {}
        for y in YEARS:
            T = math.exp(Cn.ln_years(ctx, y))
            l["closure_eff"][str(y)] = LR.closure(ctx, l["tail_shells"], mu, T, omega=om)
    with open(p, "w") as f:
        json.dump(jsonable(d), f, indent=1)
    return key, time.time() - t0


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--procs", type=int, default=7)
    ap.add_argument("--keys", default=None)
    a = ap.parse_args()
    keys = a.keys.split(",") if a.keys else [k for k in catalogue() if os.path.exists(os.path.join(RES, k + ".json"))]
    with mp.Pool(a.procs) as p:
        for k, t in p.imap_unordered(run, keys):
            print(f"{k}: {t:.0f}s", flush=True)
