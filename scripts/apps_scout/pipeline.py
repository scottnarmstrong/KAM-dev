#!/usr/bin/env python3
"""Shared analysis: from a converged numerical torus to thresholds, digits and support.

For each (rho, c, lam): sampled majorants (kamlib.package; slack 1.05 and margin mu as package R1), the three threshold columns
(thresholds_est.columns), the truncation digits L (thresholds_est.digits_needed) and the support S(L) = CAL * alpha * L^2.

CAL = 1.4 calibrates the double-precision fit alpha on SO-GEN2: alpha(L = 8..12) = 0.79 for the lower lunar torus while the measured
count at L = 88 is 1.1 L^2 (scripts/spin_orbit data, SO-GEN2 table).
"""
import json
import math
import os
import numpy as np

import kamlib as kl
import thresholds_est as te

CAL = 1.4
RES = os.path.join(os.path.dirname(os.path.abspath(__file__)), "results")
os.makedirs(RES, exist_ok=True)


def strip_data_scaled(H, tor, rho, mu_ang, mu_act):
    """as kamlib.strip_data, with separate margins on angles and actions (the action margin scales with lam)."""
    g = tor.g
    data = []
    for sg in kl.SIGNS:
        q = [g.t1 + 1j * rho * sg[0] + g.strip(tor.u[0], rho, sg), g.t2 + 1j * rho * sg[1] + g.strip(tor.u[1], rho, sg)]
        p = [g.strip(tor.y[0], rho, sg), g.strip(tor.y[1], rho, sg)]
        L = np.zeros((4, 2, g.N1, g.N2), dtype=complex)
        arrs = [tor.u[0], tor.u[1], tor.y[0], tor.y[1]]
        wt = np.exp(-2 * np.pi * rho * (sg[0] * g.k1 + sg[1] * g.k2)) * g.mask
        for i in range(4):
            for j in range(2):
                k = g.k1 if j == 0 else g.k2
                L[i, j] = g.i(g.f(arrs[i]) * (2j * np.pi * k) * wt)
        L[0, 0] += 1
        L[1, 1] += 1
        ders = []
        for o in (1, -1):
            zo = [q[0] + 1j * o * mu_ang, q[1] + 1j * o * mu_ang, p[0] + 1j * o * mu_act, p[1] + 1j * o * mu_act]
            ders.append(kl.derivs(H, zo, 3))
        data.append(dict(L=L, ders=ders))
    return data


def analyse(H, tor, om, s, rhos, cs=(1.0,), lams=(1.0,), mu=1 / 160, gamma=None, slack=1.05, coarsen=None):
    """scan the package parameters; `best` = smallest digit count L under v1."""
    fit = kl.fit_decay(tor)
    decs = [x for x in (fit[0][0], fit[1][0]) if x == x and x > 0]
    a_min = min(decs)
    alpha, counts = kl.support_model(tor)
    out = dict(decay=[fit[0][0], fit[1][0]], width=[f[0] * math.log(10) / (2 * math.pi) for f in fit], alpha=alpha,
               counts=counts, rows=[], gamma=gamma, om=list(om))
    work = tor if coarsen is None else tor.resample(kl.Grid(*coarsen))
    for rho in rhos:
        for lam in lams:
            sd = strip_data_scaled(H, work, rho, mu, mu * lam)
            for c in cs:
                P = kl.package(sd, H, work, om, s, lam=(lam, lam), c=c, mu=mu, slack=slack)
                if not np.isfinite(P["sT"]) or not np.isfinite(P["M"]):
                    continue
                P.update(rho=rho, mu=mu, Tmax=P["raw"]["Tmax"])
                r = te.columns(P, gamma * c)
                r.update(rho=rho, c=c, lam=lam, M=P["M"], M2=P["M2"], sK=P["sK"], sB=P["sB"], sT=P["sT"], Tmax=P["raw"]["Tmax"], P=P)
                r["L"] = {key: te.digits_needed(r[key], rho, a_min) for key in ("current", "v1", "v2", "ell1")}
                r["S"] = {key: CAL * alpha * r["L"][key] ** 2 for key in r["L"]}
                out["rows"].append(r)
    if not out["rows"]:
        return out
    b = min(out["rows"], key=lambda r: r["L"]["v1"])
    bv = min(out["rows"], key=lambda r: r["L"]["v2"])
    bc = min(out["rows"], key=lambda r: r["L"]["current"])
    full = te.columns(b["P"], gamma * b["c"], om=(b["c"] * om[0], b["c"] * om[1]))
    b["v2+"], b["c_fs"] = full["v2+"], full["c_fs"]
    out["best"], out["best_v2"], out["best_cur"] = strip(b), strip(bv), strip(bc)
    out["rows"] = [strip(r) for r in out["rows"]]
    return out


def strip(r):
    return {k: v for k, v in r.items() if k != "P"}


def show(name, a):
    if "best" not in a:
        print("%-30s no finite package" % name, flush=True)
        return
    b, v, c = a["best"], a["best_v2"], a["best_cur"]
    print("%-30s dec %.3f %.3f alpha %.2f gam %.4f | v1@rho %.4f c %.2f lam %.3g M %.2f sK %.2f sB %.2f sT %.2f T %.1f | thr cur %.1f v1 %.1f v2 %.1f(@%.1f) v2+ %.1f ell1 %.1f | L cur %.0f v1 %.0f v2 %.0f | S cur %.0f v1 %.0f v2 %.0f"
          % (name, a["decay"][0], a["decay"][1], a["alpha"], a["gamma"], b["rho"], b["c"], b["lam"], b["M"], b["sK"], b["sB"], b["sT"], b["Tmax"],
             c["current"], b["v1"], v["v2"], v["L"]["v2"], b.get("v2+", float("nan")), b["ell1"], c["L"]["current"], b["L"]["v1"], v["L"]["v2"],
             c["S"]["current"], b["S"]["v1"], v["S"]["v2"]), flush=True)


def save(name, obj):
    json.dump(obj, open(os.path.join(RES, name), "w"), indent=1, default=float)


def continuation(H_of, om_of, tor, steps, s=1.0, E_of=None, tol=3e-13, verbose=False, iso=True, maxerr=1e-8):
    """continuation along steps t; returns (tor, s, err, t_reached)."""
    err = None
    t_ok = 0.0
    for t in steps:
        H = H_of(t)
        om = om_of(t)
        if E_of is not None:
            E0 = E_of(t)
        else:
            E0 = float(np.real(kl.derivs(H, tor.z(), 1, const=True)[0]).mean())
        tor2, s2, err = kl.solve(H, tor, om, s, E0=E0, iso=iso, tol=tol)
        if verbose:
            print("   t %.4f err %.2e s %.8f" % (t, err, s2), flush=True)
        if not np.isfinite(err) or err > maxerr:
            return tor, s, err, t_ok
        tor, s = tor2, s2
        t_ok = t
    return tor, s, err, t_ok
