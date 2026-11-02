#!/usr/bin/env python3
"""HD11964-HOLO: the margins of the complex extension of P = mu fMov(Psi) on the anisotropic strip (estimated).

P's complex extension in the fast angles (and, optionally, in the cell variables) is

    P_C = mu ( (p_c + p_b).(p_c + p_b) / 2 - nu_c nu_b / sqrt(d2) ),   d2 = (q_c - q_b).(q_c - q_b)   (bilinear),

with (q_j, p_j) LP's Poincare chart continued to complex lambda_j: k = 1 - Gamma/Lambda,
v = ((1 - Gamma/(2 Lambda))/Lambda)^(1/2) (xi, eta), F = the solution of F - v0 sin F + v1 cos F = lambda in a strip
|Im F| <= y0 (`KAM.Kepler.keplerSol y0`), c = (cos F, sin F), q = (Lambda^2/nu^2)(k c - v + (v.c/(1+k)) v),
p = (nu^2/(Lambda (1 - v.c))) ((-c1, c0) - (v.c/(1+k)) (-v1, v0)).  It is holomorphic where

  (K) the Kepler contraction of `KAM.Kepler.KeplerData` holds with some y0:
        |Im lambda| + (|Re v0| + |Re v1|) sinh y0 + (|Im v0| + |Im v1|) cosh y0 < y0,  (|v0| + |v1|) cosh y0 < 1;
  (R) the radicand (1 - Gamma/(2 Lambda))/Lambda has Re > 0, and 1 + k != 0;
  (D) Re d2 > 0 (no complex collision; then sqrt(d2) is the principal branch and != 0).

This script measures, on every cell of the fitted plan, with |Im lambda_j| <= 2 pi rho_j:
  (K) the best y0 and the slack of both inequalities (the sup of the v-terms over the cell, sampled);
  (R) min Re of the radicand and min |1 + k|;
  (D) min Re d2, sampled on the distinguished boundary (Im lambda_j = +-2 pi rho_j; Re d2 is pluriharmonic in the
      angles, so its minimum over the strip is attained there) times the cell points; and the crude provable bound
      Re(q_b.q_b) - |q_c.q_c| - 2 |q_c| |q_b| (sups/infs over the samples), q_j.q_j = a_j^2 (1 - v.c)^2 exactly.
Cell points: the real cell (|u_j| <= 1, a grid) or the complex polydisc (|u_j| = 1, random phases).
Usage: python3 -I holo_margin.py --plan=PLAN.json [--rho=0.03,0.15] [--complex] [--cells=all|K,K] [--out=F.json]
"""
import json
import math
import os
import sys

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import hd11964_model as HM  # noqa: E402
import prod2_hp as PH  # noqa: E402

opt = PH.opt


def cell_points(cq, complex_u, n_real=3, n_cplx=400, seed=0):
    """Slow variables (Lam_c, Lam_b, xi_c, eta_c, xi_b, eta_b) at the cell points, complex arrays."""
    c = np.array([float(x) for x in cq["c"]])
    h = np.array([float(x) for x in cq["h"]])
    a, b = float(cq["a"]), float(cq["b"])
    if complex_u:
        rng = np.random.default_rng(seed)
        U = np.exp(2j * np.pi * rng.random((n_cplx, 6)))
        U = np.concatenate([U, np.exp(2j * np.pi * np.array([[0, 0, 0, 0, 0, 0], [.25] * 6, [.5] * 6, [.75] * 6]))])
    else:
        g = np.linspace(-1, 1, n_real)
        mesh = np.meshgrid(*([g] * 6), indexing="ij")
        U = np.stack([m.ravel() for m in mesh], axis=1).astype(complex)
    X = np.empty_like(U)
    X[:, :4] = c[:4] + h[:4] * U[:, :4]
    X[:, 4] = c[4] + a * h[4] * U[:, 4] - b * h[5] * U[:, 5]
    X[:, 5] = c[5] + b * h[4] * U[:, 4] + a * h[5] * U[:, 5]
    return X


def chart_parts(Lam, xi, eta):
    G = (xi * xi + eta * eta) / 2
    k = 1 - G / Lam
    rad = (1 - G / (2 * Lam)) / Lam
    beta = np.sqrt(rad)                       # principal branch
    return k, rad, beta * xi, beta * eta


def kepler(lam, v0, v1, it=60):
    F = lam.copy()
    for _ in range(it):
        g = F - v0 * np.sin(F) + v1 * np.cos(F) - lam
        dg = 1 - v0 * np.cos(F) - v1 * np.sin(F)
        F = F - g / dg
    res = np.abs(F - v0 * np.sin(F) + v1 * np.cos(F) - lam).max()
    return F, res


def qp(nu, Lam, k, v0, v1, F):
    c0, c1 = np.cos(F), np.sin(F)
    vc = v0 * c0 + v1 * c1
    s = Lam ** 2 / nu ** 2
    f = vc / (1 + k)
    q0 = s * (k * c0 - v0 + f * v0)
    q1 = s * (k * c1 - v1 + f * v1)
    t = nu ** 2 / (Lam * (1 - vc))
    p0 = t * (-c1 + f * v1)
    p1 = t * (c0 - f * v0)
    return q0, q1, p0, p1, vc


def kepler_slack(Y, A, B, C, kcap=0.95):
    """The best y0 for `KeplerData`: max over y0 of y0 - (Y + A sinh y0 + B cosh y0), subject to
    C cosh y0 <= kcap (the contraction constant kept away from 1)."""
    best = (-np.inf, None, None)
    for y0 in np.linspace(0.01, 3.0, 3000):
        kap = C * math.cosh(y0)
        if kap > kcap:
            continue
        s = y0 - (Y + A * math.sinh(y0) + B * math.cosh(y0))
        if s > best[0]:
            best = (s, y0, kap)
    return dict(slack=best[0], y0=best[1], kappa=best[2])


def main():
    plan = opt("plan", "")
    rho = [float(x) for x in opt("rho", "0.03,0.15").split(",")]
    complex_u = "--complex" in sys.argv
    m = HM.Model(dps=30)
    nu = [float(x) for x in m.nu]
    cells = PH.plan_cells(plan)
    sel = opt("cells", "all")
    idx = range(len(cells)) if sel == "all" else [int(x) for x in sel.split(",")]
    Y = [2 * math.pi * r for r in rho]
    nx = int(opt("nx", "48"))
    xs = np.linspace(0, 2 * np.pi, nx, endpoint=False)
    out = dict(rho=rho, complex_u=complex_u, cells=[])
    worst = dict(K=[np.inf, np.inf], D=np.inf, crude=np.inf)
    for K in idx:
        cq = cells[K]
        X = cell_points(cq, complex_u)
        rec = dict(cell=K, slab=cq["slab"])
        parts = []
        for j, (iL, ix, ie) in enumerate([(0, 2, 3), (1, 4, 5)]):
            k, rad, v0, v1 = chart_parts(X[:, iL], X[:, ix], X[:, ie])
            A = float((np.abs(v0.real) + np.abs(v1.real)).max())
            B = float((np.abs(v0.imag) + np.abs(v1.imag)).max())
            C = float((np.abs(v0) + np.abs(v1)).max())
            ks = kepler_slack(Y[j], A, B, C, float(opt("kcap", "0.95")))
            ks["slack_kappa_lt_1"] = kepler_slack(Y[j], A, B, C, 0.9999)["slack"]
            ks.update(A=A, B=B, C=C, e_max=float(np.abs(np.sqrt(v0 * v0 + v1 * v1)).max()),
                      rad_re_min=float(rad.real.min()), one_plus_k_min=float(np.abs(1 + k).min()))
            rec["planet_%s" % "cb"[j]] = ks
            worst["K"][j] = min(worst["K"][j], ks["slack"])
            parts.append((X[:, iL], k, v0, v1))
        # (D): the distinguished boundary of the angle strip, times the cell points
        dmin, crude = np.inf, None
        Qc_max = Qb_max = 0.0
        Rb_min = qcqc_max = np.inf
        qcqc_max = 0.0
        for sc in (-1, 1):
            for sb in (-1, 1):
                lc = (xs[:, None] + 1j * sc * Y[0])[:, :, None]          # (nx, 1, 1)
                lb = (xs[None, :] + 1j * sb * Y[1])[:, :, None]          # (1, nx, 1)
                (Lc, kc, v0c, v1c), (Lb, kb, v0b, v1b) = parts
                Fc, rc = kepler(np.broadcast_to(lc, (nx, 1, len(Lc))).copy(), v0c, v1c)
                Fb, rb = kepler(np.broadcast_to(lb, (1, nx, len(Lb))).copy(), v0b, v1b)
                q0c, q1c, p0c, p1c, vcc = qp(nu[0], Lc, kc, v0c, v1c, Fc)
                q0b, q1b, p0b, p1b, vcb = qp(nu[1], Lb, kb, v0b, v1b, Fb)
                d2 = (q0c - q0b) ** 2 + (q1c - q1b) ** 2
                dmin = min(dmin, float(d2.real.min()))
                Qc_max = max(Qc_max, float(np.sqrt(np.abs(q0c) ** 2 + np.abs(q1c) ** 2).max()))
                Qb_max = max(Qb_max, float(np.sqrt(np.abs(q0b) ** 2 + np.abs(q1b) ** 2).max()))
                Rb_min = min(Rb_min, float((q0b * q0b + q1b * q1b).real.min()))
                qcqc_max = max(qcqc_max, float(np.abs(q0c * q0c + q1c * q1c).max()))
                assert rc < 1e-9 and rb < 1e-9, (rc, rb)
        crude = Rb_min - qcqc_max - 2 * Qc_max * Qb_max
        rec.update(d2_re_min=dmin, crude_bound=crude, Qc_max=Qc_max, Qb_max=Qb_max, Rb_min=Rb_min,
                   qcqc_max=qcqc_max)
        worst["D"] = min(worst["D"], dmin)
        worst["crude"] = min(worst["crude"], crude)
        out["cells"].append(rec)
        print("cell %2d slab %d | K_c slack %.4f (y0 %.3f, kappa %.3f, e %.3f) | K_b slack %.4f (y0 %.3f) | "
              "Re d2 min %.3f | crude %.3f" % (K, cq["slab"], rec["planet_c"]["slack"], rec["planet_c"]["y0"] or 0,
                                               rec["planet_c"]["kappa"] or 0, rec["planet_c"]["e_max"],
                                               rec["planet_b"]["slack"], rec["planet_b"]["y0"] or 0, dmin, crude),
              flush=True)
    out["worst"] = worst
    print("worst", worst)
    path = opt("out", "")
    if path:
        with open(path, "w") as fh:
            json.dump(out, fh, indent=1, default=float)


if __name__ == "__main__":
    main()
