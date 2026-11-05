#!/usr/bin/env python3
"""LOCK-DATA: the v2 refined threshold of the N = 65 lock package with CHECKER-FAITHFUL sizes (untrusted tooling).

LOCK-GEN-2 (lock_v2.frame) sized sK, sB, sT, the frame claims (bL, bN, bNt, bT) and the domain (rhoH, r1, r2) by
grid SUPREMA on the strip.  The landed checks (checkEmbedding, checkGram, checkTorsion, checkFrameMajorants) bound
the same quantities by the model sup bound, i.e. the WEIGHTED l1 (Wiener) norm sum |c_k| w^{|k|_1}, w = e^{2 pi rho}
(plus rounding and truncation radii), which is larger for this data (the mirror of checkEmbedding at rho = 1/100:
DK row 1.854 against the grid's 1.445; action deviation 0.00325 against 0.0015).  This scan recomputes every size
as a weighted l1 norm of the real-grid Fourier data (a LOWER bound of what the kernel certifies: no rounding, no
truncation radius), the disc-pass claims on the enlarged domain (lock_balls mirror), and the refined threshold.

    OMP_NUM_THREADS=4 python3 lock_l1scan.py OUT.json [rho ...]
"""
import json
import math
import sys
from fractions import Fraction as F

import numpy as np

import lock_v2 as LV

TWO_PI = 2 * math.pi


def l1w(T, f, rho, Ks=90, Ls=18):
    """weighted l1 norm of the real-grid function f (Fourier data), on the diamond support."""
    nx, nt = T["nx"], T["nt"]
    c = np.fft.fft2(f) / (nx * nt)
    k, l = T["k"], T["l"]
    return float(np.sum(np.abs(c) * np.exp(TWO_PI * rho * (np.abs(k) + np.abs(l)))))


def truncate(T, fh, Ks=90, Ls=18):
    k, l = T["k"], T["l"]
    return fh * ((np.abs(k) / Ks + np.abs(l) / Ls) <= 1)


def sizes(T, rho, kappa=1.0, Om=float(LV.OMEGA_R)):
    T = dict(T, Uh=truncate(T, T["Uh"]), Ph=truncate(T, T["Ph"]), Jh=truncate(T, T["Jh"]))
    Ominv = np.zeros((4, 4))
    Ominv[0, 2] = Ominv[1, 3] = -1
    Ominv[2, 0] = Ominv[3, 1] = 1
    ev = lambda fh, d=None: LV.eval_shift(T, fh, 0.0, 0.0, d)
    z = LV.torus_points(T, 0.0, 0.0)
    L = np.zeros(z[0].shape + (4, 2), complex)
    L[..., 0, 0] = 1 + ev(T["Uh"], 0)
    L[..., 0, 1] = ev(T["Uh"], 1)
    L[..., 1, 1] = 1
    for r, key in ((2, "Ph"), (3, "Jh")):
        L[..., r, 0] = ev(T[key], 0)
        L[..., r, 1] = ev(T[key], 1)
    G = np.einsum("...ri,...rj->...ij", L, L)
    B = np.linalg.inv(G)
    Nm = np.einsum("ab,...bk,...kj->...aj", Ominv, L, B)
    LV.Jet.ORDER = 2
    Hj = LV.lock_ham_jet(z, Om, kappa=kappa)
    LV.Jet.ORDER = 3
    h = np.moveaxis(Hj.h, (0, 1), (-2, -1))
    A = np.concatenate([h[..., 2:, :], -h[..., :2, :]], axis=-2)
    DN = np.zeros_like(Nm)
    nx, nt = T["nx"], T["nt"]
    for a in range(4):
        for j in range(2):
            DN[..., a, j] = kappa * LV.eval_shift(T, np.fft.fft2(Nm[..., a, j]) / (nx * nt), 0.0, 0.0, "om")
    XN = np.einsum("...ab,...bj->...aj", A, Nm) - DN
    Tm = np.einsum("...ai,ab,...bj->...ij", Nm, Ominv, XN)
    nrm = lambda Mx: np.array([[l1w(T, Mx[..., i, j], rho) for j in range(Mx.shape[-1])]
                               for i in range(Mx.shape[-2])])
    nL, nB, nN, nT = nrm(L), nrm(B), nrm(Nm), nrm(Tm)
    Tavg = Tm.mean(axis=(0, 1)).real
    s1 = l1w(T, np.real(ev(T["Uh"])), rho)
    s2 = rho * (l1w(T, ev(T["Uh"], 0), rho) + l1w(T, ev(T["Uh"], 1), rho))
    P0, J0 = float(np.real(T["Ph"][0, 0])), float(np.real(T["Jh"][0, 0]))
    out = dict(DK=float(nL.sum(-1).max()), bL=float(nL.sum(-2).max()), Ginv=float(nB.sum(-1).max()),
               bN=float(nN.sum(-1).max()), bNt=float(nN.sum(-2).max()), bT=float(nT.sum(-1).max()),
               Tavg_inv_rowsum=float(np.abs(np.linalg.inv(Tavg)).sum(-1).max()), iota=min(s1, s2),
               P_dev=l1w(T, np.real(ev(T["Ph"])) - P0, rho), J_dev=l1w(T, np.real(ev(T["Jh"])) - J0, rho),
               P0=P0, J0=J0)
    return out


def row(T, rho, mu, kappa=F(1)):
    fr = sizes(T, float(rho))
    up = lambda x: F(LV._up(x * 1.01))
    e6 = F(1, 10 ** 6)
    dom = dict(rhoH=rho + up(fr["iota"]) + mu + e6, c1=F(fr["P0"]).limit_denominator(10 ** 7),
               r1=up(fr["P_dev"]) + mu + e6, c2=F(fr["J0"]).limit_denominator(10 ** 7), r2=up(fr["J_dev"]) + mu + e6)
    bc = LV.ball_claims({k: float(v) for k, v in dom.items()}, 1)
    res = dict(rho=str(rho), mu=str(mu), sizes=fr, domain={k: float(v) for k, v in dom.items()})
    if bc is None:
        res["disc_pass"] = "fails"
        return res
    R = dict(dh=up(bc["dh"]), dx=up(bc["dx"]), d2x=up(bc["d2x"]), d2h=up(bc["d2h"]), bL=up(fr["bL"]),
             bN=up(fr["bN"]), bNt=up(fr["bNt"]), bT=up(fr["bT"]))
    p = LV.lock_package(rho, kappa, up(fr["DK"]) + mu, up(fr["Ginv"]) + mu, up(fr["Tavg_inv_rowsum"]) + mu,
                        up(bc["M"]), mu=mu)
    th = LV.threshold(p, R)
    res.update(claims={a: float(b) for a, b in R.items()}, M=float(p["M"]), sK=float(p["sK"]), sB=float(p["sB"]),
               sT=float(p["sT"]), **th)
    return res


if __name__ == "__main__":
    out = sys.argv[1]
    rhos = [F(x) for x in sys.argv[2:]] or [F(1, 100), F(1, 140), F(1, 200)]
    T = LV.load_torus()
    res = []
    for rho in rhos:
        for mu in (F(1, 1000), F(1, 4000)):
            r = row(T, rho, mu)
            res.append(r)
            print(json.dumps({k: v for k, v in r.items()}, default=str), flush=True)
            json.dump(res, open(out, "w"), indent=1, default=str)
