#!/usr/bin/env python3
"""Weighted-l1 data of the lunar candidate R1 for the l1 entry step (B10, blueprint/parts/p2s2-l1hybrid.tex).

Untrusted tooling, double precision, HEURISTIC: FFT coefficients on the shifted grids of step0_actual.py (sampled data,
not enclosures).  Every number below is a ratio of a weighted-l1 norm to the sup norm (or sup cap) that the sup-norm
theorem already uses, so it is scale-free in the size of the invariance error.

Norms (blueprint Part p2s2-l1hybrid, Definition bp:p2s2l1:norms): for f : T_r -> C^p, |f|_{l1,r} = max_i
sum_k |f_hat_{i,k}| e^{2 pi r |k|_1}; for matrices the maximum over rows of the sums over the entries of a row.  The
coefficients of a real-on-reals f are read off the two corner grids Im theta = (r, r) and (r, -r): there the shifted
coefficient of k is f_hat_k e^{-2 pi k.y}, equal to |f_hat_k| e^{2 pi r |k|_1} in modulus on the quadrants
{k1 <= 0, k2 <= 0} and {k1 <= 0, k2 > 0}; the half plane k1 > 0 follows from |f_hat_{-k}| = |f_hat_k|.

Measured (normalised error E^ = E/e_act, e_act = sampled sup_{T_rho}|E|, time scale c = 7/4, rotated frame):
  r_E   = |E|_{l1,rho} / e_act
  aN    = |eta^N|_{l1,rho} / (s_Lt e_act),  aL = |eta^L|_{l1,rho} / (s_Nt e_act)   (s_*: the caps of thresholds_v2.package)
  t1    = |T|_{l1, rho - delta0} (row sums), tR = sup_R |T|
  nuK   = |L|_{l1,rho}, nuN = |N|_{l1,rho}, and |L^T|_{l1}, |N^T|_{l1}, |B|_{l1} for reference.

Usage:  python3 -I scripts/apost_sharp/l1_entry_r1.py [--grid N1 N2] [--json OUT]
"""
import json, math, os, sys
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import step0_actual as S0                      # noqa: E402
import r1_norms                                # noqa: E402

TWO_PI = 2 * math.pi


def weighted_l1(G, vals_a, vals_b, matrix=False):
    """|f|_{l1,r} from the corner grids (r, r) -> vals_a and (r, -r) -> vals_b (shape N1 x N2 x p or x p x q)."""
    ca = np.abs(G.coef_at(vals_a))
    cb = np.abs(G.coef_at(vals_b))
    k, l = G.kk, G.ll
    sh = (slice(None), slice(None)) + (None,) * (ca.ndim - 2)
    qa = ((k <= 0) & (l <= 0))[sh]
    qb = ((k <= 0) & (l > 0))[sh]
    half = np.where(qa, ca, 0.0) + np.where(qb, cb, 0.0)              # k1 <= 0
    w = np.where((k < 0)[sh], 2.0, 1.0)                                 # mirror k1 > 0 (realness)
    tot = (half * w).sum(axis=(0, 1))                                   # per component (or entry)
    if matrix:
        return float(tot.sum(axis=-1).max())                            # max row sum
    return float(tot.max())


def rowsum_sup(M):
    return float(np.abs(M).sum(-1).max())


def main():
    N1, N2 = 1024, 256
    if "--grid" in sys.argv:
        i = sys.argv.index("--grid"); N1, N2 = int(sys.argv[i + 1]), int(sys.argv[i + 2])
    res = S0.residual_coefficients(log=lambda *a: None)
    G = S0.Grid(N1, N2)
    Cs = S0.residual_grid(G, res)
    rho, d0, c = S0.RHO, S0.DELTA0, S0.C_TIME
    # e_act: sampled sup over T_rho (corners)
    e_act = 0.0
    for y in ((rho, rho), (rho, -rho)):
        e_act = max(e_act, S0.vmax(np.stack([G.eval(C, y) for C in Cs], axis=-1)))
    out = {}
    corners = lambda yy: ((yy, yy), (yy, -yy))
    # E, eta^L, eta^N and the frame on T_rho
    vals = {k_: [] for k_ in ("E", "etaL", "etaN", "L", "N", "LT", "NT", "B")}
    sups = {k_: 0.0 for k_ in vals}
    for y in corners(rho):
        o = r1_norms.objects(G.cand, y[0], y[1], c)
        Ev, _ = S0.E_at(G, Cs, y, e_act)
        LT = S0.tr(o["L"])
        etaL = -S0.mv(S0.mm(o["B"], LT), Ev)
        etaN = S0.mv(LT, S0.mv(S0.OM, Ev))
        for k_, v_ in (("E", Ev), ("etaL", etaL), ("etaN", etaN), ("L", o["L"]), ("N", o["N"]), ("LT", LT),
                       ("NT", o["NT"]), ("B", o["B"])):
            vals[k_].append(v_)
            sups[k_] = max(sups[k_], S0.vmax(v_) if v_.ndim == 3 else rowsum_sup(v_))
        del o
    for k_, (va, vb) in vals.items():
        out[k_ + "_l1_rho"] = weighted_l1(G, va, vb, matrix=(va.ndim == 4))
        out[k_ + "_sup_rho"] = sups[k_]
    del vals
    # torsion on T_{rho - delta0} and on the reals
    Tv = []
    tsup = 0.0
    for y in corners(rho - d0):
        T = r1_norms.objects(G.cand, y[0], y[1], c)["T"]
        Tv.append(T); tsup = max(tsup, rowsum_sup(T))
    out["T_l1_rho-d0"] = weighted_l1(G, Tv[0], Tv[1], matrix=True)
    out["T_sup_rho-d0"] = tsup
    out["T_sup_R"] = rowsum_sup(r1_norms.objects(G.cand, 0.0, 0.0, c)["T"])
    # ratios against the caps of the threshold package (thresholds_v2.package: sampled x 1.05 + mu)
    import thresholds_v2 as T2
    D = T2.package("R1")
    sLt, sNt = float(D["sLt"]), float(D["sNt"])
    out.update(grid=[N1, N2], e_act=e_act, r_E=out["E_l1_rho"], aN=out["etaN_l1_rho"] / sLt,
               aL=out["etaL_l1_rho"] / sNt, sLt_cap=sLt, sNt_cap=sNt)
    print("R1 weighted-l1 data (heuristic: sampled FFT, grid %dx%d; E normalised by e_act = %.4e)" % (N1, N2, e_act))
    print("| object | l1 norm | sup norm | l1 / sup |")
    print("|---|---:|---:|---:|")
    for k_ in ("E", "etaN", "etaL", "L", "N", "LT", "NT", "B"):
        a_, b_ = out[k_ + "_l1_rho"], out[k_ + "_sup_rho"]
        print("| %s on T_rho | %.4f | %.4f | %.3f |" % (k_, a_, b_, a_ / b_))
    print("| T on T_(rho-delta0) | %.4f | %.4f | %.3f |" % (out["T_l1_rho-d0"], out["T_sup_rho-d0"],
                                                         out["T_l1_rho-d0"] / out["T_sup_rho-d0"]))
    print("sup_R |T| = %.4f" % out["T_sup_R"])
    print("aN = |eta^N|_l1/(s_Lt e) = %.4f, aL = |eta^L|_l1/(s_Nt e) = %.4f  (caps s_Lt = %.4f, s_Nt = %.4f)"
          % (out["aN"], out["aL"], sLt, sNt))
    if "--json" in sys.argv:
        json.dump(out, open(sys.argv[sys.argv.index("--json") + 1], "w"), indent=1)
    return out


if __name__ == "__main__":
    main()
