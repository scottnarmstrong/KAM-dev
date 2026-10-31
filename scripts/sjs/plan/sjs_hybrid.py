#!/usr/bin/env python3
"""SJS-PLAN item 1: the hybrid restart's constant on SJS: e1 = A e^2 for truncated candidates of the coarse torus.

Untrusted design tooling, double precision.  SHARP2-HYBRID's measured first step, on FH25's Delaunay chart (the additive step
K1 = K + DK, DK = P xi, fixed frequency): for the truncation K_L of the torus at L digits,
    E_L = invariance error of K_L,   Et = E_L + DX_H(K_L) DK - D(DK) omega   (the linearised new error),
    E1 = the actual new error of K_L + DK.
Weighted l^1 norms at the strip rho (2 pi units), per block (angles, actions); the theorem's norm in a chart (c, ell) is
max(c/2pi |E_ang|, c/ell |E_act|).  The hybrid threshold of the plain threshold e* is sqrt(e*/A), A = e1/e^2 in the chart's units.
The floor of this measurement is the torus's own residual (1.7e-9 on the 128 x 128 x 144 grid).
Usage: python3 -I scripts/sjs/plan/sjs_hybrid.py TORUS.npz [--json OUT]
"""
import json, math, os, sys, time
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import sjs_torus as ST
sys.path.pop(0)
TP = 2 * math.pi


def l1(gr, f, rho):
    """weighted l^1 norm of real periodic f (..., N1, N2, N3) over the full lattice, per leading index"""
    F = np.abs(gr.f(f)) / np.prod(gr.shape)
    k1 = sum(np.abs(k) for k in gr.kk)
    w = np.exp(rho * k1)
    mult = np.where(gr.kk[2] == 0, 1.0, 2.0)            # rfft half
    if gr.shape[2] % 2 == 0:
        mult = np.where(gr.kk[2] == gr.shape[2] // 2, 1.0, mult)
    return np.sum(F * w * mult, axis=(-3, -2, -1))


def truncate(gr, u, L, rho, ell):
    """keep k with max_components |c_k| s_j e^{rho |k|} >= 10^-L, s = (1, 1, 1, 1/ell, ...)"""
    U = gr.f(u)
    avg = U[..., 0, 0, 0].copy()
    A = np.abs(U) / np.prod(gr.shape)
    s = np.array([1.0] * 3 + [1.0 / ell] * 3).reshape(6, 1, 1, 1)
    k1 = sum(np.abs(k) for k in gr.kk)
    m = (A * s).max(axis=0) * np.exp(rho * k1)
    m[0, 0, 0] = 0
    keep = m >= 10.0 ** -L
    keep[0, 0, 0] = True
    return gr.fi(U * keep), int(np.count_nonzero(keep)) * 2


def run(gr, u, L, rho, ell):
    uL, S = truncate(gr, u, L, rho, ell)
    g = ST.geom(gr, uL, ST.MU0, 0.0, want_hess=True)
    E = g["E"]
    u1, _, info = ST.newton(gr, uL, 0.0, ST.MU0, "invariant")
    du = u1 - uL
    H = g["hess"]
    OMi = -ST.OM
    Hdu = np.einsum("ij...,j...->i...", H, du)
    DX = np.einsum("ij,j...->i...", OMi, Hdu)
    Dd = gr.D(du)
    om = gr.omega.reshape(1, 3, 1, 1, 1)
    Et = E + DX - np.sum(Dd * om, axis=1)
    g1 = ST.geom(gr, u1, ST.MU0, 0.0, want_hess=False)
    E1 = g1["E"]
    nE, nEt, nE1, nd = l1(gr, E, rho), l1(gr, Et, rho), l1(gr, E1, rho), l1(gr, du, rho)
    return dict(L=L, S=S, ell=ell, rho=rho, e_ang=float(nE[:3].max()), e_act=float(nE[3:].max()), et_ang=float(nEt[:3].max()),
                et_act=float(nEt[3:].max()), e1_ang=float(nE1[:3].max()), e1_act=float(nE1[3:].max()),
                du_ang=float(nd[:3].max()), du_act=float(nd[3:].max()), sup_E=float(np.abs(E).max()), sup_E1=float(np.abs(E1).max()))


def main():
    d = np.load(sys.argv[1])
    u = d["u"]
    gr = ST.Grid(u.shape[1:])
    rho, ell = 0.02, 0.01
    rows = []
    print("| L | kept terms | |E| ang | |E| act | |Et| ang | |Et| act | |E1| ang | |E1| act | |DK| ang | |DK| act | A = Et/E^2 (ang units) |")
    print("|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|")
    for L in (3, 4, 5, 6, 7, 8):
        t0 = time.time()
        r = run(gr, u, L, rho, ell)
        rows.append(r)
        print("| %d | %d | %.2e | %.2e | %.2e | %.2e | %.2e | %.2e | %.2e | %.2e | %.2e |" % (
            L, r["S"], r["e_ang"], r["e_act"], r["et_ang"], r["et_act"], r["e1_ang"], r["e1_act"], r["du_ang"], r["du_act"],
            max(r["et_ang"], r["et_act"]) / max(r["e_ang"], r["e_act"]) ** 2), flush=True)
    if "--json" in sys.argv:
        json.dump(rows, open(sys.argv[sys.argv.index("--json") + 1], "w"), indent=1)


if __name__ == "__main__":
    main()
