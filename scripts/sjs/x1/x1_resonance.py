#!/usr/bin/env python3
"""SJS-X1: isolated near-resonant modes of a torus state: coefficients far above the smooth envelope at their order.

Untrusted design tooling.  For each mode of the band with |k.omega| < KW_MAX (theta lattice of SJS-PLAN's torus, omega = FH25's
frequency), prints its normalized coefficient (max over the 'reg' components, each relative to its largest nonconstant
coefficient) and its cluster k + n (2, -5, 2), the great-inequality direction (|(2, -5, 2).omega| = 1.25e-3).
Usage: x1_resonance.py STATE.npz [--kwmax 1e-5] [--json OUT]
"""
import argparse, json, os, sys
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import x1_spectrum as XS
import hsyn as HS
sys.path.pop(0)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("src")
    ap.add_argument("--kwmax", type=float, default=1e-5)
    ap.add_argument("--json")
    a = ap.parse_args()
    C, G, shape, kind, cut = XS.load_coeffs(a.src)
    m = XS.normalized_max(XS.comps(C, "reg"))
    del C
    kp, k = XS.lattice(shape, G)
    band = np.ones(shape, dtype=bool)
    for i in range(3):
        band &= np.abs(kp[i]) <= cut * shape[i]
    kw = np.abs(np.einsum("i...,i->...", k, HS.OMEGA))
    k1 = np.abs(k).sum(axis=0)
    sel = band & (kw < a.kwmax) & (k1 > 0)
    gi = np.array([2, -5, 2])
    gp = np.array(G) @ gi
    out = []
    for idx in zip(*np.nonzero(sel)):
        kk = k[:, idx[0], idx[1], idx[2]]
        if tuple(kk) < tuple(-kk):
            continue
        # the smooth envelope at this |k|_1: the median coefficient of the modes with the same |k|_1 in the band
        same = band & (k1 == k1[idx])
        env = float(np.median(m[same]))
        cl = []
        for n in range(-4, 5):
            q = kp[:, idx[0], idx[1], idx[2]] + n * gp
            if all(abs(q[i]) <= cut * shape[i] for i in range(3)):
                cl.append((n, float(m[tuple(np.mod(q, shape))])))
        rec = dict(k=kk.tolist(), kp=kp[:, idx[0], idx[1], idx[2]].tolist(), k_omega=float(kw[idx]), k1=int(k1[idx]),
                   coefficient=float(m[idx]), envelope_median=env, cluster=cl)
        out.append(rec)
        print("k %-16s |k|_1 %3d |k.w| %.2e  coefficient %.2e  (median at this |k|_1: %.1e)  cluster along (2,-5,2): %s" % (
            rec["k"], rec["k1"], rec["k_omega"], rec["coefficient"], env, " ".join("%+d:%.1e" % t for t in cl)))
    if a.json:
        json.dump(dict(src=os.path.basename(a.src), kwmax=a.kwmax, modes=out), open(a.json, "w"), indent=1)


if __name__ == "__main__":
    main()
