#!/usr/bin/env python3
"""SJS-X1: move a torus state (double 'u' or DD 'C_hi', 'C_lo') to another p grid, keeping the modes inside the new band.

Untrusted design tooling.  Usage: x1_regrid.py IN.npz --grid N1 N2 N3 [--cut 0.45] --out OUT.npz
"""
import argparse, json
import numpy as np


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("src")
    ap.add_argument("--grid", type=int, nargs=3, required=True)
    ap.add_argument("--cut", type=float)
    ap.add_argument("--out", required=True)
    a = ap.parse_args()
    d = np.load(a.src)
    old = tuple(int(x) for x in d["grid"])
    new = tuple(a.grid)
    cut = a.cut if a.cut is not None else float(d["cut"])
    if "C_hi" in d:
        parts = {"C_hi": d["C_hi"], "C_lo": d["C_lo"]}
    else:
        parts = {"C_hi": np.fft.fftn(d["u"], axes=(-3, -2, -1)) / np.prod(old)}
        parts["C_lo"] = np.zeros_like(parts["C_hi"])
    kf = np.meshgrid(*[np.fft.fftfreq(n, 1.0 / n) for n in old], indexing="ij")
    ok = np.ones(old, dtype=bool)
    for i in range(3):
        ok &= np.abs(kf[i]) <= cut * new[i]
    idx = tuple(np.mod(kf[i][ok].astype(int), new[i]) for i in range(3))
    out = {}
    for key, A in parts.items():
        B = np.zeros((6,) + new, dtype=complex)
        for c in range(6):
            B[c][idx] = A[c][ok]
        out[key] = B
    hist = json.loads(str(d["hist"])) if "hist" in d and "C_hi" in d else []
    hist.append(dict(regrid=[list(old), list(new)], cut=cut))
    np.savez(a.out, C_hi=out["C_hi"], C_lo=out["C_lo"], G=d["G"], Fs=d["Fs"], phi=d["phi"], grid=np.array(new), cut=cut,
             hist=json.dumps(hist))
    print("regridded %s -> %s, %d modes kept" % (old, new, int(ok.sum())))


if __name__ == "__main__":
    main()
