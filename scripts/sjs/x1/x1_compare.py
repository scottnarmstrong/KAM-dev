#!/usr/bin/env python3
"""SJS-X1: two DD tori on different p grids, compared mode by mode on their common band; and their S(L).

Untrusted design tooling.  Usage: x1_compare.py A.npz B.npz SPEC_A.json SPEC_B.json [--json OUT]
"""
import json, os, sys
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import x1_spectrum as XS
sys.path.pop(0)


def main():
    fa, fb, ja, jb = sys.argv[1:5]
    out = {}
    Ca, G, sa, _, cuta = XS.load_coeffs(fa)
    ma = XS.normalized_max(XS.comps(Ca, "reg")); del Ca
    Cb, _, sb, _, cutb = XS.load_coeffs(fb)
    mb = XS.normalized_max(XS.comps(Cb, "reg")); del Cb
    kp = np.stack(np.meshgrid(*[np.fft.fftfreq(n, 1.0 / n) for n in sa], indexing="ij")).astype(int)
    ok = np.ones(sa, dtype=bool)
    for i in range(3):
        ok &= (np.abs(kp[i]) <= cuta * sa[i]) & (np.abs(kp[i]) <= cutb * sb[i])
    a = ma[ok]
    b = mb[tuple(np.mod(kp[i][ok], sb[i]) for i in range(3))]
    rows = []
    print("modes of the common band, by size (normalized max over the reg components):")
    for L in range(4, 29, 2):
        sel = (np.maximum(a, b) >= 10.0 ** -L) & (np.maximum(a, b) < 10.0 ** -(L - 2))
        if not sel.any():
            continue
        rel = np.abs(a[sel] - b[sel]) / np.maximum(a[sel], b[sel])
        r = dict(range="1e-%d..1e-%d" % (L, L - 2), n=int(sel.sum()), median=float(np.median(rel)), p99=float(np.percentile(rel, 99)),
                 max=float(rel.max()))
        rows.append(r)
        print("  |c| in [1e-%d, 1e-%d): %8d modes, relative difference median %.1e, 99th pct %.1e, max %.1e" % (
            L, L - 2, r["n"], r["median"], r["p99"], r["max"]))
    out["modes"] = rows
    A = json.load(open(ja)); B = json.load(open(jb))
    print("S(L), reg components, strip 0.02:  A %s  B %s" % (A["grid"], B["grid"]))
    out["S"] = []
    for L, x, y in zip(A["Ls"], A["reg"]["S"]["0.02"], B["reg"]["S"]["0.02"]):
        out["S"].append((L, x, y))
        print("  L %2d  %8d  %8d  ratio %.4f" % (L, x, y, y / x))
    if len(sys.argv) > 6 and sys.argv[5] == "--json":
        json.dump(out, open(sys.argv[6], "w"), indent=1)


if __name__ == "__main__":
    main()
