#!/usr/bin/env python3
"""Support statistics and exact residual of truncated candidate data (exact_residual.py), per threshold.

usage: analyze.py data.json [out.json]
Truncation: coefficients with |N|/2^P < thr dropped from v and from E independently (absolute threshold).
The reported residual is the exact (Fraction/Q(sqrt5)) Fourier residual rho of exact_residual.py:
sum |rho| over the full lattice, the weighted sum with e^{2 pi (0.01|k| + 0.005|l|)} (rotating strip of the
rho = 1/200 package: |Im psi| <= 2 rho, |Im phi| <= rho) and the pi-restored scalar residual r = 2 pi R.
"""
import json, sys, time, mpmath
from exact_residual import residual, weighted_l1

THRS = ["1e-30", "1e-60", "1e-110", "1e-130"]

def main(path, out=None):
    d = json.load(open(path)); P = d["scale_bits"]
    b0 = {(k, l): int(n) for k, l, n in d["v_sin"]}; E0 = {(k, l): int(n) for k, l, n in d["E_re"]}
    res = {}
    for t in THRS:
        ti = int(mpmath.ceil(mpmath.mpf(t) * mpmath.mpf(2) ** P))
        b = {k: n for k, n in b0.items() if abs(n) >= ti}; E = {k: n for k, n in E0.items() if abs(n) >= ti}
        t0 = time.time()
        rho = residual(b, E, P, d["which"])
        tw, tu, mx = weighted_l1(rho)
        res[t] = dict(v_terms_half=len(b), E_terms=len(E), rho_terms_half=len(rho),
                      sum_abs_R=mpmath.nstr(tu, 8), weighted_abs_R=mpmath.nstr(tw, 8),
                      weighted_abs_r_2piR=mpmath.nstr(tw * 2 * mpmath.pi, 8), max_abs_R=mpmath.nstr(mx, 8),
                      seconds=round(time.time() - t0, 1))
        print(d["which"], t, res[t], flush=True)
    if out: json.dump(res, open(out, "w"), indent=1)

if __name__ == "__main__":
    main(*sys.argv[1:])
