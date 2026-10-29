"""Residual coefficients of the truncated candidate at many truncation levels; saved as numpy arrays.
Mirrors scripts/spin_orbit/analyze.py (exact Fraction/Q(sqrt5) residual), but keeps per-mode |rho_kappa|."""
import json, sys, time, mpmath, numpy as np, pickle
from exact_residual import residual
mpmath.mp.prec = 900
which = sys.argv[1]
d = json.load(open('/root/code/KAM/certificates/lunar-spin-orbit/%s.json' % which)); P = d["scale_bits"]
b0 = {(k, l): int(n) for k, l, n in d["v_sin"]}; E0 = {(k, l): int(n) for k, l, n in d["E_re"]}
s5 = mpmath.sqrt(5)
out = {}
for L in list(range(20, 131, 5)):
    ti = int(mpmath.ceil(mpmath.mpf(10) ** (-L) * mpmath.mpf(2) ** P))
    b = {k: n for k, n in b0.items() if abs(n) >= ti}; E = {k: n for k, n in E0.items() if abs(n) >= ti}
    t0 = time.time()
    rho = residual(b, E, P, which)
    ks = np.array([k for (k, l) in rho]); ls = np.array([l for (k, l) in rho])
    mags = []
    for (k, l), (x, y) in rho.items():
        v = abs(mpmath.mpf(x.numerator) / x.denominator + s5 * mpmath.mpf(y.numerator) / y.denominator)
        mags.append(float(mpmath.log10(v)) if v > 0 else -1e9)
    vb = np.array(list(b.keys())); eb = np.array(list(E.keys()))
    out[L] = dict(nv=len(b), nE=len(E), k=ks, l=ls, log10mag=np.array(mags),
                  vbox=(int(np.abs(vb[:,0]).max()), int(np.abs(vb[:,1]).max())))
    print(which, L, len(b), len(E), len(rho), round(time.time() - t0, 1), flush=True)
pickle.dump(out, open('trunc_%s.pkl' % which, 'wb'))
