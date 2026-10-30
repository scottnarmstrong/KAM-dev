#!/usr/bin/env python3
"""SO-GEN3: Fourier decay, analyticity width and truncation projection of a double-precision torus (g3_double.py).

    python3 g3_analyze.py V.npy N which
Fits log10 max_l |b_{k,l}| ~ a_k - d_k |k| and log10 max_k |b_{k,l}| ~ a_l - d_l |l| on the coefficients above
1e-12 (double precision floor ~1e-15), gives the widths rho_k = d_k ln10/(2 pi), rho_l = d_l ln10/(2 pi) (the
torus is analytic on |Im psi| < rho_k, |Im phi| < rho_l), and projects the half-lattice count of |b| >= 10^-L
with the anisotropic model  log10|b| <= a - d_k|k| - d_l|l| (calibrated on N = 40 against the 440-bit data).
Untrusted tooling."""
import sys, json, math, numpy as np
import model, dsolve

def analyze(path, which):
    v = np.load(path); nx, nt = v.shape
    vh = np.abs(np.fft.fft2(v)) / v.size * 2          # |b| of the sin series (b = 2|vhat|)
    ks = np.fft.fftfreq(nx, 1 / nx).astype(int); ls = np.fft.fftfreq(nt, 1 / nt).astype(int)
    lg = np.log10(np.maximum(vh, 1e-300))
    mk = {}; ml = {}
    for a in range(nx):
        for c in range(nt):
            k, l = abs(ks[a]), abs(ls[c])
            mk[k] = max(mk.get(k, -300), lg[a, c]); ml[l] = max(ml.get(l, -300), lg[a, c])
    def fit(m, lo):
        xs = [x for x in sorted(m) if x >= lo and m[x] > -12]
        ys = [m[x] for x in xs]
        d, a = np.polyfit(xs, ys, 1)
        return -d, a, xs[-1] if xs else None
    dk, ak, kfit = fit(mk, 4)
    dl, al, lfit = fit(ml, 2)
    G = dsolve.Grid(nx, nt, which)
    p = G.p_of(v)
    a0 = max(ak, al)
    def count(L):
        # half lattice points with a0 - dk|k| - dl|l| >= -L
        n = 0
        for k in range(0, int((a0 + L) / dk) + 2):
            r = (a0 + L - dk * k) / dl
            if r < 0: continue
            n += (2 * int(r) + 1) if k > 0 else int(r)
        return n
    rk = dk * math.log(10) / (2 * math.pi); rl = dl * math.log(10) / (2 * math.pi)
    return dict(N=model.N_BARRIER, which=which, pmin=float(p.min()), pmax=float(p.max()),
                band=float(max(abs(p.min() - 1), abs(p.max() - 1))), inner=float(min(abs(p.min() - 1), abs(p.max() - 1))),
                digits_per_k=dk, digits_per_l=dl, rho_k=rk, rho_l=rl, a0=a0,
                max_b=float(vh.max()), count_model={L: count(L) for L in (25, 28, 30, 32, 35, 40, 88)},
                shell_k={k: round(mk[k], 2) for k in (10, 20, 30, 40, 60, 80) if k in mk},
                shell_l={l: round(ml[l], 2) for l in (2, 5, 8, 10, 15) if l in ml})

if __name__ == "__main__":
    print(json.dumps(analyze(sys.argv[1], sys.argv[3]), default=str))
