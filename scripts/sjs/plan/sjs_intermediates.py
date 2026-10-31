#!/usr/bin/env python3
"""SJS-PLAN: Fourier support of the checker's intermediate models against the support of K, on the coarse torus.

Untrusted design tooling.  The support S was measured on K (sjs_spectrum.py); the certificate's cost is set by the largest model of
the program.  This counts, at the same relative tolerance 10^-L, strip rho, full lattice, the functions along the torus that the
program builds: the Cartesian positions, 1/r, 1/r^3 (the force), the Kepler characters of each planet, and X_H.  These functions
of theta do not depend on the chart.
Usage: python3 -I scripts/sjs/plan/sjs_intermediates.py TORUS.npz [--json OUT]
"""
import json, math, os, sys
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import sjs_torus as ST
import sjs_spectrum as SP
sys.path.pop(0)


def main():
    d = np.load(sys.argv[1])
    u = d["u"]
    gr = ST.Grid(u.shape[1:])
    kk = SP.lattice(gr.shape)
    th = gr.theta_chart()
    z = u.copy(); z[:3] += th
    l1, l2, gh, L1, L2, Gh = z
    G2 = ST.GTOT - Gh
    m1, m2 = ST.M

    def planet(l, g, L, G, m):
        e = np.sqrt(1 - (G / L) ** 2)
        E = ST.kepler_val(l, e)
        a = L * L / m ** 2
        q1 = a * (np.cos(E) - e); q2 = a * (G / L) * np.sin(E)
        return np.cos(g) * q1 - np.sin(g) * q2, np.sin(g) * q1 + np.cos(g) * q2, E, e
    x1, y1, E1, e1 = planet(l1, gh, L1, Gh, m1)
    x2, y2, E2, e2 = planet(l2, 0 * gh, L2, G2, m2)
    r = np.sqrt((x1 - x2) ** 2 + (y1 - y2) ** 2)
    # the (periodic) Kepler character in the torus's frame, the winding removed: e^{i (E - theta)}
    ch1 = np.exp(1j * (E1 - th[0])); ch2 = np.exp(1j * (E2 - th[1]))
    funcs = dict(K_ang=u[0], K_act=u[3], x1=x1 * np.cos(th[0] + th[2]) + y1 * np.sin(th[0] + th[2]), inv_r=1 / r, inv_r3=1 / r ** 3,
                 char1_re=ch1.real, char1_im=ch1.imag, char2_re=ch2.real, char2_im=ch2.imag)
    g, _ = ST.grad_hess(z, ST.MU0, want_hess=False)
    funcs["dH_dl1"] = g[0]
    funcs["dH_dGhat"] = g[5]
    funcs["dH_dL1"] = g[3]
    Ls = (4, 6, 8)
    k1 = sum(np.abs(k) for k in kk)
    out = {}
    print("| function | S(4) | S(6) | S(8) | S(8) / S_K(8) (K = max over the six components) |")
    print("|---|---:|---:|---:|---:|")
    C = SP.fullspec(u)
    Cm = np.max(C / np.max(C.reshape(6, -1)[:, 1:], axis=1).reshape(6, 1, 1, 1), axis=0)
    base = SP.counts(Cm, kk, Ls, [0.02], None)[0.02]
    print("| K (six components) | %d | %d | %d | 1 |" % tuple(base))
    for name, f in funcs.items():
        A = np.abs(np.fft.fftn(f)) / f.size
        s = SP.counts(A, kk, Ls, [0.02], None)[0.02]
        out[name] = s
        print("| %s | %d | %d | %d | %.2f |" % (name, s[0], s[1], s[2], s[2] / base[2]), flush=True)
    if "--json" in sys.argv:
        json.dump(dict(K=base, f=out), open(sys.argv[sys.argv.index("--json") + 1], "w"), indent=1)


if __name__ == "__main__":
    main()
