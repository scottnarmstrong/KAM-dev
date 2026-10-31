#!/usr/bin/env python3
"""SJS-PLAN: diagnostics for the continuation of sjs_torus.py: Newton history at one mu, largest residual modes, spectrum."""
import sys, os, time
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import sjs_torus as S
sys.path.pop(0)

grid = tuple(int(x) for x in sys.argv[1:4])
mu_stop = float(sys.argv[4])
steps = int(sys.argv[5])
gr = S.Grid(grid)
u = S.initial(gr)
lam = float(S.OMEGA[2])
us, lams = [], []
for j in range(1, steps + 1):
    mu = mu_stop * j / steps
    if len(us) == 2:
        u = 2 * us[1] - us[0]; lam = 2 * lams[1] - lams[0]
    for it in range(3):
        u, lam, info = S.newton(gr, u, lam, mu, "translated", S.GHAT0)
    us = (us + [u.copy()])[-2:]; lams = (lams + [lam])[-2:]
print("reached mu", mu, "err", info["err"], flush=True)
for it in range(6):
    u, lam, info = S.newton(gr, u, lam, mu, "translated", S.GHAT0)
    print("  it", it, "err %.3e du %.3e dlam %.3e" % (info["err"], info["du"], info["dlam"]), flush=True)
g = S.geom(gr, u, mu, lam, want_hess=False)
for name, a in (("E", g["E"]), ("u", u)):
    A = np.abs(gr.f(a)) / np.prod(grid)
    A[..., 0, 0, 0] = 0
    A = A.max(axis=0)
    idx = np.argsort(A.ravel())[::-1][:8]
    print(name, "top modes:")
    for i in idx:
        c = np.unravel_index(i, A.shape)
        print("   k", [int(gr.k[d][c[d]]) for d in range(3)], "%.3e" % A[c], "k.w %.3e" % gr.kw[c])
    for ax in range(3):
        kk = np.abs(gr.k[ax])
        m = [float(np.max(np.take(A, np.where(kk == v)[0], axis=ax))) for v in sorted(set(kk))]
        print("   axis", ax, "max per |k|:", " ".join("%.0e" % x for x in m[::max(1, len(m) // 14)]))
