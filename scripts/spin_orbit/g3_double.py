#!/usr/bin/env python3
"""SO-GEN3: double-precision continuation of one rotated-frame torus at barrier N (env SO_N), saved for analysis.

    SO_N=50 python3 g3_double.py lower|upper OUTDIR [nx nt]
Writes OUTDIR/N<N>_<which>_v<nx>.npy and prints convergence, the p range and the residual.  Untrusted tooling."""
import sys, time, json, numpy as np
import dsolve, model
from model import EPS

def main(which, outdir, nx=256, nt=64):
    t = time.time(); nx, nt = int(nx), int(nt)
    G, v = dsolve.continuation(nx, nt, which)
    r = G.odd(G.proj(G.resid(v, float(EPS))))
    p = G.p_of(v)
    np.save("%s/N%d_%s_v%d.npy" % (outdir, model.N_BARRIER, which, nx), v)
    out = dict(N=model.N_BARRIER, which=which, nx=nx, nt=nt, pmin=float(p.min()), pmax=float(p.max()),
               resid=float(np.abs(r).max()), seconds=round(time.time() - t, 1))
    print(json.dumps(out), flush=True)

if __name__ == "__main__":
    main(*sys.argv[1:])
