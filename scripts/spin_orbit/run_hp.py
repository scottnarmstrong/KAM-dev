#!/usr/bin/env python3
"""Driver: double continuation -> hp chord iteration on 256x64 -> embed -> hp iteration on 512x128 -> pickle state."""
import sys, time, pickle, numpy as np
import dsolve
from hpsolve import HP
from hpfft import P, zeros

def embed(vre, vim, nx, nt, nx2, nt2):
    def e(a):
        out = zeros((nx2, nt2))
        for k in range(-(nx // 2) + 1, nx // 2):
            for l in range(-(nt // 2) + 1, nt // 2):
                out[k % nx2, l % nt2] = a[k % nx, l % nt]
        return out
    return e(vre), e(vim)

def main(which, outdir, stage1_iters=8, stage2_iters=10):
    t0 = time.time(); log = lambda s: print(s, flush=True)
    import os
    cache = f"{outdir}/{which}_v256.npy"
    if os.path.exists(cache):
        G = dsolve.Grid(256, 64, which); v = np.load(cache)
    else:
        G, v = dsolve.continuation(256, 64, which); np.save(cache, v)
    log(f"{which}: double continuation done {time.time()-t0:.0f}s; p range {G.p_of(v).min()!r} {G.p_of(v).max()!r}")
    from model import EPS
    eps = float(EPS)
    H1 = HP(256, 64, which)
    vre, vim = H1.vhat_from_double(v)
    vre, vim, er, ei, h1 = H1.run(vre, vim, v, eps, stage1_iters, tag=f"{which}[256x64]", log=log)
    pickle.dump(dict(vre=vre, vim=vim, hist=h1), open(f"{outdir}/{which}_256.pkl", "wb"))
    H2 = HP(512, 128, which)
    vre, vim = embed(vre, vim, 256, 64, 512, 128)
    # double base for the Jacobian: interpolate from the hp coefficients
    vh = np.zeros((512, 128), dtype=complex)
    for k in range(512):
        for l in range(128):
            if vre[k, l] != 0 or vim[k, l] != 0:
                vh[k, l] = float(vre[k, l] / 2**P) + 1j * float(vim[k, l] / 2**P)
    vbase = np.real(np.fft.ifft2(vh)) * (512 * 128)
    vre, vim, er, ei, h2 = H2.run(vre, vim, vbase, eps, stage2_iters, tag=f"{which}[512x128]", log=log)
    pickle.dump(dict(vre=vre, vim=vim, er=er, ei=ei, hist1=h1, hist2=h2, time=time.time() - t0),
                open(f"{outdir}/{which}_512.pkl", "wb"))
    log(f"{which}: total {time.time()-t0:.0f}s")

if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2], *map(int, sys.argv[3:]))
