#!/usr/bin/env python3
"""HD11964-PILOT numerical gate: sampled sup of the drift rate |{F_i, H}| and of F_i - Lam_i over the certificate region.

Untrusted design tooling (Apache-2.0).  numpy, mpmath.  Heavy: run under the memory cap, e.g.
  systemd-run --user --scope -p MemoryMax=8G -p MemorySwapMax=0 nice -n 10 \
      python3 -I applications/hd11964/scripts/gate.py --procs 4 --out applications/hd11964/validation/gate-samples.jsonl

Region R(d) (design doc, section 3): |Lam_i - Lamhat_i| <= rho_i + d, Gamma_0 + Gamma_1 <= Cbar + 2 d, all fast angles,
all perihelia.  Rotation invariance (H, Lam and the construction are invariant under the common rotation) fixes
varpi_1 = 0.  Every centre is a full fast-angle grid; slow points and actions are sampled (label `estimated`).
"""
import argparse
import json
import math
import os
import sys
import time

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import hd11964_model as HM  # noqa: E402
from normal_form import NormalForm  # noqa: E402


def region(m, d=1e-3, Cbar=0.0100, rho=(1e-4, 3e-3)):
    Lhat = [float(m.Lam(i)) for i in range(2)]
    Cmax = Cbar + 2 * d
    Lmin = [Lhat[i] - rho[i] - d for i in range(2)]
    emax = [math.sqrt(1 - (1 - Cmax / Lmin[i]) ** 2) if Cmax < Lmin[i] else 1.0 for i in range(2)]
    delta = Lmin[0] + d - Cbar  # margin of the initial set: min Lam_0(z0) - max C(z0)
    return dict(d=d, Cbar=Cbar, rho=list(rho), Lhat=Lhat, Cmax=Cmax, Lmin=Lmin, emax=emax, delta=delta,
                r_helper=delta / 12)


def centre(Lam, G, varpi):
    xi = [math.sqrt(2 * G[i]) * math.cos(varpi[i]) for i in range(2)]
    eta = [math.sqrt(2 * G[i]) * math.sin(varpi[i]) for i in range(2)]
    return list(Lam), xi, eta


def ecc(Lam, G):
    return math.sqrt(max(0.0, 1 - (1 - G / Lam) ** 2))


def grid_for(e0, e1, a=None, fine=False):
    """Grid from the decay of the harmonics.  Inner angle: the analyticity strip of the Kepler solution,
    sigma(e) = ln((1+s)/e) - s, s = sqrt(1-e^2).  Outer angle: min(sigma(e_1), ln(1/alpha)), alpha the largest
    axis ratio r_0/r_1 = a_0(1+e_0)/(a_1(1-e_1)) (the pair harmonics in lam_1 decay like the multipole order)."""
    def sig(e):
        if e < 1e-9:
            return 50.0
        s = math.sqrt(1 - e * e)
        return math.log((1 + s) / e) - s
    tol = 40.0 if not fine else 60.0
    k1 = int(math.ceil(tol / sig(e0)))
    s2 = sig(e1)
    if a is not None:
        al = a[0] * (1 + e0) / (a[1] * (1 - e1))
        s2 = min(s2, math.log(1 / al))
    k2 = int(math.ceil(tol / s2))
    N1 = 16 * int(math.ceil((3 * k1 + 3) / 16))
    N2 = 16 * int(math.ceil((3 * k2 + 3) / 16))
    return max(64, min(N1, 1024)), max(32, min(N2, 192))


def run_one(task):
    nu, mu, N, Lam, G, varpi, fine, tag = task
    e0, e1 = ecc(Lam[0], G[0]), ecc(Lam[1], G[1])
    a = [(Lam[i] / nu[i]) ** 2 for i in range(2)]
    N1, N2 = grid_for(e0, e1, a, fine)
    t0 = time.time()
    nf = NormalForm(nu, mu, N1=N1, N2=N2, N=N)
    nf.setup(*centre(Lam, G, varpi))
    nf.run()
    out = dict(tag=tag, Lam=Lam, G=G, varpi=varpi, e=[e0, e1], N1=N1, N2=N2, orders={})
    for Np in range(N + 1):
        rr = nf.residual(Np)
        out["orders"][Np] = dict(rate=[float(np.max(np.abs(a))) for a, _ in rr],
                                 Gmin=[float(np.min(g)) for _, g in rr], Gmax=[float(np.max(g)) for _, g in rr])
    # spectrum of the order-N residual: tail of the exact f beyond the solved box (diagnostic)
    out["secs"] = time.time() - t0
    return out


def tasks(m, reg, N, nshare=(0.0, 0.15, 0.3, 0.5, 0.7, 0.85, 1.0), nang=6, interior=(0.0, 0.5), corners=True):
    nu = [float(HM.R(x)) for x in m.nu]
    mu = float(HM.R(m.mu))
    Lc = reg["Lhat"]
    out = []
    Cm = reg["Cmax"]
    for s in nshare:
        angs = [0.0] if s in (0.0, 1.0) else [2 * math.pi * a / nang for a in range(nang)]
        for a in angs:
            out.append((nu, mu, N, Lc, [s * Cm, (1 - s) * Cm], [a, 0.0], False, f"sphere s={s} dw={a:.3f}"))
    for f in interior:
        for s in (0.0, 0.5, 1.0):
            out.append((nu, mu, N, Lc, [s * f * Cm, (1 - s) * f * Cm], [math.pi / 2, 0.0], False,
                        f"interior f={f} s={s}"))
    for s in (1.0, 0.85):
        out.append((nu, mu, N, Lc, [s * Cm, (1 - s) * Cm], [math.pi / 3, 0.0], True, f"fine s={s}"))
    if corners:
        w = [reg["rho"][i] + reg["d"] for i in range(2)]
        for sg0 in (-1, 1):
            for sg1 in (-1, 1):
                L = [Lc[0] + sg0 * w[0], Lc[1] + sg1 * w[1]]
                for s in (0.0, 1.0):
                    out.append((nu, mu, N, L, [s * Cm, (1 - s) * Cm], [0.0, 0.0], False,
                                f"corner {sg0:+d}{sg1:+d} s={s}"))
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--N", type=int, default=3)
    ap.add_argument("--d", type=float, default=1e-3)
    ap.add_argument("--Cbar", type=float, default=0.0100)
    ap.add_argument("--procs", type=int, default=2)
    ap.add_argument("--out", default=None)
    ap.add_argument("--quick", action="store_true")
    a = ap.parse_args()
    m = HM.Model()
    reg = region(m, d=a.d, Cbar=a.Cbar)
    print(json.dumps(reg), flush=True)
    ts = tasks(m, reg, a.N)
    if a.quick:
        ts = ts[:: max(1, len(ts) // 6)]
    out = open(a.out, "a") if a.out else None
    if out:
        out.write(json.dumps(dict(region=reg, N=a.N)) + "\n")
    import multiprocessing as mpc
    with mpc.get_context("fork").Pool(a.procs, maxtasksperchild=1) as pool:
        for r in pool.imap_unordered(run_one, ts):
            last = r["orders"][a.N]
            print(f'{r["tag"]:28s} e=({r["e"][0]:.3f},{r["e"][1]:.3f}) grid {r["N1"]}x{r["N2"]} '
                  + " ".join(f'N{k}:{max(v["rate"]):.2e}' for k, v in r["orders"].items())
                  + f' osc={[round(last["Gmax"][i] - last["Gmin"][i], 8) for i in range(2)]} {r["secs"]:.0f}s',
                  flush=True)
            if out:
                out.write(json.dumps(r) + "\n")
                out.flush()


if __name__ == "__main__":
    main()
