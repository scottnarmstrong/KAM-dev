#!/usr/bin/env python3
"""HD11964-PILOT rigorous-design estimate (untrusted, Apache-2.0).

A certificate bounds sup_lam |R| by the l1 (Wiener) norm of the Fourier coefficients of R plus radii, and the range
of G = F - Lam by twice the l1 norm of its oscillating part.  At given centres this measures the loss factors
W(R)/sup|R| per order and the l1 range bound of G against its sampled range.  Writes validation/rigor.json.
"""
import json
import math
import os
import sys

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import gate  # noqa: E402
import hd11964_model as HM  # noqa: E402
from normal_form import NormalForm  # noqa: E402

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


def wiener(a):
    c = np.fft.fft2(a) / a.size
    return float(np.sum(np.abs(c)))


def main():
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 3
    shares = [float(x) for x in sys.argv[2].split(",")] if len(sys.argv) > 2 else [0.0, 0.5, 1.0]
    m = HM.Model()
    reg = gate.region(m)
    nu = [float(HM.R(x)) for x in m.nu]
    mu = float(HM.R(m.mu))
    out = []
    for s in shares:
        G = [s * reg["Cmax"], (1 - s) * reg["Cmax"]]
        L = reg["Lhat"]
        e0, e1 = gate.ecc(L[0], G[0]), gate.ecc(L[1], G[1])
        a = [(L[i] / nu[i]) ** 2 for i in range(2)]
        N1, N2 = gate.grid_for(e0, e1, a)
        nf = NormalForm(nu, mu, N1=N1, N2=N2, N=N)
        nf.setup(*gate.centre(L, G, [0.0, 0.0]))
        nf.run()
        row = dict(share=s, e=[e0, e1], grid=[N1, N2], orders={})
        for Np in range(N + 1):
            rr = nf.residual(Np)
            row["orders"][Np] = dict(
                sup=[float(np.max(np.abs(R))) for R, _ in rr],
                wiener=[wiener(R) for R, _ in rr],
                G_range=[float(np.ptp(g)) for _, g in rr],
                G_l1_range=[2 * (wiener(g) - abs(float(np.mean(g)))) for _, g in rr])
            o = row["orders"][Np]
            o["factor"] = [o["wiener"][i] / o["sup"][i] if o["sup"][i] > 0 else None for i in range(2)]
        out.append(row)
        print(json.dumps(row), flush=True)
    with open(os.path.join(ROOT, "validation", f"rigor-N{N}.json"), "w") as fh:
        json.dump(out, fh, indent=1)


if __name__ == "__main__":
    main()
