#!/usr/bin/env python3
"""HD11964-PILOT: which Fourier cutoff K_c (inner angle) the normal form needs (untrusted, Apache-2.0).
Solve only modes with |k_c| <= K (all |k_b| of the box) and record the order-N residual at the e_c-max corner."""
import json
import os
import sys

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import gate  # noqa: E402
import hd11964_model as HM  # noqa: E402
from normal_form import NormalForm  # noqa: E402

N = int(sys.argv[1])
s = float(sys.argv[2])
Ks = [int(x) for x in sys.argv[3].split(",")]
m = HM.Model()
reg = gate.region(m)
nu = [float(HM.R(x)) for x in m.nu]
mu = float(HM.R(m.mu))
G = [s * reg["Cmax"], (1 - s) * reg["Cmax"]]
L = reg["Lhat"]
e0, e1 = gate.ecc(L[0], G[0]), gate.ecc(L[1], G[1])
N1, N2 = gate.grid_for(e0, e1, [(L[i] / nu[i]) ** 2 for i in range(2)])
out = dict(N=N, share=s, e=[e0, e1], grid=[N1, N2], K={})
for K in Ks:
    nf = NormalForm(nu, mu, N1=N1, N2=N2, N=N, K1solve=K)
    nf.setup(*gate.centre(L, G, [0.0, 0.0]))
    nf.run()
    out["K"][K] = {Np: [float(np.max(np.abs(R))) for R, _ in nf.residual(Np)] for Np in range(1, N + 1)}
    print(K, out["K"][K], flush=True)
root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
with open(os.path.join(root, "validation", f"kscan-N{N}-s{s}.json"), "w") as fh:
    json.dump(out, fh, indent=1)
