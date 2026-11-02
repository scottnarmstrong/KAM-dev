#!/usr/bin/env python3
"""HD11964-PILOT: grid convergence of the order-3 and order-4 drift rates (untrusted, Apache-2.0).
Usage: conv.py <share> <amd_fraction> <N1xN2,...>.  At the centre with Lambda = Lambda_hat, AMD
amd_fraction * Cmax split share : (1 - share) between c and b, and zero angles, runs the order-4 normal form on each
grid and records the sup of the order-3 and order-4 residuals.  `conv.py 1.0 0.5 224x64,320x64,224x96` (e_c = 0.44,
e_b = 0) writes validation/conv-N4-ec044.json; other arguments write validation/conv-N4-s<share>-f<fraction>.json."""
import json
import os
import sys
import time

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import gate  # noqa: E402
import hd11964_model as HM  # noqa: E402
from normal_form import NormalForm  # noqa: E402

root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
s, famd = float(sys.argv[1]), float(sys.argv[2])
grids = [tuple(map(int, g.split("x"))) for g in sys.argv[3].split(",")]
m = HM.Model()
reg = gate.region(m)
nu = [float(HM.R(x)) for x in m.nu]
mu = float(HM.R(m.mu))
G = [s * reg["Cmax"] * famd, (1 - s) * reg["Cmax"] * famd]
L = reg["Lhat"]
out = {}
for N1, N2 in grids:
    t = time.time()
    nf = NormalForm(nu, mu, N1=N1, N2=N2, N=4)
    nf.setup(*gate.centre(L, G, [0.0, 0.0]))
    nf.run()
    out[f"{N1}x{N2}"] = {Np: [float(np.max(np.abs(R))) for R, _ in nf.residual(Np)] for Np in (3, 4)}
    print(N1, N2, out[f"{N1}x{N2}"], round(time.time() - t), flush=True)
name = "conv-N4-ec044.json" if (s, famd) == (1.0, 0.5) else f"conv-N4-s{s}-f{famd}.json"
with open(os.path.join(root, "validation", name), "w") as fh:
    json.dump(out, fh, indent=1)
