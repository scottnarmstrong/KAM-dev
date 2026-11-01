#!/usr/bin/env python3
"""HD11964-PILOT high-precision leg (untrusted, Apache-2.0): the same normal form and residual in 80-bit long double
(explicit DFTs) against float64, at the same centre and grid; plus the mass-scaling test (residual of order N must
scale like mu^(N+1) if it is not a rounding floor).  Writes validation/hiprec.json."""
import json
import os
import sys
import time

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import gate  # noqa: E402
import hd11964_model as HM  # noqa: E402
from normal_form import NormalForm  # noqa: E402

N = int(sys.argv[1])
s = float(sys.argv[2])
N1, N2 = int(sys.argv[3]), int(sys.argv[4])
m = HM.Model()
reg = gate.region(m)
nu = [float(HM.R(x)) for x in m.nu]
mu = float(HM.R(m.mu))
G = [s * reg["Cmax"], (1 - s) * reg["Cmax"]]
L = reg["Lhat"]
out = dict(N=N, share=s, grid=[N1, N2], runs={})
for name, long, scale in (("double", False, 1.0), ("long", True, 1.0), ("double_mu/2", False, 0.5)):
    t = time.time()
    nf = NormalForm(nu, mu * scale, N1=N1, N2=N2, N=N, long=long)
    c = gate.centre(L, G, [0.0, 0.0])
    if long:
        c = tuple([np.longdouble(x) for x in v] for v in c)
    nf.setup(*c)
    nf.run()
    out["runs"][name] = {Np: [float(np.max(np.abs(R))) for R, _ in nf.residual(Np)] for Np in range(N + 1)}
    out["runs"][name]["secs"] = time.time() - t
    print(name, out["runs"][name], flush=True)
d, l, h = out["runs"]["double"], out["runs"]["long"], out["runs"]["double_mu/2"]
out["rel_diff_long_double"] = {Np: [abs(l[Np][i] - d[Np][i]) / l[Np][i] for i in range(2)] for Np in range(N + 1)}
out["mu_scaling_ratio"] = {Np: [d[Np][i] / h[Np][i] for i in range(2)] for Np in range(N + 1)}
out["mu_scaling_expected"] = {Np: 2 ** (Np + 1) for Np in range(N + 1)}
print(json.dumps({k: out[k] for k in ("rel_diff_long_double", "mu_scaling_ratio")}, indent=1))
root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
with open(os.path.join(root, "validation", f"hiprec-N{N}-s{s}.json"), "w") as fh:
    json.dump(out, fh, indent=1)
