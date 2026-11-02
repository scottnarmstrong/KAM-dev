#!/usr/bin/env python3
"""HD11964-PILOT: analyticity radii of planet c's chart in its slow variables (untrusted, Apache-2.0).
Expands the chart (q, p) of c to degree 12 in (Lambda, xi, eta) at e_c in {0.1, ..., 0.61}, takes the sup over 256
mean longitudes of the pure-power coefficients, and estimates each radius by a root test on the last four degrees.
Used to size the cells of the cover (design section 8).  Writes validation/slow-radius.json."""
import json
import math
import os
import sys

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import hd11964_model as HM  # noqa: E402
from jets import Space  # noqa: E402
from normal_form import chart_planet  # noqa: E402

root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
m = HM.Model()
nu = float(HM.R(m.nu[0]))
L0 = float(m.Lam(0))
D = 12
S = Space(3, D)
lam = 2 * math.pi * np.arange(256) / 256
out = {}
for e in (0.1, 0.3, 0.45, 0.55, 0.61):
    G = L0 * (1 - math.sqrt(1 - e * e))
    xi = math.sqrt(2 * G)
    q, p = chart_planet(S, nu, lam, L0, xi, 0.0, 0, 1, 2)
    rows = {}
    for name, v in (("Lam", 0), ("xi", 1), ("eta", 2)):
        sz = []
        for k in range(D + 1):
            ex = [0, 0, 0]
            ex[v] = k
            i = S.idx[tuple(ex)]
            sz.append(max(float(np.max(np.abs(x.c[i]))) for x in (q[0], q[1], p[0], p[1])))
        R = [(sz[k - 4] / sz[k]) ** 0.25 if sz[k] > 0 else float("inf") for k in range(D - 3, D + 1)]
        rows[name] = float(np.median(R))
    out[e] = dict(xi=xi, R_Lam=rows["Lam"], R_xi=rows["xi"], R_eta=rows["eta"])
    print(e, round(xi, 4), {k: round(v, 4) for k, v in out[e].items()})
with open(os.path.join(root, "validation", "slow-radius.json"), "w") as fh:
    json.dump(out, fh, indent=1)
