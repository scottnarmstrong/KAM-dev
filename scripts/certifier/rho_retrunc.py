#!/usr/bin/env python3
"""SHARP-CERTSIDE: the strip width that minimizes support once the candidate is truncated for the sharp threshold.

Untrusted design tooling.  For truncations L (digits; S = ceil(3.33 L) + 24 bits, SO-GEN2's rule) of the rotated
lunar candidate, T/e under v1 (corner regime, rotated frame, lam = 1, c = 237/125, mu re-optimized) as a function of
rho.  The optimizer's preference for small rho at L = 88 is an artefact of the over-resolved data.
Usage: python3 -I scripts/certifier/rho_retrunc.py CACHE_DIR [L ...]
"""
import sys, os
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from lunar_oracle import LunarOracle           # noqa: E402
from optimize import package, evaluate, ROT     # noqa: E402

cache = sys.argv[1]
Ls = [int(x) for x in sys.argv[2:]] or [28, 32, 36, 88]
rhos = [0.004, 0.0054, 0.008, 0.0107, 1 / 70, 0.02, 0.03, 0.04]
print("T/e (orders), v1 iso, corner regime, c = 237/125, mu optimized; columns rho")
print("| L | " + " | ".join("%.4f" % r for r in rhos) + " |")
for L in Ls:
    for which in ("lower", "upper"):
        O = LunarOracle(which, cache, log=lambda *a: None, L=L)
        row = []
        for rho in rhos:
            nm = O.norms(np.eye(2), 1.0, rho, regimes=("corner",))
            best = max(evaluate(package(O, nm, "corner", ROT, 1.0, 237 / 125, rho, mu, theorem="v1"), "v1")[2]
                       for mu in np.geomspace(1e-4, 0.05, 30))
            row.append(best)
        print("| %d %s | " % (L, which) + " | ".join("%+.2f" % x for x in row) + " |", flush=True)
