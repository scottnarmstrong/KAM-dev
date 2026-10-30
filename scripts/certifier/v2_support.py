#!/usr/bin/env python3
"""SHARP-CERTSIDE: the truncation (support) the v2 mirror needs on the lunar candidates.

Untrusted design tooling.  For re-truncated rotated candidates (L digits, SO-GEN2's bit rule), T/e under
SHARP-PLUS's v2 mirror (variant A7, through v2_adapter.py) and under v1, corner regime, c = 7/4, mu = 1/160, at a few
strip widths.  Usage: python3 -I scripts/certifier/v2_support.py CACHE_DIR [L ...]
"""
import sys, os
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from lunar_oracle import LunarOracle           # noqa: E402
from optimize import package, evaluate, ROT     # noqa: E402
import v2_adapter as V2                          # noqa: E402

cache = sys.argv[1]
Ls = [int(x) for x in sys.argv[2:]] or [16, 18, 20, 24]
c, mu = 7 / 4, 1 / 160
for L in Ls:
    for which in ("lower", "upper"):
        O = LunarOracle(which, cache, log=lambda *a: None, L=L)
        cells = []
        for rho in (0.01, 1 / 70, 0.02):
            nm = O.norms(np.eye(2), 1.0, rho, regimes=("corner",))
            pkg = package(O, nm, "corner", ROT, 1.0, c, rho, mu)
            pkg["extras"] = V2.extras(O, ROT, 1.0, c, rho)
            T2 = V2.log10_threshold(pkg)
            T1, le, r1, _ = evaluate(package(O, nm, "corner", ROT, 1.0, c, rho, mu, theorem="v1"), "v1")
            cells.append("rho %.4f: log e %.2f | v2 T %.2f T/e %+.2f | v1 T/e %+.2f" % (rho, le, T2, T2 - le, r1))
        print("L %d %s: %s" % (L, which, " || ".join(cells)), flush=True)
