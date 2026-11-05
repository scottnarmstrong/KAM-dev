#!/usr/bin/env python3
"""LOCK-DATA: the routeARefined sites of the N = 65 lock at kp = 4 (untrusted tooling; the kernel runs biteOk).

The bite bounds B are Lean `#eval`s of `balBound (biteData lockN65Box 1 (1/67) b w) l` (scratch file, diagnostic
only, 2026-10-31), rounded up to 1e-3; E1 = ceil(1e6 / expLow)/1e6 at J = 8 (checked by balCheck there).
Certified: delta_0, delta_1, b_0..b_3; classical: delta_2, delta_3 (delta_1 at l = 11: l = 12 changes B by 0.03 %).
"""
from fractions import Fraction as F
import v2_q as V
import sodata3_witness as SW

KP, J = 4, 20
BITES = {("d", 0): (10, F(195861, 200000), F(57760713, 1000)),
         ("d", 1): (11, F(989599, 1000000), F(217274653, 1000)),
         ("b", 0): (8, F(55123, 62500), F(10929640, 1000)),
         ("b", 1): (9, F(939073, 1000000), F(13870905, 1000)),
         ("b", 2): (10, F(968997, 1000000), F(29041724, 1000)),
         ("b", 3): (10, F(196863, 200000), F(100291655, 1000))}


def sites(p):
    d0 = min(F(1), (p["rho"] - p["rhoInf"]) / 6)
    st = {}
    for s in range(KP):
        for tag, b in (("d", F(1, 2) ** s * d0), ("b", min(p["rho"] - 6 * d0 * (1 - F(1, 2) ** s), F(1)))):
            st[(tag, s)] = SW.site_c(p, b, BITES[(tag, s)][2]) if (tag, s) in BITES else V.classical_c(2, 1, J, b)
    return st
