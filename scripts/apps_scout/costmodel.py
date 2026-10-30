#!/usr/bin/env python3
"""Projected kernel cost of a torus certificate, calibrated on the SO measurements.

Unit: one lunar torus at package R1 (S0 = 8.4k E-terms, 318 bits, w0 = 654, 3 full products + 125 low-precision products, SO-ADVCOUNT).  Measured or modelled costs of that unit:
  P  after SO-PACKFIX (D34)     7.5-14.5 CPU-h per torus (OVERNIGHT 11:29: one blockRows-32 shard measured at 4.55 GB, +45 s; projection 15-29 CPU-h for both tori, shard
                                kernel time only: composition, Gram and torsion not yet measured on the fixed code).  THIS IS THE HEADLINE TIER.
  A  landed code before D34     50-85 CPU-h per torus (SO-DATA-2, blockRows 4, 9.1-9.4k shards; measured on one shard, projected to all)
  B  D34 fix F1 + F2            12.5-32.5 CPU-h per torus (SO-KPERF projection from measured parts: 25-65 for both tori)
  C  D34 fix + F2', big blocks  2.5-7.5 CPU-h per torus (SO-KPERF model, 5-15 for both tori; not measured end to end)
  D  SO-REPLAY2 model           0.10-0.15 CPU-h per torus (SO-ADVCOUNT; contradicted ~50x by SO-DATA-2 for the landed code)

Scaling.  Per-slot kernel cost from SO-REPLAY2: t(w) = 0.05 + 0.1 w/896 ms, w = 2 b + 16.  Packed products are bounded by the box, so a product of support S costs slots(S) t(w).
box/support for a diamond is 2 at n = 2 and 6 at n = 3; `box_factor` is relative to the lunar unit, so 3 at n = 3.  Number of products: a full-precision product count N_full per torus and a low
precision count N_low.  The torsion/Gram stage (72 bits, support at 17 digits) is common to all clients: 125 products at n = 2 in SO-ADVCOUNT; its share of the unit is 1/3 (kernel column of SO-ADVCOUNT).
Data volume: advice about 4 MB per lunar torus, scaling like S * b (+ 1 MB embedding); elaboration 18 s/MB.
"""
import math

S0, B0 = 8400.0, 318.0
N_FULL0, N_LOW0 = 3.0, 125.0
SHARE_FULL, SHARE_LOW = 0.66, 0.34
UNIT = dict(P=(7.5, 14.5), A=(50, 85), B=(12.5, 32.5), C=(2.5, 7.5), D=(0.10, 0.15))
ADV0_MB = 4.0


def bits(L):
    """S = ceil(3.33 L) + 24 (SO-GEN2)."""
    return 3.33 * L + 24


def tw(b):
    return 0.05 + 0.1 * (2 * b + 16) / 896


def ratio(S, L, Nfull, S_low=None, Nlow=125, box_factor=1.0):
    """cost of the certificate in units of one lunar torus at R1."""
    b = bits(L)
    full = SHARE_FULL * (Nfull / N_FULL0) * (S / S0) * box_factor * tw(b) / tw(B0)
    if S_low is None:
        S_low = 0.5 * S0 * (17.0 / 88) ** 2 * (S / (S0 * (L / 88.0) ** 2))   # the same alpha at the 17 digits of cfgLow
    low = SHARE_LOW * (Nlow / N_LOW0) * (S_low / (S0 * (17.0 / 88) ** 2 * 0.5)) * box_factor
    return full + low


def project(S, L, Nfull, Nlow=125, tori=1, box_factor=1.0):
    r = ratio(S, L, Nfull, None, Nlow, box_factor) * tori
    adv = ADV0_MB * (S / S0) * (bits(L) / B0) * (Nfull / N_FULL0) * tori
    return dict(ratio=r, cpuh={k: (v[0] * r, v[1] * r) for k, v in UNIT.items()}, advice_MB=adv, elab_min=adv * 18 / 60 / tori)


if __name__ == "__main__":
    print("lunar R1, check:", project(8400, 88, 3)["ratio"])
    for S, L, N in ((1100, 32, 3), (4000, 40, 8), (1100, 34, 25), (30000, 47, 60)):
        p = project(S, L, N)
        print(S, L, N, round(p["ratio"], 2), {k: (round(v[0], 1), round(v[1], 1)) for k, v in p["cpuh"].items()}, round(p["advice_MB"], 1))
