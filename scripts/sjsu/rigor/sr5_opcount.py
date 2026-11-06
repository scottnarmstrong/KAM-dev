#!/usr/bin/env python3
"""SR-5 OPCOUNT: price SR-4's straight-line program with sjs-plan's packed-kernel laws (standard library only).

Input: results/<sr4 tag>.json and results/<sr4 tag>-ops.json, the multiset of 2-D Fourier products
(stage, kind, support cA, support cB) and the number of truncations (unpacks) SR-4 performed.
Laws (docs/explorations/sjs-plan.md section 3.1-3.2; docs/campaign/design/V2-PACKED.md:248-249):
  * precision p bits per coefficient (fixed point, per model): SR-4's fixed-point emulation gives the p at
    which rounding adds 10 % to eta; we add GUARD bits;
  * cell width w = 2p + ceil(log2 S) + 2, S = the number of terms in one product coefficient;
  * operand F = 2.25 w box bits (stride 1.5 on both axes), box = (2c+1)^2 cells;
  * one Nat.mul costs 8 ns per operand bit (the larger operand), a cycle kappa = 2-3 multiplications;
  * peak per declaration 0.45 GB + 10 F (16 F if a cycle is split);
  * ledger: one literal output model per declaration, box_out * p bits; two scenarios: one literal per
    truncation (sums of products accumulated inside a declaration) and one per product;
  * literal elaboration 0.9-1.3 us per bit, 36-47 bytes charged per bit.
PASS iff kernel <= 50 CPU-h, ledger <= 5 GB and every declaration <= 8 GB by the memory law.
Usage: python3 sr5_opcount.py [--tag sr4-sr-vp-L8-Lv8-d1e-06]
"""
from __future__ import annotations

import argparse
import json
import math
from collections import defaultdict
from pathlib import Path

HERE = Path(__file__).resolve().parent
GUARD = 16


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--tag', default='sr4-sr-vp-L8-Lv8-d1e-06')
    ap.add_argument('--p', type=int, default=0, help='override the precision (bits)')
    args = ap.parse_args()
    rep4 = json.loads((HERE / f'results/{args.tag}.json').read_text())
    ops = json.loads((HERE / f'results/{args.tag}-ops.json').read_text())
    CP, KH = ops['CP'], ops['KH']
    p = args.p or (rep4['fixed_point_bits_for_10pct'] + GUARD)
    box_out = (2 * CP + 1) ** 2
    nprod = 0
    t_mul = 0.0
    maxF = 0.0
    bystage = defaultdict(lambda: [0, 0.0])
    lit_prod_bits = 0
    for stage, kind, ca, cb, cnt in ops['products']:
        ba, bb = (2 * ca + 1) ** 2, (2 * cb + 1) ** 2
        S = min(ba, bb)
        w = 2 * p + math.ceil(math.log2(max(S, 2))) + 2
        F = 2.25 * w * max(ba, bb)
        t = 8e-9 * F
        nprod += cnt
        t_mul += cnt * t
        maxF = max(maxF, F)
        bystage[stage][0] += cnt
        bystage[stage][1] += cnt * t
        lit_prod_bits += cnt * box_out * p
    lit_unpack_bits = ops['unpacks'] * box_out * p
    out = {'gate': 'SR-5 OPCOUNT', 'sr4': args.tag, 'p_bits': p, 'guard_bits': GUARD, 'CP': CP, 'KH': KH,
           'Lv': ops['Lv'], 'products': nprod, 'unpacks': ops['unpacks'],
           'by_stage': {k: {'products': v[0], 'mul_CPU_h': v[1] / 3600} for k, v in bystage.items()},
           'max_operand_Mbit': maxF / 1e6,
           'peak_per_declaration_GB': 0.45 + 10 * maxF / 8e9,
           'peak_split_cycle_GB': 0.45 + 16 * maxF / 8e9}
    for kappa in (2, 3):
        out[f'kernel_CPU_h_kappa{kappa}'] = kappa * t_mul / 3600
    for name, bits in (('per_truncation', lit_unpack_bits), ('per_product', lit_prod_bits)):
        out[f'ledger_{name}'] = {'GB': bits / 8e9, 'elaboration_CPU_h': [0.9e-6 * bits / 3600, 1.3e-6 * bits / 3600],
                                 'charged_GB': [36 * bits / 1e9, 47 * bits / 1e9]}
    # inputs: H_z (7,941 decimals, ~83 bits), S, F (literal), witnesses W, Y (3 + 3 models)
    out['inputs_Mbit'] = {'H_z': 7941 * 83 / 1e6, 'S_F_witnesses_estimate': (2790 + 3 * 4000 + 6 * box_out) * p / 1e6}
    # H_w = H_z o V' via symmetric powers: C'_d = S_d(V')^T C_d S_d(V'), d <= 9, matrices <= 55 x 55
    nmac = sum(2 * ((d + 1) * (d + 2) // 2) ** 3 for d in range(1, 10))
    out['H_w_by_symmetric_powers'] = {'rational_multiply_adds': nmac, 'entry_bits_max': 87 * 18 + 83,
                                      'note': 'estimate; exact, no balls; one-off'}
    k3 = out['kernel_CPU_h_kappa3']
    led = out['ledger_per_truncation']['GB']
    out['pass'] = {'kernel<=50': k3 <= 50, 'ledger<=5GB (per truncation)': led <= 5,
                   'declaration<=8GB': out['peak_split_cycle_GB'] <= 8}
    out['verdict'] = 'PASS' if all(out['pass'].values()) else 'FAIL'
    (HERE / 'results/sr5.json').write_text(json.dumps(out, indent=1) + '\n')
    for k, v in out.items():
        print(k, ':', v)


if __name__ == '__main__':
    main()
