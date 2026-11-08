#!/usr/bin/env python3
"""SR-7 Q-RADIUS: the largest r with the sup-norm ball {||z - z*||_inf <= r} (z = (xi, eta) in R^6) inside
Q = {|F_j - c_j| <= delta/2, j = J, S, U} ∩ tube, for the literal data of SR-4 (python-flint).

Mean-value bound on the ball (convex, so segments from z* stay in it):
  |F_j(z) - c_j| <= |F_j(z*) - c_j| + r sum_x sup|dF_j/dx|,   |u_l(z)| <= |u_l(z*)| + r sum_x sup|du_l/dx|,
over the 6 real coordinates x, with the chain z_j = (xi_j - i eta_j)/sqrt2, w = V'^T z, I = |w|^2,
q = arg w, phi = (q1 - q3, q2 - q3), u = I - B0(phi):
  |dI_l/dx| <= sqrt2 |w_l|max |V'_il|,  |dq_l/dx| <= |V'_il| / (sqrt2 |w_l|min),
  |du_l/dx| <= |dI_l/dx| + sum_a sup|dB0_l/dphi_a| |dphi_a/dx|,
  |dF_j/dx| <= sum_l sup|dF_j/du_l| |du_l/dx| + sum_a sup|dF_j/dphi_a| |dphi_a/dx|,
with |w_l| within r sum_i |V'_il| of |w*_l| and the sup of dF over the whole tube (weighted l1 norms at
radius kappa delta).  F_j(z*) is enclosed in arb from the exact decimals of z*; c_j is F_j(z*) rounded to
30 digits.  PASS iff r >= 1e-6.
Usage: python sr7_qradius.py [--run sr-vp-L8] [--delta 1e-6]
"""
from __future__ import annotations

import argparse
import json
import math
import sys
from fractions import Fraction
from pathlib import Path

from flint import arb, ctx

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import sr4_ball_mirror as S4  # noqa: E402
from ballft import FM, Layout, ZERO, hexn, to_arb  # noqa: E402


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--run', default='sr-vp-L8')
    ap.add_argument('--delta', type=float, default=1e-6)
    ap.add_argument('--kappa', type=float, default=2.0)
    args = ap.parse_args()
    L = Layout(30, 60, 160)
    delta, kappa = args.delta, args.kappa
    R = kappa * delta
    Fd, sig, Ibar, mons = S4.load_run(args.run)
    vp = json.loads((HERE / 'results/vprime.json').read_text())
    V = [[Fraction(x) for x in row] for row in vp['Vprime_exact']]
    B0c = []
    for j in range(3):
        d = {}
        for (k1, k2), s in sig.items():
            kj = (k1, k2, -k1 - k2)[j]
            if kj:
                d[(k1, k2)] = -kj * s
        B0c.append(d)
    dB = [[S4.up(S4.l1_k(B0c[l], a)) for a in range(2)] for l in range(3)]
    # z* exactly; w* = V'^T z*, z*_j = (xi_j - i eta_j)/sqrt2 -> work with sqrt2 w* = V'^T (xi - i eta) (exact)
    dec = json.loads((HERE / 'results/sr1.json').read_text())['nominal']['decimals']
    zs = [Fraction(s) for s in dec]
    xi, eta = zs[:3], zs[3:]
    sw = [(sum(V[j][l] * xi[j] for j in range(3)), -sum(V[j][l] * eta[j] for j in range(3))) for l in range(3)]
    Ist = [(a * a + b * b) / 2 for a, b in sw]               # I*_l = |w*_l|^2 exactly
    q = [arb.atan2(to_arb(b), to_arb(a)) for a, b in sw]      # q_l = arg w*_l
    phi = (q[0] - q[2], q[1] - q[2])
    wabs = [math.sqrt(float(I)) for I in Ist]
    B0 = []
    for j in range(3):
        d = dict(B0c[j])
        d[(0, 0)] = d.get((0, 0), 0) + Ibar[j]
        B0.append(FM.from_coeffs(L, d, 0))
    ust = [to_arb(Ist[l]) - B0[l].eval(*phi) for l in range(3)]
    rows = []
    for j in range(3):
        Fm = {m: FM.from_coeffs(L, d, 0) for m, d in Fd[j].items()}
        Fz = ZERO
        for m, f in Fm.items():
            t = f.eval(*phi)
            for l in range(3):
                t *= ust[l] ** m[l]
            Fz += t
        cj = Fraction(str(Fz.mid().str(30, radius=False)).replace(' ', ''))
        off = S4.up(abs(Fz - to_arb(cj)))
        # sup over the tube of dF/du_l and dF/dphi_a (weighted l1 norms at radius R)
        Su = [0.0, 0.0, 0.0]
        Sp = [0.0, 0.0]
        for m, f in Fm.items():
            dm = sum(m)
            for l in range(3):
                if m[l]:
                    Su[l] += m[l] * S4.up(f.n1) * R ** (dm - 1)
            for a in range(2):
                Sp[a] += S4.up(S4.l1_k(Fd[j][m], a)) * R ** dm
        rows.append({'j': j, 'c_j': str(cj), 'F(z*) - c_j': off, 'sup_dF_du': Su, 'sup_dF_dphi': Sp})

    def bounds(r):
        rho = [r * sum(abs(float(V[i][l])) for i in range(3)) for l in range(3)]
        wmin = [wabs[l] - rho[l] for l in range(3)]
        wmax = [wabs[l] + rho[l] for l in range(3)]
        if min(wmin) <= 0:
            return None
        # per coordinate x = xi_i or eta_i (same bounds for both)
        dI = [[math.sqrt(2) * wmax[l] * abs(float(V[i][l])) for l in range(3)] for i in range(3)]
        dq = [[abs(float(V[i][l])) / (math.sqrt(2) * wmin[l]) for l in range(3)] for i in range(3)]
        dphi = [[dq[i][a] + dq[i][2] for a in range(2)] for i in range(3)]
        du = [[dI[i][l] + sum(dB[l][a] * dphi[i][a] for a in range(2)) for l in range(3)] for i in range(3)]
        Fb, ub = [], []
        for row in rows:
            g = sum(2 * (sum(row['sup_dF_du'][l] * du[i][l] for l in range(3))
                         + sum(row['sup_dF_dphi'][a] * dphi[i][a] for a in range(2))) for i in range(3))
            Fb.append(row['F(z*) - c_j'] + r * g)
        for l in range(3):
            ub.append(abs(float(ust[l].mid())) + S4.up(ust[l].rad()) + r * sum(2 * du[i][l] for i in range(3)))
        return Fb, ub

    def ok(r):
        b = bounds(r)
        return b is not None and max(b[0]) <= delta / 2 and max(b[1]) <= R

    lo, hi = 0.0, 1e-3
    for _ in range(60):
        mid = (lo + hi) / 2
        if ok(mid):
            lo = mid
        else:
            hi = mid
    Fb, ub = bounds(lo)
    rep = {'gate': 'SR-7 Q-RADIUS', 'args': vars(args), 'u_at_z*': [float(x.mid()) for x in ust],
           'rows': rows, 'r_max': lo, 'at_r_max': {'F_bounds': Fb, 'u_bounds': ub, 'delta/2': delta / 2},
           'lipschitz_F_per_r': [(f - row['F(z*) - c_j']) / lo for f, row in zip(Fb, rows)],
           'verdict': 'PASS' if lo >= 1e-6 else 'FAIL'}
    (HERE / 'results/sr7.json').write_text(json.dumps(rep, indent=1, default=str) + '\n')
    for k, v in rep.items():
        print(k, ':', v)
    return 0


if __name__ == '__main__':
    sys.exit(main())
