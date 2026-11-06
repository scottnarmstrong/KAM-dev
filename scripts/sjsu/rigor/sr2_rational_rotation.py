#!/usr/bin/env python3
"""SR-2 RATIONAL-ROTATION, part 1: an exactly orthogonal rational modal matrix V' (standard library + mpmath).

The gate scripts diagonalize the quadratic block A of SJSU18-O2 (complex form, A[i][j] = coefficient of
z_i zbar_j) by a floating Jacobi rotation V (z = V w).  A float V is not exactly orthogonal, so w = V^T z
is not exactly symplectic.  Here V' = R(q) D with
  * R(q) the rotation of an integer quaternion q = (a, b, c, d) (the Cayley transform of the skew matrix
    of (b, c, d)/a): every entry is an integer over N = a^2 + b^2 + c^2 + d^2, and R(q)^T R(q) = I exactly;
  * D a diagonal sign matrix with det(V D) = +1, so that V' keeps the column signs of V.
A real orthogonal V' acts on (xi, eta) as one rotation of each, which is symplectic.

Output: results/vprime.json (q, N, D, the nine entries as exact fractions and floats, checks).
PASS (part 1) iff V'^T V' = I exactly, det V' = det V (= -1 here) and max |V' - V| <= 1e-12, with V the gate scripts' V and the
eigenvectors of A computed at 60 digits from the exact decimal A.
Part 2 (the producer rerun with V') is run by sr2_rerun.sh.
"""
from __future__ import annotations

import json
import sys
from fractions import Fraction
from pathlib import Path

import mpmath as mp

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
sys.path.insert(0, str(ROOT / 'scripts/sjsu/gate2'))
import run_nf as R  # noqa: E402

mp.mp.dps = 60
SCALE = 10 ** 13  # quaternion component scale: entry error ~ 1/SCALE


def exact_A():
    data = json.loads((ROOT / 'applications/sjsu/data/sjsu18-o2.json').read_text())
    A = [[Fraction(0)] * 3 for _ in range(3)]
    for t in data['complex_form']['terms']:
        e = t[:6]  # zJ zbJ zS zbS zU zbU
        if sum(e) == 2:
            i = [j for j in range(3) if e[2 * j]][0]
            k = [j for j in range(3) if e[2 * j + 1]][0]
            A[i][k] = Fraction(t[6])
    return A


def quat_to_rot(a, b, c, d):
    """Integer matrix M and N with R = M / N (R the rotation of the quaternion a + bi + cj + dk)."""
    N = a * a + b * b + c * c + d * d
    M = [[a * a + b * b - c * c - d * d, 2 * (b * c - a * d), 2 * (b * d + a * c)],
         [2 * (b * c + a * d), a * a - b * b + c * c - d * d, 2 * (c * d - a * b)],
         [2 * (b * d - a * c), 2 * (c * d + a * b), a * a - b * b - c * c + d * d]]
    return M, N


def rot_to_quat(Rm):
    """Unit quaternion of a rotation matrix (mpmath), Shepperd's method."""
    tr = Rm[0][0] + Rm[1][1] + Rm[2][2]
    cand = [tr, Rm[0][0], Rm[1][1], Rm[2][2]]
    i = max(range(4), key=lambda j: cand[j])
    if i == 0:
        s = mp.sqrt(1 + tr) * 2
        return [s / 4, (Rm[2][1] - Rm[1][2]) / s, (Rm[0][2] - Rm[2][0]) / s, (Rm[1][0] - Rm[0][1]) / s]
    if i == 1:
        s = mp.sqrt(1 + Rm[0][0] - Rm[1][1] - Rm[2][2]) * 2
        return [(Rm[2][1] - Rm[1][2]) / s, s / 4, (Rm[0][1] + Rm[1][0]) / s, (Rm[0][2] + Rm[2][0]) / s]
    if i == 2:
        s = mp.sqrt(1 + Rm[1][1] - Rm[0][0] - Rm[2][2]) * 2
        return [(Rm[0][2] - Rm[2][0]) / s, (Rm[0][1] + Rm[1][0]) / s, s / 4, (Rm[1][2] + Rm[2][1]) / s]
    s = mp.sqrt(1 + Rm[2][2] - Rm[0][0] - Rm[1][1]) * 2
    return [(Rm[1][0] - Rm[0][1]) / s, (Rm[0][2] + Rm[2][0]) / s, (Rm[1][2] + Rm[2][1]) / s, s / 4]


def main():
    A = exact_A()
    # the gate scripts' V (float Jacobi, columns sorted by eigenvalue, largest component positive)
    Af = [[float(x) for x in row] for row in A]
    nu_f, Vf = R.jacobi_eig(Af)
    # high-precision eigenvectors of the exact A, aligned to Vf's order and signs
    Am = mp.matrix([[mp.mpf(x.numerator) / x.denominator for x in row] for row in A])
    E, Q = mp.eigsy(Am)
    cols = []
    for j in range(3):
        best = max(range(3), key=lambda c: abs(sum(Q[r, c] * Vf[r][j] for r in range(3))))
        sgn = 1 if sum(Q[r, best] * Vf[r][j] for r in range(3)) > 0 else -1
        cols.append([sgn * Q[r, best] for r in range(3)])
    Vm = [[cols[j][r] for j in range(3)] for r in range(3)]
    det = mp.det(mp.matrix(Vm))
    Dsg = [1, 1, 1] if det > 0 else [1, 1, -1]
    Rm = [[Vm[r][j] * Dsg[j] for j in range(3)] for r in range(3)]
    qf = rot_to_quat(Rm)
    q = [int(mp.nint(x * SCALE)) for x in qf]
    M, N = quat_to_rot(*q)
    Vp = [[Fraction(M[r][j] * Dsg[j], N) for j in range(3)] for r in range(3)]
    # exact orthogonality
    ortho = all(sum(Vp[r][i] * Vp[r][j] for r in range(3)) == (1 if i == j else 0)
                for i in range(3) for j in range(3))
    detVp = (Vp[0][0] * (Vp[1][1] * Vp[2][2] - Vp[1][2] * Vp[2][1])
             - Vp[0][1] * (Vp[1][0] * Vp[2][2] - Vp[1][2] * Vp[2][0])
             + Vp[0][2] * (Vp[1][0] * Vp[2][1] - Vp[1][1] * Vp[2][0]))
    err_float = max(abs(float(Vp[r][j]) - Vf[r][j]) for r in range(3) for j in range(3))
    err_exact = max(abs(mp.mpf(Vp[r][j].numerator) / Vp[r][j].denominator - Vm[r][j])
                    for r in range(3) for j in range(3))
    # quadratic block in V' coordinates: V'^T A V' (exact); off-diagonal residual
    B = [[sum(Vp[r][i] * A[r][s] * Vp[s][j] for r in range(3) for s in range(3)) for j in range(3)]
         for i in range(3)]
    off = max(abs(float(B[i][j])) for i in range(3) for j in range(3) if i != j)
    rep = {
        'gate': 'SR-2 RATIONAL-ROTATION (part 1: V\')',
        'construction': "V' = R(q) D, R(q) = M/N the rotation of the integer quaternion q, D = diag signs",
        'quaternion': q, 'N': N, 'N_bits': N.bit_length(), 'D': Dsg,
        'Vprime_exact': [[f'{x.numerator}/{x.denominator}' for x in row] for row in Vp],
        'Vprime_float': [[float(x) for x in row] for row in Vp],
        'V_float_gate_scripts': Vf, 'nu_float': nu_f,
        'eigenvalues_60': [mp.nstr(E[i], 25) for i in range(3)],
        'exactly_orthogonal': ortho, 'det': str(detVp),
        'max_abs_Vprime_minus_V_float': err_float,
        'max_abs_Vprime_minus_V_exact_eigvec': float(err_exact),
        'quadratic_block_offdiag_max_in_Vprime': off,
        'quadratic_block_diag_in_Vprime': [float(B[i][i]) for i in range(3)],
    }
    rep['det_V_float_sign'] = int(mp.sign(det))
    rep['pass_part1'] = ortho and detVp == int(mp.sign(det)) and err_float <= 1e-12 and float(err_exact) <= 1e-12
    (HERE / 'results').mkdir(exist_ok=True)
    (HERE / 'results/vprime.json').write_text(json.dumps(rep, indent=1) + '\n')
    for k, v in rep.items():
        print(k, ':', v)
    return 0 if rep['pass_part1'] else 1


if __name__ == '__main__':
    sys.exit(main())
