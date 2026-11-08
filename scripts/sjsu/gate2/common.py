"""Shared loading for the SJSU18-O2 gate scripts: modal polynomial, nominal point.

SJSU_VPRIME=<vprime.json> replaces the floating Jacobi V by the exactly orthogonal rational V' (SR-2).
"""
from __future__ import annotations

import cmath
import json
import math
import os
from fractions import Fraction

import poly as P
import run_nf as R


def modal_model():
    Hz, data = R.load_model()
    A = [[0.0] * 3 for _ in range(3)]
    for k, c in Hz.items():
        e = P.exps(k)
        if sum(e) == 2:
            A[[i for i in range(3) if e[i]][0]][[i for i in range(3) if e[i + 3]][0]] = c
    nu, V = R.jacobi_eig(A)
    vp = os.environ.get('SJSU_VPRIME')
    if vp:  # exactly orthogonal rational V' (scripts/sjsu/rigor/sr2_rational_rotation.py), as floats
        V = [[float(Fraction(x)) for x in row] for row in json.loads(open(vp).read())['Vprime_exact']]
    Hw = R.to_modal(Hz, V)
    z0 = [complex(R.XI[j], -R.ETA[j]) / math.sqrt(2) for j in range(3)]
    w0 = [sum(V[j][k] * z0[j] for j in range(3)) for k in range(3)]
    return Hz, Hw, nu, V, z0, w0


def terms_of(poly_dict):
    return [(P.exps(k), c) for k, c in poly_dict.items()]


def polar(w, Istar):
    """(p, phi) of a modal point: p_j = |w_j|^2 - I*_j, phi = (q1 - q3, q2 - q3)."""
    q = [cmath.phase(x) for x in w]
    p = [abs(x) ** 2 - Istar[j] for j, x in enumerate(w)]
    return p, (q[0] - q[2], q[1] - q[2])
