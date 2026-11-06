#!/usr/bin/env python3
"""Consistency checks of ft.py against the polynomial engine (run with /usr/bin/python3)."""
import time

import numpy as np

import ft
import poly as P
from common import modal_model, polar, terms_of

t0 = time.time()
Hz, Hw, nu, V, z0, w0 = modal_model()
I0 = [abs(x) ** 2 for x in w0]
Istar = [1.01 * x for x in I0]
S = ft.Space(L=12, K=24)
print('space M =', S.M, 'G =', S.G, f'({time.time() - t0:.1f}s)')
Hf = ft.from_modal_poly(S, terms_of(Hw), Istar)
print(f'converted H ({time.time() - t0:.1f}s)')
p, phi = polar(w0, Istar)
print('H poly =', P.evaluate(Hw, w0), ' H ft =', S.eval(Hf, p, phi))
# realness: c[m, -k] = conj c[m, k]
neg = np.conj(Hf[:, (-S.K1) % S.G, (-S.K2) % S.G])
print('realness defect', np.abs(Hf - neg).max(), ' max coef', np.abs(Hf).max())
# brackets {I_j, H} vs {p_j, H}
for j in range(3):
    Ij = {P.UNIT[j] + P.UNIT[j + 3]: 1.0}
    bp = P.evaluate(P.bracket(Ij, Hw), w0)
    t1 = time.time()
    bf = S.eval(S.bracket(S.var(j), Hf), p, phi)
    print(f'{{I_{j}, H}}: poly {bp:.12e}  ft {bf:.12e}  ({time.time() - t1:.2f}s per bracket)')
# a nonlinear test function: G = w0^2 wbar1^2 + c.c. style invariant monomial and its bracket with H
Gp = {P.key_of((2, 0, 0, 0, 2, 0)): 1.0, P.key_of((0, 2, 0, 2, 0, 0)): 1.0,
      P.key_of((1, 1, 0, 0, 1, 1)): 0.5j, P.key_of((0, 1, 1, 1, 1, 0)): -0.5j}
Gf = ft.from_modal_poly(S, terms_of(Gp), Istar)
bp = P.evaluate(P.bracket(Gp, Hw), w0)
bf = S.eval(S.bracket(Gf, Hf), p, phi)
print(f'{{G, H}}: poly {bp:.12e}  ft {bf:.12e}')
print('omega(p=0) =', S.omega(Hf), ' linear nu =', nu)
