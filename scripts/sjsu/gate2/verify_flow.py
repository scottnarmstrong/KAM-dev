#!/usr/bin/env python3
"""Independent check: are the stage-2 integrals F_j conserved along the true degree-18 flow?

Integrates the original SJSU18-O2 vector field (orbit.py, RK4) from the nominal point and evaluates
F_j(u, phi), u = |w|^2 - B0(phi), along the orbit, next to the modal actions for scale.
Usage: /usr/bin/python3 verify_flow.py <torus2 tag> [years] [h]
"""
import json
import math
import sys

import numpy as np

import ft
import orbit
import run_nf as R
from common import modal_model

tag = sys.argv[1]
years = float(sys.argv[2]) if len(sys.argv) > 2 else 2e5
h = float(sys.argv[3]) if len(sys.argv) > 3 else 10.0
# optional action offset of the initial point (modal actions), e.g. 5e-7,-5e-7,2e-7
off = [float(x) for x in sys.argv[4].split(',')] if len(sys.argv) > 4 else [0.0, 0.0, 0.0]
out = ft.__file__.rsplit('/', 1)[0] + '/results'
rep = json.load(open(f'{out}/{tag}.json'))
z = np.load(f'{out}/{tag}-F.npz')
S = ft.Space(L=rep['args']['L'], K=rep['args']['K'])
Fs = [z['F0'], z['F1'], z['F2']]
s_hat, Istar, c0 = z['s_hat'], z['Istar'], z['c0']
G2 = s_hat.shape[0]
k = np.rint(np.fft.fftfreq(G2, 1.0 / G2)).astype(int)
K1, K2 = np.meshgrid(k, k, indexing='ij')
kk = [K1, K2, -K1 - K2]
nz = np.abs(s_hat) > 0
grad = [(1j * kk[j] * s_hat)[nz] for j in range(3)]
k1n, k2n = K1[nz], K2[nz]
Hz, Hw, nu, V, z0, w0 = modal_model()
V = np.array(V)


def Fvals(w):
    q = np.angle(w)
    phi = (q[0] - q[2], q[1] - q[2])
    e = np.exp(1j * (k1n * phi[0] + k2n * phi[1]))
    B0 = [Istar[j] + c0[j] + float((grad[j] * e).sum().real) for j in range(3)]
    u = [abs(w[j]) ** 2 - B0[j] for j in range(3)]
    return [S.eval(F, u, phi).real for F in Fs], u


model = orbit.Model()
every = max(1, int(round(1000.0 / h)))
n = int(round(years / h))
wi = np.array(w0) * np.sqrt(1 + np.array(off) / np.abs(np.array(w0)) ** 2)
zi = V @ wi  # z = V w
zs = orbit.rk4(model, zi, h, n, every)
ws = zs @ V
F0, u0 = Fvals(ws[0])
I0 = np.abs(ws[0]) ** 2
dF = np.zeros(3)
dI = np.zeros(3)
for i, w in enumerate(ws):
    F, u = Fvals(w)
    dF = np.maximum(dF, np.abs(np.array(F) - F0))
    dI = np.maximum(dI, np.abs(np.abs(w) ** 2 - I0))
    if i % max(1, len(ws) // 10) == 0:
        print(f't={i * every * h:9.0f} yr  F-F0={np.array(F) - F0}  u={np.array(u)}', flush=True)
print('years', years, 'h', h)
print('max |F_j(t) - F_j(0)| =', dF)
print('max |I_j(t) - I_j(0)| =', dI, ' (modal actions, for scale)')
print('energy drift', abs(model.H(zs[-1]) - model.H(zs[0])) / abs(model.H(zs[0])))
