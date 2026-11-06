#!/usr/bin/env python3
"""Eccentricity ranges over the stage-2 torus tube (measured, floating).

e_j from Gamma_j = |z_j|^2 = Lambda*_j (1 - sqrt(1 - e_j^2)), z = V w, w_j = sqrt(I_j) e^{i q_j}, with
I = B0(phi) + v, |v_j| <= kappa delta (the tube about the torus graph; tau2 ~ 1e-13 is neglected here).
Usage: /usr/bin/python3 ecc.py <torus2 tag> [delta] [kappa]
"""
import json
import sys

import numpy as np

import run_nf as R
from common import modal_model

tag = sys.argv[1]
delta = float(sys.argv[2]) if len(sys.argv) > 2 else 1e-6
kappa = float(sys.argv[3]) if len(sys.argv) > 3 else 2.0
out = R.HERE / 'results'
z = np.load(out / f'{tag}-F.npz')
s_hat, Istar, c0 = z['s_hat'], z['Istar'], z['c0']
G2 = s_hat.shape[0]
k = np.rint(np.fft.fftfreq(G2, 1.0 / G2)).astype(int)
K1, K2 = np.meshgrid(k, k, indexing='ij')
kk = [K1, K2, -K1 - K2]
B0 = [Istar[j] + c0[j] + np.fft.ifft2(1j * kk[j] * s_hat).real * G2 * G2 for j in range(3)]
Hz, Hw, nu, V, z0, w0 = modal_model()
V = np.array(V)
Lam = [float(x) for x in json.loads((R.MODEL / 'data/sjsu18-o2.json').read_text())['parameters']['Lambda_star']]
ph = np.arange(G2) * 2 * np.pi / G2
P1, P2 = np.meshgrid(ph, ph, indexing='ij')
phase = [np.exp(1j * P1), np.exp(1j * P2), np.ones_like(P1)]


def ecc(I):
    w = [np.sqrt(I[j]) * phase[j] for j in range(3)]
    zz = [sum(V[j][kk_] * w[kk_] for kk_ in range(3)) for j in range(3)]
    G = [np.abs(x) ** 2 for x in zz]
    return [np.sqrt(1 - (1 - G[j] / Lam[j]) ** 2) for j in range(3)]


e_t = ecc(B0)
lo, hi = [np.inf] * 3, [-np.inf] * 3
r = kappa * delta
for s in np.array(np.meshgrid([-1, 0, 1], [-1, 0, 1], [-1, 0, 1])).reshape(3, -1).T:
    e = ecc([B0[j] + s[j] * r for j in range(3)])
    lo = [min(lo[j], float(e[j].min())) for j in range(3)]
    hi = [max(hi[j], float(e[j].max())) for j in range(3)]
zn = [complex(R.XI[j], -R.ETA[j]) / np.sqrt(2) for j in range(3)]
en = [np.sqrt(1 - (1 - abs(zn[j]) ** 2 / Lam[j]) ** 2) for j in range(3)]
print('nominal e =', en)
print('torus e range:', [(float(x.min()), float(x.max())) for x in e_t])
print(f'tube (delta={delta:g}, kappa={kappa:g}) e range (vertex sampling):', list(zip(lo, hi)))
