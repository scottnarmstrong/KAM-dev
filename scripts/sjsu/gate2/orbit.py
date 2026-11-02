#!/usr/bin/env python3
"""Nominal SJSU18-O2 secular orbit: RK integration and frequency analysis (measured, floating).

Run with /usr/bin/python3 (numpy). Integrates dz/dt = -i dH/d(zbar) from the Table-1 nominal point,
checks H and the AMD C = sum |z_j|^2, and measures the fundamental frequencies of the modal
coordinates w = V^T z by a windowed Fourier peak search refined by golden-section maximization.
"""
from __future__ import annotations

import json
import math
import sys
import time
from pathlib import Path

import numpy as np

import run_nf as R


class Model:
    def __init__(self):
        data = json.loads((R.MODEL / 'data/sjsu18-o2.json').read_text())
        t = np.array(data['complex_form']['terms'], dtype=object)
        # exponent order in file: zJ, zbJ, zS, zbS, zU, zbU
        e = np.array([[int(r[i]) for i in range(6)] for r in t])
        self.a = e[:, [0, 2, 4]]
        self.b = e[:, [1, 3, 5]]
        self.c = np.array([float(r[6]) for r in t])

    def _mono(self, z, a, b):
        zb = np.conj(z)
        out = np.ones(len(self.c), dtype=complex)
        for j in range(3):
            out *= z[j] ** a[:, j] * zb[j] ** b[:, j]
        return out

    def H(self, z):
        return np.sum(self.c * self._mono(z, self.a, self.b)).real

    def rhs(self, z):
        """dz/dt = -i dH/dzbar."""
        zb = np.conj(z)
        out = np.empty(3, dtype=complex)
        for j in range(3):
            bj = self.b[:, j]
            mask = bj > 0
            bb = self.b[mask].copy()
            bb[:, j] -= 1
            aa = self.a[mask]
            m = np.ones(mask.sum(), dtype=complex)
            for i in range(3):
                m *= z[i] ** aa[:, i] * zb[i] ** bb[:, i]
            out[j] = np.sum(self.c[mask] * bj[mask] * m)
        return -1j * out


def rk4(model, z0, h, n, every=1):
    z = np.array(z0, dtype=complex)
    out = [z.copy()]
    f = model.rhs
    for s in range(1, n + 1):
        k1 = f(z)
        k2 = f(z + 0.5 * h * k1)
        k3 = f(z + 0.5 * h * k2)
        k4 = f(z + h * k3)
        z = z + (h / 6) * (k1 + 2 * k2 + 2 * k3 + k4)
        if s % every == 0:
            out.append(z.copy())
    return np.array(out)


def refine_peak(sig, t, w0, dw):
    """Golden-section maximization of |sum sig(t) win(t) e^{-i w t}| near w0."""
    T = t[-1] - t[0]
    win = 1 - np.cos(2 * np.pi * (t - t[0]) / T)  # Hann

    def amp(w):
        return abs(np.sum(sig * win * np.exp(-1j * w * t)))
    a, b = w0 - dw, w0 + dw
    g = (math.sqrt(5) - 1) / 2
    c, d = b - g * (b - a), a + g * (b - a)
    fc, fd = amp(c), amp(d)
    for _ in range(80):
        if fc > fd:
            b, d, fd = d, c, fc
            c = b - g * (b - a)
            fc = amp(c)
        else:
            a, c, fc = c, d, fd
            d = a + g * (b - a)
            fd = amp(d)
    w = (a + b) / 2
    coef = np.sum(sig * win * np.exp(-1j * w * t)) / np.sum(win)
    return w, coef


def naff(sig, t, nterms=6):
    """Frequency analysis: successive peak extraction from sig(t) = sum A_k e^{i w_k t}."""
    res = []
    s = sig.copy()
    n = len(t)
    dt = t[1] - t[0]
    for _ in range(nterms):
        win = 1 - np.cos(2 * np.pi * np.arange(n) / n)
        F = np.fft.fft(s * win)
        freqs = 2 * np.pi * np.fft.fftfreq(n, d=dt)
        i = int(np.argmax(np.abs(F)))
        w, coef = refine_peak(s, t, freqs[i], 2 * np.pi / (n * dt))
        res.append((w, coef))
        s = s - coef * np.exp(1j * w * t)
    return res


def main():
    years = float(sys.argv[1]) if len(sys.argv) > 1 else 2e6
    h = float(sys.argv[2]) if len(sys.argv) > 2 else 100.0
    model = Model()
    Hz, _ = R.load_model()
    A = [[0.0] * 3 for _ in range(3)]
    import poly as P
    for k, c in Hz.items():
        e = P.exps(k)
        if sum(e) == 2:
            A[[i for i in range(3) if e[i]][0]][[i for i in range(3) if e[i + 3]][0]] = c
    nu, V = R.jacobi_eig(A)
    V = np.array(V)
    z0 = np.array([complex(R.XI[j], -R.ETA[j]) / math.sqrt(2) for j in range(3)])
    n = int(round(years / h))
    every = max(1, int(round(500.0 / h)))
    t0 = time.time()
    zs = rk4(model, z0, h, n, every)
    t = np.arange(len(zs)) * h * every
    E = np.array([model.H(z) for z in zs[:: max(1, len(zs) // 200)]])
    C = np.sum(np.abs(zs) ** 2, axis=1)
    ws = zs @ V  # w_k = sum_j V[j][k] z_j
    I = np.abs(ws) ** 2
    print(f'integrated {years:.3g} yr with h={h} in {time.time() - t0:.1f}s; {len(zs)} samples')
    print('rel energy drift', (E.max() - E.min()) / abs(E[0]), ' AMD rel drift', (C.max() - C.min()) / C[0])
    print('modal actions: mean', I.mean(axis=0), ' min', I.min(axis=0), ' max', I.max(axis=0))
    print('linear nu', nu)
    rep = {'years': years, 'h': h, 'nu': nu, 'I_mean': I.mean(axis=0).tolist(),
           'I_min': I.min(axis=0).tolist(), 'I_max': I.max(axis=0).tolist(), 'naff': []}
    for j in range(3):
        terms = naff(ws[:, j], t, 6)
        rep['naff'].append([(w, abs(c)) for w, c in terms])
        print(f'mode {j}:', ', '.join(f'{w:.10e} (|A|={abs(c):.3e})' for w, c in terms))
    out = R.HERE / 'results'
    out.mkdir(exist_ok=True)
    (out / 'orbit.json').write_text(json.dumps(rep, indent=1) + '\n')
    np.save(out / 'orbit_w.npy', ws)


if __name__ == '__main__':
    main()
