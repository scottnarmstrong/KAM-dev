#!/usr/bin/env python3
"""Fundamental frequencies of a secular model from the SLG13/GLS17 Table 2 initial data.

GLS17 eq. (37) reports, for the degree-18 secular Hamiltonian H^(D) and the Table 2 initial
data, the frequencies obtained by numerical integration and frequency analysis of the signals
x_j(t) + i y_j(t).  This script repeats the experiment for a given model:

  --model data/sjsu18_model.json       (complex form, z = (xi - i eta)/sqrt 2), or
  --table scripts/sjsu/slg13_quartic.json  (the printed 78-term quartic, real form).

The linear diagonalizer O is recomputed from the model's own quadratic part; (xi, eta) = (O x, O y).
Equations of motion: dz/dt = -i dH/dzbar.  Integrator: classical RK4 (complex128), step dt.
Frequency analysis: Hann-windowed Fourier transform, peak refined by golden-section search
(a simplified NAFF first-frequency step).  Float64: an estimate, not an enclosure.
"""
import argparse
import json
import math
import os
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np

from sjsu_common import TABLE2, GLS17_OMEGA


class ComplexPoly:
    def __init__(self, terms):
        """terms: list of (p1,q1,p2,q2,p3,q3, coef complex)."""
        E = np.array([t[:6] for t in terms], dtype=np.int64)
        C = np.array([complex(t[6]) for t in terms], dtype=np.complex128)
        self.E, self.C = E, C
        self.deg = int(E.sum(1).max())
        self.der = []
        for j in range(3):
            q = E[:, 2 * j + 1]
            m = q > 0
            Ed = E[m].copy(); Ed[:, 2 * j + 1] -= 1
            self.der.append((Ed, C[m] * q[m]))

    def quad_matrix(self):
        A = np.zeros((3, 3))
        for e, c in zip(self.E, self.C):
            if e.sum() == 2:
                i = [j for j in range(3) if e[2 * j] == 1][0]
                k = [j for j in range(3) if e[2 * j + 1] == 1][0]
                A[i, k] += c.real
        return A

    def rhs(self, z):
        zb = np.conj(z)
        n = self.deg + 1
        tab = np.empty((6, n), dtype=np.complex128)
        for j in range(3):
            tab[2 * j] = z[j] ** np.arange(n)
            tab[2 * j + 1] = zb[j] ** np.arange(n)
        out = np.empty(3, dtype=np.complex128)
        for j in range(3):
            Ed, Cd = self.der[j]
            mon = np.ones(len(Cd), dtype=np.complex128)
            for v in range(6):
                mon *= tab[v, Ed[:, v]]
            out[j] = -1j * np.dot(Cd, mon)
        return out


def from_real_table(path):
    """Convert a real (xi, eta) polynomial table to complex-form terms."""
    import sympy as sp
    from fractions import Fraction
    with open(path) as fh:
        d = json.load(fh)
    xi = sp.symbols('x1:4'); eta = sp.symbols('y1:4'); z = sp.symbols('z1:4'); w = sp.symbols('w1:4')
    H = 0
    for t in d['terms']:
        fr = Fraction(t['coefficient'])
        m = sp.Rational(fr.numerator, fr.denominator)
        for j in range(3):
            m *= xi[j] ** t['powers'][j] * eta[j] ** t['powers'][3 + j]
        H += m
    sub = {}
    for j in range(3):
        sub[xi[j]] = (z[j] + w[j]) / sp.sqrt(2)
        sub[eta[j]] = sp.I * (z[j] - w[j]) / sp.sqrt(2)
    P = sp.Poly(sp.expand(H.subs(sub)), *z, *w)
    terms = []
    for mon, c in P.terms():
        e = [mon[0], mon[3], mon[1], mon[4], mon[2], mon[5]]
        terms.append(tuple(e) + (complex(c),))
    return terms


def from_model(path):
    with open(path) as fh:
        d = json.load(fh)
    return [tuple(t[:6]) + (complex(float(t[6]), 0.0),) for t in d['complex_form']['terms']]


def table1_poincare_xieta():
    """(xi, eta) of SLG13 Table 1 read as Poincare elements (formula (2)); float64."""
    from fractions import Fraction
    from sjsu_common import TABLE1, MASS_RECIPROCALS
    m0 = 4 * math.pi ** 2
    xi, eta = [], []
    for j in range(3):
        mj = m0 / float(Fraction(MASS_RECIPROCALS[j]))
        beta = m0 * mj / (m0 + mj); mu = m0 + mj
        a = float(TABLE1['a'][j]); e = float(TABLE1['e'][j]); om = float(TABLE1['omega'][j])
        Lam = beta * math.sqrt(mu * a)
        G = Lam * (1 - math.sqrt(1 - e * e))
        xi.append(math.sqrt(2 * G) * math.cos(om)); eta.append(-math.sqrt(2 * G) * math.sin(om))
    return np.array(xi), np.array(eta)


def rk4(poly, z0, dt, nsteps, every):
    z = z0.copy()
    out = [z.copy()]
    for k in range(1, nsteps + 1):
        k1 = poly.rhs(z)
        k2 = poly.rhs(z + 0.5 * dt * k1)
        k3 = poly.rhs(z + 0.5 * dt * k2)
        k4 = poly.rhs(z + dt * k3)
        z = z + dt / 6 * (k1 + 2 * k2 + 2 * k3 + k4)
        if k % every == 0:
            out.append(z.copy())
    return np.array(out)


def fundamental_frequency(sig, h):
    """Dominant frequency (rad per time unit) of a complex signal sampled with step h."""
    n = len(sig)
    t = np.arange(n) * h
    win = 0.5 * (1 - np.cos(2 * np.pi * np.arange(n) / (n - 1)))
    spec = np.fft.fft(sig * win)
    freqs = np.fft.fftfreq(n, d=h) * 2 * np.pi
    k = int(np.argmax(np.abs(spec)))
    df = 2 * np.pi / (n * h)

    def amp(om):
        return abs(np.sum(sig * win * np.exp(-1j * om * t)))
    a, b = freqs[k] - df, freqs[k] + df
    g = (math.sqrt(5) - 1) / 2
    c, d = b - g * (b - a), a + g * (b - a)
    fc, fd = amp(c), amp(d)
    for _ in range(200):
        if fc > fd:
            b, d, fd = d, c, fc
            c = b - g * (b - a); fc = amp(c)
        else:
            a, c, fc = c, d, fd
            d = a + g * (b - a); fd = amp(d)
        if abs(b - a) < 1e-16 * max(1.0, abs(a)):
            break
    return 0.5 * (a + b)


def run(terms, years, dt, sample, label, log=print):
    poly = ComplexPoly(terms)
    A = poly.quad_matrix()
    A = 0.5 * (A + A.T)
    w, V = np.linalg.eigh(A)
    order = np.argsort(-np.abs(w)); w = w[order]; V = V[:, order]
    x0 = np.array([float(s) for s in TABLE2['x0']]); y0 = np.array([float(s) for s in TABLE2['y0']])
    # Column signs of O change the initial point (relative modal phases), so they are fixed as in
    # initial_map.py: project the Table 1 Poincare point onto the modes and match Table 2's signs.
    xiP, etaP = table1_poincare_xieta()
    xT = V.T @ xiP
    yT = V.T @ etaP
    flips = []
    for j in range(3):
        if xT[j] * x0[j] < 0:
            V[:, j] *= -1
            flips.append(j + 1)
    xT = V.T @ xiP; yT = V.T @ etaP
    sign_ok = bool(all(np.sign(yT) == np.sign(y0)))
    xi0, eta0 = V @ x0, V @ y0
    z0 = (xi0 - 1j * eta0) / math.sqrt(2)
    nsteps = int(round(years / dt))
    every = max(1, int(round(sample / dt)))
    t0 = time.time()
    traj = rk4(poly, z0, dt, nsteps, every)
    h = every * dt
    W = traj @ V            # modal w = O^T z  (rows: time)
    sigs = np.sqrt(2) * np.conj(W)   # x + i y
    om = [fundamental_frequency(sigs[:, j], h) for j in range(3)]
    # energy check
    log(f'[{label}] {len(terms)} terms, {nsteps} RK4 steps, {time.time()-t0:.0f}s; linear nu = {w}; '
        f'y-sign pattern of Table 1 projection matches Table 2: {sign_ok}')
    return {'label': label, 'nu_linear': w.tolist(), 'omega': om, 'years': years, 'dt': dt,
            'O': V.tolist(), 'table1_projection_x': xT.tolist(), 'table1_projection_y': yT.tolist(),
            'omega_gls17': [float(s) for s in GLS17_OMEGA]}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--model')
    ap.add_argument('--table')
    ap.add_argument('--years', type=float, default=2e7)
    ap.add_argument('--dt', type=float, default=100.0)
    ap.add_argument('--sample', type=float, default=1000.0)
    ap.add_argument('--json')
    args = ap.parse_args()
    results = []
    if args.table:
        results.append(run(from_real_table(args.table), args.years, args.dt, args.sample, 'printed quartic (78 terms)'))
    if args.model:
        results.append(run(from_model(args.model), args.years, args.dt, args.sample, os.path.basename(args.model)))
    for r in results:
        print(r['label'])
        for j in range(3):
            print(f"   omega_{j+1} = {r['omega'][j]:.12e}   GLS17 (37): {r['omega_gls17'][j]:.12e}   "
                  f"rel diff {(r['omega'][j] - r['omega_gls17'][j]) / abs(r['omega_gls17'][j]):+.3e}   linear {r['nu_linear'][j]:.10e}")
    if args.json:
        with open(args.json, 'w') as fh:
            json.dump(results, fh, indent=1)


if __name__ == '__main__':
    main()
