#!/usr/bin/env python3
"""Golden invariant circle of the Chirikov standard map: analyticity width against the coupling, and what the kernel could reach.

Map (FHL17 (110)): y' = y - (k/2 pi) sin(2 pi x), x' = x + y'.  The circle x = theta + u(theta), Lagrangian form
    u(theta + w) - 2 u(theta) + u(theta - w) + (k/2 pi) sin(2 pi (theta + u(theta))) = 0,       w = golden mean,
is solved by Newton in Fourier space with the reducibility preconditioner (the Jacobian is banded in real space after the
substitution of Levi-Moser): dense-free, FFT only.  Double precision, N up to 2^20, k up to the mode budget.

For each k the fit gives the strip width w(k) from the coefficient decay; S(L) = L ln 10 / (2 pi w) * 2 (real coefficients of a
parity-symmetric u: half that) is the support at L digits.  FHL17 Table 5 gives the theorem's margin at tolerance 1e-33.
"""
import json
import math
import os
import numpy as np

import pipeline as pl

W = (math.sqrt(5) - 1) / 2


def residual(uh, N, k):
    th = np.arange(N) / N
    ks = np.fft.fftfreq(N, 1 / N)
    u = np.fft.ifft(uh * N).real
    r = 2 * (np.cos(2 * np.pi * ks * W) - 1) * uh + np.fft.fft(k / (2 * np.pi) * np.sin(2 * np.pi * (th + u))) / N
    return r, u


def newton_step(uh, N, k):
    """Levi-Moser reducibility.  With h = 1 + u', differentiating F[u] = 0 gives k cos(2 pi (th + u)) h = -(h+ - 2h + h-) + F'.  Hence for
    v = h b the linearization satisfies, up to O(F),   h L v = a - a(-w),   a = h h+ (b+ - b).   Solve L v = -r by two cohomological equations."""
    ks = np.fft.fftfreq(N, 1 / N)
    r, u = residual(uh, N, k)
    h = 1 + np.fft.ifft(2j * np.pi * ks * uh * N).real
    h_p = np.fft.ifft(np.fft.fft(h) * np.exp(2j * np.pi * ks * W)).real
    fh = np.fft.fft(h * np.fft.ifft(r * N).real) / N
    fh[0] = 0
    lam = 1 - np.exp(-2j * np.pi * ks * W)
    lam[0] = 1
    a0 = np.fft.ifft(-fh / lam * N).real
    ip = 1 / (h * h_p)
    c = -(a0 * ip).mean() / ip.mean()
    ah = np.fft.fft((a0 + c) * ip) / N
    ah[0] = 0
    lam2 = np.exp(2j * np.pi * ks * W) - 1
    lam2[0] = 1
    b = np.fft.ifft(ah / lam2 * N).real
    vh = np.fft.fft(h * b) / N
    vh[0] = 0
    return uh + vh


def solve(k_target, N, uh=None, k0=0.0, steps=8):
    ks = np.fft.fftfreq(N, 1 / N)
    mask = np.abs(ks) < N / 3
    if uh is None:
        uh = np.zeros(N, dtype=complex)
    for kk in np.linspace(k0, k_target, steps + 1)[1:]:
        for it in range(14):
            uh = newton_step(uh, N, kk) * mask
            r, _ = residual(uh, N, kk)
            e = np.abs(r * mask).max()
            if e < 2e-14:
                break
    return uh, e


def width(uh, N):
    """strip width from the upper envelope of |u_k| on 1e-11 < |u_k| < 1e-2 (above the double-precision floor)."""
    ks = np.abs(np.fft.fftfreq(N, 1 / N)).astype(int)
    m = np.zeros(N // 2 + 1)
    np.maximum.at(m, ks, np.abs(uh))
    env = np.maximum.accumulate(m[::-1])[::-1]
    idx = np.where((env > 1e-11) & (env < 1e-2))[0]
    idx = idx[idx > 0]
    p = np.polyfit(idx, np.log(env[idx]), 1)
    return -p[0] / (2 * np.pi), int(idx.max())


def main():
    out = []
    N = 2 ** 15   # the filter N/3 stops just below the Fibonacci number 10946: a larger cut amplifies round-off through the next small divisor
    uh = None
    k0 = 0.0
    for k in (0.3, 0.5, 0.6, 0.7, 0.76, 0.8, 0.86, 0.9, 0.92, 0.94, 0.95, 0.96):
        uh2, e = solve(k, N, uh, k0, steps=2 if k <= 0.8 else (6 if k <= 0.9 else 40))
        if not np.isfinite(e) or e > 1e-11:
            print("stop at k", k, "err", e)
            break
        uh, k0 = uh2, k
        w, kmax = width(uh, N)
        row = dict(k=k, N=N, err=float(e), width=w, kmax=kmax)
        for L in (30, 40, 50, 60):
            row["S%d" % L] = L * math.log(10) / (2 * math.pi * w)
        out.append(row)
        print("k %.3f err %.1e width %.3e kmax(1e-11) %d  S30 %.0f S50 %.0f" % (k, e, w, kmax, row["S30"], row["S50"]), flush=True)
    pl.save("stdmap.json", dict(rows=out, fhl17_table5=[
        (0.06, 128, 1.606160e-02, 1.35e-28), (0.16, 256, 1.369960e-02, 9.24e-28), (0.26, 256, 1.369960e-02, 1.74e-26), (0.36, 512, 1.369960e-02, 4.24e-25),
        (0.46, 512, 1.369960e-02, 1.76e-23), (0.56, 512, 4.520867e-03, 9.39e-24), (0.66, 1024, 3.300233e-03, 1.88e-23), (0.76, 1024, 2.310163e-03, 2.32e-18),
        (0.86, 2048, 1.178183e-03, 1.74e-17), (0.96, 32768, 1.178183e-04, 2.34e-12)]))


def reach():
    """How close to k_c the kernel gets, given a maps theorem.  Width law w = 0.235 (k_c - k) (fit of `main`, k = 0.86..0.96; beyond k = 0.96 an extrapolation, and the true
    scaling near k_c is renormalization, so these are optimistic at the last rows).  The theorem is assumed of FHL17 form: threshold = gamma^4 rho^4 / C1, C1 = 1e7 (from FHL17 Table 5 at
    k = 0.96: ratio 2.34e-12 at tolerance 1e-33, rho = 1.18e-4, an upper estimate of their C1 if b_E > 1e-33) or C1 = 1e10 (a first Lean theorem, 3 orders cruder)."""
    import costmodel as cm
    kc = 0.971635406
    gam = (3 - math.sqrt(5)) / 2
    rows = []
    for k in (0.9, 0.95, 0.96, 0.965, 0.97, 0.971, 0.9714, 0.9715, 0.9716):
        w = 0.235 * (kc - k)
        for C1 in (1e7, 1e10):
            best = None
            for frac in (1 / 2, 1 / 3, 1 / 4, 1 / 6, 1 / 8):
                rho = w * frac
                thr = gam ** 4 * rho ** 4 / C1
                L = (-math.log10(thr) + 5) / (1 - frac)
                S = L * math.log(10) / (2 * math.pi * w)
                if best is None or S < best[0]:
                    best = (S, L, rho, thr)
            S, L, rho, thr = best
            p = cm.project(S * 2, L, 3, Nlow=20, box_factor=1.0)   # factor 2: complex slots of the witness E
            rows.append(dict(k=k, C1=C1, width=w, rho=rho, log10thr=math.log10(thr), L=L, S=S, ratio=p["ratio"], cpuh=p["cpuh"]["P"], advice_MB=p["advice_MB"]))
            print("k %.4f C1 %.0e width %.2e rho %.2e thr 1e%.1f L %.0f S %.0f  lunar units %.2f CPU-h %.1f-%.1f advice %.1f MB" % (k, C1, w, rho, math.log10(thr), L, S, p["ratio"], p["cpuh"]["P"][0], p["cpuh"]["P"][1], p["advice_MB"]), flush=True)
    pl.save("stdmap_reach.json", rows)


if __name__ == "__main__":
    import sys
    (reach if len(sys.argv) > 1 and sys.argv[1] == "reach" else main)()
