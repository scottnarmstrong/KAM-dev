#!/usr/bin/env python3
"""SHARP-CERTSIDE: actual sizes of the objects the v2 hypotheses (SHARP-PLUS levers L1, L6) would bound, on the
lunar candidates, next to the values the sharp v1 theorem derives from (M, sK, sB, sT).

Untrusted design tooling.  Rotated frame, rho = 1/70, mu = 1/160, time scale c (default 237/125, package R1).
Sup norms: sampled on the distinguished boundary of the polystrip (max principle) and, for comparison, the
weighted l1 / corner bounds of the Fourier coefficients (computed on the real torus).  Matrix norms are max row
sums (the operator norm of ell^infinity), as in the frozen hypotheses.
  |L^T|   = max column sum of L = DK              (v1 derives 2 n sK)
  |N|     = max row sum of N = Omega0 L G^-1       (v1: sK sB)
  |N^T|   = max column sum of N                   (v1: 2 n sK sB)
  sup |T| on the strip (2 x 2 torsion block)      (v1: H_T = 4 n M sK^2 sB^2 + 1, KAM/Sharp/Constants.lean)
  |omega| = c |omega'|                            (v1: Theta = 2 n sK sB (M + 1))
Usage: python3 -I scripts/certifier/v2_majorants.py CACHE_DIR [c]
"""
import sys, os, math
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from lunar_oracle import LunarOracle, OM, JX, series_from_grid, TP   # noqa: E402

rho, mu = 1 / 70, 1 / 160
cache = sys.argv[1] if len(sys.argv) > 1 else None
c = float(sys.argv[2]) if len(sys.argv) > 2 else 237 / 125
n = 2
for which in ("lower", "upper"):
    O = LunarOracle(which, cache, log=lambda *a: None)
    A = np.eye(2)
    fr = O.frame(A, 1.0)
    Ls = fr["Ls"]
    out = {}
    N1, N2 = O.N1, O.N2
    kk = np.fft.fftfreq(N1, 1 / N1)[:, None] * np.ones((1, N2))
    ll = np.fft.fftfreq(N2, 1 / N2)[None, :] * np.ones((N1, 1))
    mult = 2j * math.pi * c * (O.om[0] * kk + O.om[1] * ll)
    sup = dict(Lt=0.0, N=0.0, Nt=0.0, T=0.0, Treal=0.0)
    for y in [(0.0, 0.0)] + O._corners(A, rho):
        L = O._eval_L(Ls, y)
        G = np.einsum("...ki,...kj->...ij", L, L)
        B = np.linalg.inv(G)
        N = np.einsum("ab,...bk,...kj->...aj", OM, L, B)
        DH, Hs = O._hess(y, A, 1.0, c)
        DX = np.einsum("ab,...bc->...ac", JX, Hs)
        # d_omega N on the shifted torus: the multiplier acts on the Fourier series of N(. + i y)
        DN = np.fft.ifft2(np.fft.fft2(N, axes=(0, 1)) * mult[:, :, None, None], axes=(0, 1))
        XN = np.einsum("...ab,...bj->...aj", DX, N) - DN
        T = np.einsum("...ai,ab,...bj->...ij", N, OM, XN)
        if y == (0.0, 0.0):
            sup["Treal"] = float(np.abs(T).sum(-1).max())
            continue
        sup["Lt"] = max(sup["Lt"], float(np.abs(L).sum(-2).max()))
        sup["N"] = max(sup["N"], float(np.abs(N).sum(-1).max()))
        sup["Nt"] = max(sup["Nt"], float(np.abs(N).sum(-2).max()))
        sup["T"] = max(sup["T"], float(np.abs(T).sum(-1).max()))
    # v1 derived values at the R1-type package (one regime: sampled sups + mu, as the optimizer's 'sup' regime)
    r = O.norms(A, 1.0, rho)
    M, parts = O.H_majorant(A, 1.0, c, rho, mu, r["sup"])
    sK = r["sup"]["sK"] + mu; sB = r["sup"]["sB"] + mu
    HT = 4 * n * M * sK ** 2 * sB ** 2 + 1
    Theta = 2 * n * sK * sB * (M + 1)
    print("%s (c = %.4f, rho = 1/70): M %.4f sK %.4f sB %.4f | H parts %s" % (
        which, c, M, sK, sB, {k: round(float(v), 4) for k, v in parts.items()}))
    print("   |L^T| %.4f (v1: 2 n sK = %.3f) | |N| %.4f (v1: sK sB = %.3f) | |N^T| %.4f (v1: 2 n sK sB = %.3f)" % (
        sup["Lt"], 2 * n * sK, sup["N"], sK * sB, sup["Nt"], 2 * n * sK * sB))
    print("   sup|T| strip %.4f, real torus %.4f (v1: H_T = 4 n M sK^2 sB^2 + 1 = %.2f) | |omega| %.4f (v1: Theta = %.2f)" % (
        sup["T"], sup["Treal"], HT, c * float(np.abs(O.om).max()), Theta))
