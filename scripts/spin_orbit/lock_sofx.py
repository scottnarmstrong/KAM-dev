#!/usr/bin/env python3
"""LOCK-DATA: the N = 65 librational certificate (`TorusCertificate 2 (CertFixed 112)`) as the Python objects of the
sofx mirror, from LOCK-GEN-2's emitted JSON (lock_emit.py).  Untrusted tooling: the kernel checks everything.

The emitter leaves these fields to LOCK-DATA, and they are fixed here:
  * weightH, centre, radius: the ball-pass domain of the SO-LOCK-COST gate (GateLib.lean.inc, G2claim passed):
    rho_H = 1523/100000, centre (37/2500, 49986/100000), radius (2615/1000000, 109/100000); the weights' w are
    the smallest 30-decimal rationals passing `checkWeight` (expHalvings 12, expOrder 30);
  * freqBox: `lockN65Box`, the interval evaluation of `lunarRotFreqPlusN_eq 65 1`'s Q(sqrt 5) coefficients at a
    sqrt 5 enclosure of width 10^-SQRT5_DIGITS (the box radius enters the invariance defect through `freqModel`,
    so the R2 box's 10^-6 enclosure is far too coarse for err ~ 1e-19);
  * gramInv: an approximate inverse of the Gram matrix DK^T DK, by pointwise inversion on a grid (gram_inverse);
  * torsInv: sofx_gen.torsion_witness (in lock_gen.py);
  * the sqrt witnesses' RealPoly polynomials as full sorted CertPolys (toSortedPoly).
"""
import json
import os
from fractions import Fraction as F

import numpy as np

import sofx_arith as A
import sofx_model as M
import sofx_check as C
import sofx_lunar as SL
import lock_ham as LH
import lock_jet as LJ

DATA = os.environ.get("SO_LOCK_DATA", "/mnt/HC_Volume_106379410/kam-data/so-lock/data/lockN65.json")
N = 65
OMEGA = F(8, 65)
CS = [F(-3, 250000), F(-699, 2000000000), F(-883, 50000000000)]
RHO_H = F(1523, 100000)
CENTRE = [F(37, 2500), F(49986, 100000)]
RADIUS = [F(2615, 1000000), F(109, 100000)]
SQRT5_DIGITS = 60
GRAM_BITS = 48


def sqrt5_enclosure(d=SQRT5_DIGITS):
    import math
    D = 10 ** d
    a = math.isqrt(5 * D * D)
    return F(a, D), F(a + 1, D)


def plus_coeffs(kappa):
    """lunarRotFreqPlusN_eq 65 kappa: [[(2N-1) k / (2(N^2-N-1)), -k / (2(N^2-N-1))], [k]]."""
    D = 2 * (N * N - N - 1)
    return [[F(2 * N - 1) * kappa / D, -kappa / D], [kappa]]


def alg_box(coeffs, lo, hi):
    """lunarR2Box-style box (midpoint, half-width) of the interval evaluation (algRowLo/Hi, linear rows)."""
    out = []
    for row in coeffs:
        a = row[0]
        b = row[1] if len(row) > 1 else F(0)
        x, y = a + b * lo, a + b * hi
        rlo, rhi = min(x, y), max(x, y)
        out.append(((rlo + rhi) / 2, (rhi - rlo) / 2))
    return out


def jet(kappa):
    J = LJ.jet(2, LH.lock_ham_scaled(kappa, OMEGA, CS))
    J["prog"] = [tuple(LJ.norm_op(op)) if op[0] != "char" else ("char", tuple(op[1])) for op in J["prog"]]
    return J


def real_poly(d):
    return M.RealPoly(int(d["zero"]), [(tuple(k), (int(z[0]), int(z[1]))) for k, z in d["half"]])


def cpoly(L):
    return sorted((tuple(k), (int(z[0]), int(z[1]))) for k, z in L)


def params_of(p, err, disp):
    g = lambda k: F(p[k])
    return dict(tau=int(p["tau"]), rho=g("rho"), rhoInf=g("rhoInf"), M=g("M"), sK=g("sK"), sB=g("sB"),
                sT=g("sT"), mu=g("mu"), gbar=g("gbar"), som=g("som"), nu=g("nu"), gamma=g("gamma"), s=g("s"),
                err=F(err), E0=g("E0"), disp=F(disp))


def load(path=DATA):
    with open(path) as fh:
        return json.load(fh)


def build(err, disp, cfgFull, cfgLow, expHalvings=12, expOrder=30, gramInv=None, S=None, graph=None, d=None):
    d = d if d is not None else load()
    prec = int(d["precision"])
    B = A.FixedB(prec)
    c = C.Cert()
    c.B, c.which, c.n, c.prec = B, "lock", 2, prec
    p = d["params"]
    kappa = F(p["kappa"])
    c.kappa = kappa
    c.params = params_of(p, err, disp)
    c.jet = jet(kappa)
    c.jetOps = c.jet["prog"]
    assert len(c.jetOps) == int(d["ham"]["program_length"]), len(c.jetOps)
    c.expHalvings, c.expOrder = expHalvings, expOrder
    c.weightH = M.Weight(RHO_H, SL.weight_for(RHO_H, expHalvings, expOrder))
    rho = c.params["rho"]
    c.weight = M.Weight(rho, SL.weight_for(rho, expHalvings, expOrder))
    c.centre, c.radius = list(CENTRE), list(RADIUS)
    c.sqrt5 = sqrt5_enclosure()
    c.freqCoeffs = plus_coeffs(kappa)
    c.freqBox = alg_box(c.freqCoeffs, *c.sqrt5)
    e = d["emb"]
    c.emb = M.Embedding([int(x) for x in e["angleDeg"]], [real_poly(x) for x in e["angle"]],
                        [int(x) for x in e["actionDeg"]], [real_poly(x) for x in e["action"]])
    w = d["wit"]
    expWit = [(cpoly(x["poly"]), int(x["pinHalvings"]), int(x["pinOrder"])) for x in w["expWit"]]
    invWit = [cpoly(x) for x in w["invWit"]]
    charWit = [(tuple(k), (cpoly(x["poly"]), int(x["pinHalvings"]), int(x["pinOrder"]))) for k, x in w["charWit"]]
    sqrtWit = [(int(s), (M.toSortedPoly(B, 2, real_poly(x["poly"])), F(x["anchor"]), F(x["margin"])))
               for s, x in w["sqrtWit"]]
    c.wit = M.Witnesses(expWit, invWit, charWit, sqrtWit)
    c.piEnc = SL.pi_enclosure(B)
    c.cfgFull, c.cfgLow = cfgFull, cfgLow
    c.DKc = C.dkCache(B, 2, c.emb, c.weight, c.piEnc)
    c.gramInv = gramInv if gramInv is not None else gram_inverse(B, c)
    c.torsInv = S
    c.graph = graph
    return c


def grid_eval(B, poly, N0, N1):
    """the trigonometric polynomial (2-d keys) on the N0 x N1 grid (float, complex)."""
    G = np.zeros((N0, N1), dtype=np.complex128)
    for (k0, k1), (re, im) in poly:
        G[k0 % N0, k1 % N1] += complex(float(B.val(re)), float(B.val(im)))
    return np.fft.ifft2(G) * (N0 * N1)


def gram_inverse(B, c, N0=1024, N1=256, tol=2.0 ** -GRAM_BITS):
    """An approximate inverse of G = DK^T DK as CertPolys at 2^-GRAM_BITS (checkGram verifies whatever is sent)."""
    n = c.n
    DK = C.dkModels(B, n, c.DKc)
    vals = [[grid_eval(B, M.toDeg(B, c.weight, c.piEnc, 0, C.entry(DK, r, j, B)).poly, N0, N1) for j in range(n)]
            for r in range(n + n)]
    G = np.zeros((N0, N1, n, n), dtype=np.complex128)
    for a in range(n):
        for b in range(n):
            G[:, :, a, b] = sum(vals[r][a] * vals[r][b] for r in range(n + n))
    Gi = np.linalg.inv(G)
    sc = 2 ** GRAM_BITS
    out = []
    for i in range(n):
        row = []
        for j in range(n):
            co = np.fft.fft2(Gi[:, :, i, j]) / (N0 * N1)
            terms = []
            for k0 in range(N0):
                for k1 in range(N1):
                    z = co[k0, k1]
                    if abs(z) < tol:
                        continue
                    kk = (k0 if k0 < N0 // 2 else k0 - N0, k1 if k1 < N1 // 2 else k1 - N1)
                    re, im = round(z.real * sc), round(z.imag * sc)
                    if re or im:
                        terms.append((kk, (B.ofRatDown(F(re, sc)), B.ofRatDown(F(im, sc)))))
            row.append(sorted(terms))
        out.append(row)
    return out
