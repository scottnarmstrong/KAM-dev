#!/usr/bin/env python3
"""SO-V2PKG: sampled frame majorants of a rotated-frame lunar torus, for the refined claim `RefClaim` of
KAM/CertificateSharp/V2/RefinedFacts.lean (untrusted design tooling; NOT a check).

    SO_N=65 python3 -I v2_frame.py V256.npy lower|upper [rho] [c]

Input: the double-precision torus v on the 256 x 64 grid (g3_double.py, archived in kam-data/so-gen3/g3).
Rotated frame (rot_build.py): K'(psi, phi) = (psi + v/2pi, phi, p, p + J), p = nu + Dt v,
J = -p^2/2 + sum_m eps A_m cos(2 pi (2 psi + (2-m) phi) + 2 v), H = c H', H' = P1^2/2 - P1 + P2 + V,
V(Q) = -sum_m eps A_m cos(2 pi s_m.Q), s_m = (2, 2-m); the invariance frequency is s omega* = c (nu - 1, 1).

The frozen objects (KAM/Torus/Objects.lean, KAM/Matrix/Norms.lean, the frozen X_h and extendedTorsion):
  L = DK (4 x 2), G = L^T L (bilinear), B = G^-1, Omega0 = [[0, -I], [I, 0]], N = Omega0 L B,
  X_h = (H_P, -H_Q), A = DX_h(K), T = N^T Omega0 (A N - d_omega N).
The claim's sums (FrameFacts): bL = max_j sum_r |L_rj|, bN = max_r sum_j |N_rj|, bNt = max_j sum_r |N_rj|,
bT = max_i sum_j |T_ij|; each sampled on the real grid shifted to the four corners Im theta = (+-rho, +-rho)
(the sums of moduli of holomorphic functions are plurisubharmonic, so the distinguished boundary carries the sup),
then x 1.01 as in scripts/certifier/v2_adapter.py.  Validation: the real average of T against the certified
torsion centre of the SO-GEN3 sofx run.
"""
import sys, json, math
import numpy as np
import model

TWO_PI = 2 * math.pi


def measure(v, which, rho=1 / 140, c=2.0):
    nx, nt = v.shape
    x, y = model.nu_minus_one(which)
    s = float(x) + float(y) * math.sqrt(5.0)
    nu = 1 + s
    k = np.fft.fftfreq(nx, 1.0 / nx)[:, None] * np.ones((1, nt))
    l = np.fft.fftfreq(nt, 1.0 / nt)[None, :] * np.ones((nx, 1))
    mask = np.ones((nx, nt)); mask[nx // 2, :] = 0; mask[:, nt // 2] = 0
    vh = np.fft.fft2(v) * mask
    psi = (np.arange(nx) / nx)[:, None] * np.ones((1, nt))
    phi = (np.arange(nt) / nt)[None, :] * np.ones((nx, 1))
    epsA = {m: float(model.EPS * model.A_EXACT[m]) for m in model.M_MODES}
    lam = s * k + l                                          # Dt symbol / i (index units)
    sup = dict(Lt=0.0, N=0.0, Nt=0.0, T=0.0)
    Tavg = None
    for y1, y2 in [(0.0, 0.0), (rho, rho), (rho, -rho), (-rho, rho), (-rho, -rho)]:
        sh = np.exp(-TWO_PI * (k * y1 + l * y2))
        ev = lambda fh: np.fft.ifft2(fh * sh)                    # evaluation on the shifted grid
        dpsi = lambda f: np.fft.ifft2(np.fft.fft2(f) * mask * (1j * TWO_PI * k))
        dphi = lambda f: np.fft.ifft2(np.fft.fft2(f) * mask * (1j * TWO_PI * l))
        dom = lambda f: c * np.fft.ifft2(np.fft.fft2(f) * mask * (1j * TWO_PI * lam))   # d_omega, omega = c(nu-1,1)
        V = ev(vh)
        Vpsi, Vphi = ev(vh * 1j * TWO_PI * k), ev(vh * 1j * TWO_PI * l)
        P = nu + ev(vh * 1j * lam)
        zpsi, zphi = psi + 1j * y1, phi + 1j * y2
        J = -P ** 2 / 2 + sum(epsA[m] * np.cos(TWO_PI * (2 * zpsi + (2 - m) * zphi) + 2 * V) for m in epsA)
        Ppsi, Pphi = dpsi(P), dphi(P)
        Jpsi, Jphi = dpsi(J), dphi(J)
        L = np.zeros((nx, nt, 4, 2), complex)
        L[..., 0, 0] = 1 + Vpsi / TWO_PI; L[..., 0, 1] = Vphi / TWO_PI
        L[..., 1, 1] = 1
        L[..., 2, 0] = Ppsi; L[..., 2, 1] = Pphi
        L[..., 3, 0] = Ppsi + Jpsi; L[..., 3, 1] = Pphi + Jphi
        G = np.einsum("...ri,...rj->...ij", L, L)
        B = np.linalg.inv(G)
        Om = np.zeros((4, 4)); Om[0, 2] = Om[1, 3] = -1; Om[2, 0] = Om[3, 1] = 1
        N = np.einsum("ab,...bk,...kj->...aj", Om, L, B)
        Q1 = zpsi + V / TWO_PI
        Q2 = zphi
        VQQ = np.zeros((nx, nt, 2, 2), complex)
        for m, a in epsA.items():
            sv = np.array([2.0, 2.0 - m])
            cosm = np.cos(TWO_PI * (2 * Q1 + (2 - m) * Q2))
            VQQ += a * TWO_PI ** 2 * cosm[..., None, None] * np.outer(sv, sv)
        A = np.zeros((nx, nt, 4, 4), complex)
        A[..., 0, 2] = c                                     # dX_Q/dP = H_PP (P1 block)
        A[..., 2:, :2] = -c * VQQ                            # dX_P/dQ = -H_QQ
        DN = np.stack([np.stack([dom(N[..., a, j]) for j in range(2)], -1) for a in range(4)], -2)
        XN = np.einsum("...ab,...bj->...aj", A, N) - DN
        T = np.einsum("...ai,ab,...bj->...ij", N, Om, XN)
        if y1 == 0.0 and y2 == 0.0:
            Tavg = T.mean(axis=(0, 1))
            continue
        sup["Lt"] = max(sup["Lt"], float(np.abs(L).sum(-2).max()))
        sup["N"] = max(sup["N"], float(np.abs(N).sum(-1).max()))
        sup["Nt"] = max(sup["Nt"], float(np.abs(N).sum(-2).max()))
        sup["T"] = max(sup["T"], float(np.abs(T).sum(-1).max()))
    return dict(sampled=sup, claim={kk: vv * 1.01 for kk, vv in sup.items()},
                Tavg=[[complex(z).real for z in row] for row in Tavg], s=s)


if __name__ == "__main__":
    v = np.load(sys.argv[1])
    which = sys.argv[2]
    rho = eval(sys.argv[3]) if len(sys.argv) > 3 else 1 / 140
    c = float(sys.argv[4]) if len(sys.argv) > 4 else 2.0
    print(json.dumps(measure(v, which, rho, c)))
