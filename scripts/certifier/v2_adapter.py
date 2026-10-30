#!/usr/bin/env python3
"""SHARP-CERTSIDE: adapter from the optimizer's packages to the v2 mirror of SHARP-PLUS.

Untrusted design tooling.  The v2 mirror is `scripts/apost_sharp/thresholds_v2.py` of branch `sharp-plus`
(work in progress when this was written; path in the environment variable KAM_V2_DIR, default the sharp-plus
worktree).  It is imported read-only.  `log10_threshold(pkg)` evaluates its full variant (A7: levers L1, L2, L3,
L8; route A; frequency-specific stage data, k = 5 stages) for the isoenergetic form, from the optimizer's package
plus the extra measured objects of the oracle (`extras`: |X_H|, |DX_H|, |D^2 X_H|, |Dh|, |D^2 h|, |L^T|, |N|,
|N^T|, sup |T|), all in the package's frame and time scale.
"""
import os, sys, math
import numpy as np
from fractions import Fraction as F

V2_DIR = os.environ.get("KAM_V2_DIR", "/home/scott/KAM-dev-worktrees/sharp-plus/scripts/apost_sharp")
_mod = None


def _load():
    global _mod
    if _mod is None:
        sys.path.insert(0, V2_DIR)
        import thresholds_v2 as T2                             # noqa: E402  (read-only use)
        _mod = T2
        sys.path.pop(0)
    return _mod


def q(x):
    return F(x).limit_denominator(10 ** 12) if not isinstance(x, F) else x


def extras(O, A, lam, c, rho, regime="corner"):
    """Measured frame objects (sampled sup on the distinguished boundary, x 1.01 margin for 'corner'/'sup';
    the corner bound of these analytic objects is within 0.1 % of the sampled sup on R1, see v2_majorants.py)."""
    from lunar_oracle import OM, JX
    A = np.asarray(A, float)
    fr = O.frame(A, lam)
    N1, N2 = O.N1, O.N2
    kk = np.fft.fftfreq(N1, 1 / N1)[:, None] * np.ones((1, N2))
    ll = np.fft.fftfreq(N2, 1 / N2)[None, :] * np.ones((N1, 1))
    mult = 2j * math.pi * c * (O.om[0] * kk + O.om[1] * ll)
    sup = dict(Lt=0.0, N=0.0, Nt=0.0, T=0.0)
    for y in O._corners(A, rho):
        L = O._eval_L(fr["Ls"], y)
        B = np.linalg.inv(np.einsum("...ki,...kj->...ij", L, L))
        N = np.einsum("ab,...bk,...kj->...aj", OM, L, B)
        DH, Hs = O._hess(y, A, lam, c)
        DX = np.einsum("ab,...bc->...ac", JX, Hs)
        DN = np.fft.ifft2(np.fft.fft2(N, axes=(0, 1)) * mult[:, :, None, None], axes=(0, 1))
        T = np.einsum("...ai,ab,...bj->...ij", N, OM, np.einsum("...ab,...bj->...aj", DX, N) - DN)
        sup["Lt"] = max(sup["Lt"], float(np.abs(L).sum(-2).max()))
        sup["N"] = max(sup["N"], float(np.abs(N).sum(-1).max()))
        sup["Nt"] = max(sup["Nt"], float(np.abs(N).sum(-2).max()))
        sup["T"] = max(sup["T"], float(np.abs(T).sum(-1).max()))
    return {k: v * 1.01 for k, v in sup.items()}


def log10_threshold(pkg):
    T2 = _load()
    v1 = T2.v1
    mu = q(pkg["mu"]); c = q(pkg["c"]); s = q(pkg["s"])
    H = pkg["Hparts"]; X = pkg["extras"]
    D = dict(n=2, tau=1, kappa=1, rho=q(pkg["rho"]), rhoinf=q(pkg["rhoinf"]), gamma=q(pkg["gamma"]),
             gbar=q(pkg["gamma"]), mu=mu, nu=q(pkg["nu"]), M=q(pkg["M"]), sK=q(pkg["sK"]), sB=q(pkg["sB"]),
             sT=q(pkg["sT"]), M0=q(H["XH"]), M1=q(H["DXH"]), M2=q(H["D2XH"]), Mh1=q(H["dH"]), Mh2=q(H["D2H"]),
             sLt=q(X["Lt"]) + mu, sN=q(X["N"]) + mu, sNt=q(X["Nt"]) + mu, Tsup=q(X["T"]),
             omega_star=tuple(float(x) for x in pkg["omega_star"]))
    D["Theta_omega"] = q(pkg["sigma_omega"]) * q(float(np.abs(pkg["omega_star"]).max()))
    for k_, base in (("B", D["sB"]), ("Tinv", D["sT"]), ("Lt", D["sLt"]), ("N", D["sN"]), ("Nt", D["sNt"]),
                     ("Tsup", D["Tsup"])):
        D["bud_" + k_] = base / 10
    o = dict(L1=True, torsion_cap="Tsup", omega_eta=True, avg_full_bite=True, keep_delta=True, caps_tilde=True,
             free_budgets=True)
    Dv = T2.with_caps(D, F(1, 20))
    o["torsion_cap"] = Dv.get("Tsup_cap", D["Tsup"]); o["torsion_real"] = o["torsion_cap"]
    st, ct = T2.c_stages(Dv, "freq")
    lx, d0, why = T2.thresholdA(Dv, o, True, k=5, c_stage=st, c_tail=ct)
    return lx
