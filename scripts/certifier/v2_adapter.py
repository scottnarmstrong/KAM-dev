#!/usr/bin/env python3
"""SHARP-CERTSIDE: adapter from the optimizer's packages to the v2 mirror.

Untrusted design tooling.  The v2 mirror is `scripts/apost_sharp/thresholds_v2.py` of this checkout, found from this
file's own location; the environment variable KAM_V2_DIR overrides the directory.  It is imported read-only, from
exactly that directory (see `_load`).  `log10_threshold(pkg)` evaluates its full variant (A7: levers L1, L2, L3,
L8; route A; frequency-specific stage data, k = 5 stages) for the isoenergetic form, from the optimizer's package
plus the extra measured objects of the oracle (`extras`: |X_H|, |DX_H|, |D^2 X_H|, |Dh|, |D^2 h|, |L^T|, |N|,
|N^T|, sup |T|), all in the package's frame and time scale.
"""
import importlib, os, sys
import math
import numpy as np
from fractions import Fraction as F

V2_ENV = "KAM_V2_DIR"
DEFAULT_V2_DIR = os.path.join(os.path.dirname(os.path.dirname(os.path.realpath(__file__))), "apost_sharp")
_MIRROR = "thresholds_v2"
_MIRROR_MODULES = (_MIRROR, "thresholds", "smalldiv", "smalldiv_sup")   # the mirror and what it imports by bare name
_loaded = {}                                                            # mirror directory -> module


def v2_dir():
    """The mirror directory: KAM_V2_DIR if set, else this checkout's.  ImportError if it holds no mirror."""
    d = os.environ.get(V2_ENV, DEFAULT_V2_DIR)
    origin = "%s=%r" % (V2_ENV, d) if V2_ENV in os.environ else "the default %r" % d
    if not os.path.isfile(os.path.join(d, _MIRROR + ".py")):
        raise ImportError("v2 mirror not found: %s is not a directory containing %s.py (set %s to one, or unset it "
                          "to use %r)" % (origin, _MIRROR, V2_ENV, DEFAULT_V2_DIR))
    return os.path.realpath(d)


def _load():
    """The mirror of `v2_dir()`, one module per directory.  Every name of `_MIRROR_MODULES` resolves to that directory
    during the import: `scripts/certifier/smalldiv.py` shares its name with the mirror's `smalldiv`, and any entry
    already in `sys.modules` would otherwise be reused.  The caller's `sys.modules` entries and `sys.path` (the mirror
    extends it on import) are restored afterwards, also when the import fails."""
    d = v2_dir()
    if d not in _loaded:
        saved_path = list(sys.path)
        saved_mods = {m: sys.modules.pop(m) for m in _MIRROR_MODULES if m in sys.modules}
        try:
            sys.path.insert(0, d)
            importlib.invalidate_caches()
            mod = importlib.import_module(_MIRROR)
        except Exception as e:
            raise ImportError("v2 mirror in %r failed to import: %s: %s" % (d, type(e).__name__, e)) from e
        finally:
            sys.path[:] = saved_path
            for m in _MIRROR_MODULES:
                sys.modules.pop(m, None)
            sys.modules.update(saved_mods)
        _loaded[d] = mod
    return _loaded[d]


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
