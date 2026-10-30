#!/usr/bin/env python3
"""SO-DATA-1: the lunar certificate data (`SoGraphCert SoBackend`, SoBackend = CertFixed 320) built from SO-GEN2's
R1 candidates, as the Python objects of the sofx mirror (untrusted tooling).

    K'(psi, phi) = (psi + v/(2 pi), phi, p, p + J)     (rotated frame, owner ruling O5)

  angle 0  = v/(2pi): angleDeg -1, CertRealPoly zero 0, half (-i b/2) at the half keys of v = Σ b sin
  angle 1  = 0:       angleDeg 0, CertRealPoly zero 0, half []      (normKey zeroes coordinate 1)
  action 0 = p:       actionDeg 0, zero p0, half (c/2) of p = p0 + Σ c cos
  action 1 = p + J:   actionDeg 0, zero p0 + J0, half (c + j)/2
  one character witness E ≈ exp(2 i v) under the normalized key (2, 0) (pinHalvings 0, pinOrder 1)
  ham = soRotHamExprScaled (237/125) (jet: adv_jet.py, the mirror of the landed compiler)
  params = lunarR1 err disp

All mantissas are exact at 2^-320 (v, p, E at 2^-318; J at 2^-319; B at 2^-48).
"""
import json
import os
from fractions import Fraction as F

import sofx_arith as A
import sofx_model as M
import sofx_check as C
import adv_jet
import model as MD

PREC = int(os.environ.get("SO_PREC", "320"))      # SO-GEN3: env override (fixed-point bits)
HERE = os.path.dirname(os.path.abspath(__file__))
DATA = os.environ.get("SO_DATA_DIR", os.path.join(HERE, "..", "..", "certificates", "lunar-spin-orbit"))   # SO-GEN3

TIME_SCALE = F(237, 125)            # lunarR1TimeScale
SCALAR = 1 + F(1, 10 ** 6)          # lunarR1Scalar
# SO-GEN3: a package R2 may be given as a JSON file (env SO_PKG) with string rationals
# c, rho, rhoInf, M, sK, sB, sT, mu, gden (gamma = gbar = kappa/gden); absent: R1.
_PKG = json.load(open(os.environ["SO_PKG"])) if os.environ.get("SO_PKG") else None
if _PKG:
    TIME_SCALE = F(_PKG["c"])
KAPPA = TIME_SCALE / SCALAR         # lunarR1Kappa
DEN_NU, A_NU = MD.DEN_NU, MD.A_NU   # nu = (DEN_NU -+ A_NU +- sqrt5)/DEN_NU (3118, 79 at N = 40)


def lunarR1(err, disp):
    if _PKG:
        g = KAPPA / F(_PKG["gden"])
        return dict(tau=1, rho=F(_PKG["rho"]), rhoInf=F(_PKG["rhoInf"]), M=F(_PKG["M"]), sK=F(_PKG["sK"]),
                    sB=F(_PKG["sB"]), sT=F(_PKG["sT"]), mu=F(_PKG["mu"]), gbar=g, som=F(2), nu=F(1, 10 ** 6),
                    gamma=g, s=SCALAR, err=F(err), E0=F(0), disp=F(disp))
    return dict(tau=1, rho=F(1, 70), rhoInf=F(1, 70000), M=F(203, 100), sK=F(1987, 1000), sB=F(1987, 1000),
                sT=F(1987, 1000), mu=F(1, 160), gbar=KAPPA / 42, som=F(2), nu=F(1, 10 ** 6), gamma=KAPPA / 42,
                s=SCALAR, err=F(err), E0=F(0), disp=F(disp))


def lunarR1Box(a, b):
    """lunarR1Box a b (LunarParams.lean): √5 ∈ 2236068e-6 ± 1e-6."""
    a, b = F(a), F(b)
    return [(KAPPA * ((a + b * F(2236068, 10 ** 6)) / 3118 - 1), KAPPA * abs(b) / 3118 / 10 ** 6), (KAPPA, F(0))]


SQRT5_DIGITS = 110
PIN_ORDER = 70


def sqrt5_enclosure(d=SQRT5_DIGITS):
    """lo <= √5 <= hi, both with denominator 10^d (checkRootEnclosure 2 5 lo hi)."""
    import math
    D = 10 ** d
    a = math.isqrt(5 * D * D)
    return F(a, D), F(a + 1, D)


def lunarBox(a, b, d=SQRT5_DIGITS):
    """The production frequency box around lunarRotFreq ν κ, ν = (a + b √5)/3118, from a √5 enclosure at 10^-d:
    coordinate 0 is κ(ν - 1) (centre at the midpoint of √5, radius κ|b| (hi - lo)/2/3118), coordinate 1 is κ."""
    a, b = F(a), F(b)
    lo, hi = sqrt5_enclosure(d)
    mid = (lo + hi) / 2
    return [(KAPPA * ((a + b * mid) / DEN_NU - 1), KAPPA * abs(b) * (hi - lo) / 2 / DEN_NU), (KAPPA, F(0))]


def jet():
    epsA = {m: MD.EPS * MD.A_EXACT[m] for m in MD.M_MODES}
    J = adv_jet.jet(2, adv_jet.so_rot_ham_expr_scaled(TIME_SCALE, epsA))
    J["prog"] = [tuple(op) if op[0] != "char" else ("char", tuple(op[1])) for op in J["prog"]]
    return J


def toy_ops(prog):
    """the jet program in toy_arith.slp_balls format."""
    out = []
    for op in prog:
        t = op[0]
        if t == "const":
            out.append(("C", op[1], op[2], op[3]))
        elif t == "action":
            out.append(("A", op[1]))
        elif t == "char":
            out.append(("X", list(op[1])))
        elif t == "add":
            out.append(("+", op[1], op[2]))
        elif t == "mul":
            out.append(("*", op[1], op[2]))
        else:
            raise ValueError(op)
    return out


def half_key(k, l):
    return (k, l) > (0, 0)


def build_embedding(B, d):
    sh = PREC - d["scale_bits"]
    assert sh >= 1
    v = sorted((int(k), int(l), int(x)) for k, l, x in d["v_sin"])
    p = {(int(k), int(l)): int(x) for k, l, x in d["p_cos"]}
    Jc = {(int(k), int(l)): int(x) for k, l, x in d["J_cos"]}
    shJ = PREC - d["J0_scale_bits"]
    for k, l, _ in v:
        assert half_key(k, l)
    # b sin = (-i b/2) e_k + c.c. ; mantissa at 2^-320: b * 2^sh / 2
    angle0 = M.RealPoly(0, [((k, l), (0, -(x << (sh - 1)))) for k, l, x in v])
    angle1 = M.RealPoly(0, [])
    p0 = int(d["p0"]) << sh
    J0 = int(d["J0"]) << shJ
    a0 = M.RealPoly(p0, [(kk, (p[kk] << (sh - 1), 0)) for kk in sorted(p)])
    keys = sorted(set(p) | set(Jc))
    a1 = M.RealPoly(p0 + J0, [(kk, ((p.get(kk, 0) << (sh - 1)) + (Jc.get(kk, 0) << (sh - 1)), 0))
                              for kk in keys])
    for kk in keys:
        assert half_key(*kk)
    return M.Embedding([-1, 0], [angle0, angle1], [0, 0], [a0, a1])


def build_E(d):
    sh = PREC - d["scale_bits"]
    return sorted(((int(k), int(l)), (int(x) << sh, 0)) for k, l, x in d["E_re"])


def build_gram_inv(d):
    gi = d["gram_inverse"]
    sh = PREC - gi["scale_bits"]

    def poly(rows):
        m = {(int(k), int(l)): int(x) for k, l, x in rows}
        odd = all(m.get((-k, -l), 0) == -x for (k, l), x in m.items())
        even = all(m.get((-k, -l), 0) == x for (k, l), x in m.items())
        if not (odd or even):
            # SO-GEN3: an approximate inverse with a few parity-broken rounding coefficients is projected onto its
            # dominant parity (B is untrusted witness data; checkGram verifies whatever is sent)
            so = sum(abs(x - m.get((-k, -l), 0)) for (k, l), x in m.items())
            se = sum(abs(x + m.get((-k, -l), 0)) for (k, l), x in m.items())
            sg = -1 if so > se else 1
            keys = set(m) | {(-k, -l) for (k, l) in m}
            m = {kk: (m.get(kk, 0) + sg * m.get((-kk[0], -kk[1]), 0)) // 2 for kk in keys}
            m = {kk: x for kk, x in m.items() if x}
            m = {kk: (x if kk > (0, 0) or sg == 1 or kk == (0, 0) else -m.get((-kk[0], -kk[1]), 0))
                 for kk, x in m.items()}
            for kk in list(m):
                if kk > (0, 0):
                    m[(-kk[0], -kk[1])] = sg * m[kk]
            m = {kk: x for kk, x in m.items() if x}
            odd, even = sg == -1, sg == 1
        # rotlib phase 1 (odd) means i * real
        return sorted(((k, l), ((0, x << sh) if (odd and not even) else (x << sh, 0))) for (k, l), x in m.items()
                      ), ("odd" if odd and not even else "even")
    B11, p11 = poly(gi["B11"])
    B12, p12 = poly(gi["B12"])
    B22, p22 = poly(gi["B22"])
    return [[B11, B12], [B12, B22]], (p11, p12, p22)


def pi_enclosure(B, k=72, j=21):
    lo, up = A.piLowRat(k, j), A.piUpRat(k, j)
    centre = B.ofRatDown((lo + up) / 2)
    rad = B.upAdd(B.ofRatUp((up - lo) / 2), 4)
    return A.PiEnclosure(centre, rad, k, j)


def weight_for(rho, s, N, digits=30):
    """a rational w >= ratExpUp(2 piUpQ rho, s, N), rounded up at `digits` decimals."""
    x = M.ratExpUp(2 * A.PI_UP * F(rho), s, N)
    D = 10 ** digits
    return F(-((-x.numerator * D) // x.denominator), D)


def load(which):
    with open(os.path.join(DATA, "%s_rot.json" % which)) as f:
        return json.load(f)


def build(which, err, disp, cfgFull, cfgLow, expHalvings=12, expOrder=30, S=None, graph=None):
    """The certificate (sofx_check.Cert) on the FixedB(320) backend."""
    B = A.FixedB(PREC)
    d = load(which)
    c = C.Cert()
    c.B, c.which, c.n = B, which, 2
    c.params = lunarR1(err, disp)
    c.jet = jet()
    c.jetOps = c.jet["prog"]
    dom = d["domain"]
    rhoH = F(dom["rho_H"])
    c.expHalvings, c.expOrder = expHalvings, expOrder
    c.weightH = M.Weight(rhoH, weight_for(rhoH, expHalvings, expOrder))
    rho = c.params["rho"]
    c.weight = M.Weight(rho, weight_for(rho, expHalvings, expOrder))
    c.centre = [F(dom["c1"]), F(dom["c2"])]
    c.radius = [F(dom["r1"]), F(dom["r2"])]
    c.freqBox = lunarBox(DEN_NU - A_NU, 1) if which == "lower" else lunarBox(DEN_NU + A_NU, -1)
    c.emb = build_embedding(B, d)
    E = build_E(d)
    cw = d["character_witness"]
    # pinOrder: SO-GEN2 recorded 1, but certCExp always adds eRem(N + 1) (3/4 at N = 1); at N = PIN_ORDER the
    # Taylor remainder eRem(71) ~ 1e-102 (the pin ball itself is exactly 0: v is odd)
    c.wit = M.Witnesses([], [], [((2, 0), (E, int(cw["pinHalvings"]), PIN_ORDER))])
    c.gramInv, c.gramParity = build_gram_inv(d)
    c.piEnc = pi_enclosure(B)
    c.cfgFull, c.cfgLow = cfgFull, cfgLow
    c.torsInv = S
    c.graph = graph
    c.DKc = C.dkCache(B, 2, c.emb, c.weight, c.piEnc)
    # the jet in toy format for checkHamBounds
    c.jetOps_toy = toy_ops(c.jetOps)
    return c


def S_from_rationals(B, rows):
    return [[(B.ofRatDown(F(x)), B.ofInt(0)) for x in r] for r in rows]
