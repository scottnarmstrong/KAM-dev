#!/usr/bin/env python3
"""MAG-2b: the magnetic certificate data as objects of the sofx mirror (the `SO_CLIENT` module of sofx_gen.py;
untrusted tooling).

    SO_CLIENT=sofx_mag SO_DATA_DIR=<dir of mag_rot.json> SO_PREC=128 python3 sofx_gen.py mag OUTDIR

  angle 0  = u:  angleDeg 0, half (-i b/2) at the half keys of u = sum b sin
  angle 1  = 0
  action 0 = p:  zero p0, half (c/2);   action 1 = J: zero J0, half (j/2)
  character witnesses E_m = exp(2 pi i m u) under the normalized keys (m, 0), m = 2, 3 (pinHalvings 0)
  ham = magHamExpr (factored form: J + h(p) + eps (cos a + cos b) + (1427/3200) eps^2 (c1 cos a - c2 cos b)^2)
  params = magParams err disp (plan-magnetic-barrier §3.3 at eps = 3/2500; majorants from mag_threshold.py,
           thresholds.json rho = 3/1000, rounded up)
  freqBox = [(alpha/s0 +- r, (1/s0, 0)], alpha = (7913 - sqrt5)/13618, s0 = 500001/500000
"""
import json
import math
import os
import sys
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "spin_orbit"))
import sofx_arith as A          # noqa: E402
import sofx_model as M          # noqa: E402
import sofx_check as C          # noqa: E402
import adv_jet                  # noqa: E402
import sofx_lunar as SL         # noqa: E402  (shared helpers: toy_ops, gram inverse, pi enclosure, weight)

PREC = int(os.environ.get("SO_PREC", "128"))
DATA = os.environ.get("SO_DATA_DIR", "/mnt/HC_Volume_106379410/kam-data/mag")
HAM_NAME = "magHamExpr"

EPS = F(3, 2500)
KAPPA_C = F(1427, 3200)
C1, C2 = F(32000, 2777), F(96000, 7669)
S0 = F(500001, 500000)
KAPPA = 1 / S0                      # omega* = (alpha, 1)/s0
GAMMA = F(1, 10) / S0


def mag_ham_expr():
    """`magHamExpr` (the Lean tree, node for node)."""
    a0, a1 = ("action", 0), ("action", 1)
    h = ("add", a0, ("add", ("mul", ("const", F(-3, 4)), ("pow", a0, 2)),
                     ("add", ("mul", ("const", F(1, 3)), ("pow", a0, 3)),
                      ("mul", ("const", F(-1, 16)), ("pow", a0, 4)))))
    ca, cb = ("cosMode", (2, -1)), ("cosMode", (3, -2))
    V = ("add", ("mul", ("const", EPS), ("add", ca, cb)),
         ("mul", ("const", KAPPA_C * EPS ** 2),
          ("pow", ("add", ("mul", ("const", C1), ca), ("mul", ("const", -C2), cb)), 2)))
    return ("add", a1, ("add", h, V))


# package (mag_threshold.py at rho = 3/1000, sampled majorants x 1.05 + mu, rounded up; a design choice the
# checker verifies through checkHamBounds / checkEmbedding / checkGram / checkTorsion)
PKG = dict(rho=F(3, 1000), rhoInf=F(3, 1000000), M=F(85), sK=F(9, 5), sB=F(27, 10), sT=F(11, 5), mu=F(1, 500))


def magParams(err, disp):
    p = PKG
    return dict(tau=1, rho=p["rho"], rhoInf=p["rhoInf"], M=p["M"], sK=p["sK"], sB=p["sB"], sT=p["sT"], mu=p["mu"],
                gbar=GAMMA, som=F(2), nu=F(1, 10 ** 6), gamma=GAMMA, s=S0, err=F(err), E0=F(0), disp=F(disp))


lunarR1 = magParams                 # the name sofx_gen.py calls


SQRT5_DIGITS = 110
PIN_ORDER = 70


def magBox(d=SQRT5_DIGITS):
    """coordinate 0: alpha/s0 = (7913 - sqrt5)/(13618 s0) from a sqrt5 enclosure at 10^-d; coordinate 1: 1/s0."""
    lo, hi = SL.sqrt5_enclosure(d)
    mid = (lo + hi) / 2
    return [((7913 - mid) / 13618 * KAPPA, (hi - lo) / 2 / 13618 * KAPPA), (KAPPA, F(0))]


def jet():
    J = adv_jet.jet(2, mag_ham_expr())
    J["prog"] = [tuple(op) if op[0] != "char" else ("char", tuple(op[1])) for op in J["prog"]]
    return J


def build_embedding(B, d):
    sh = PREC - d["scale_bits"]
    assert sh >= 1
    v = sorted((int(k), int(l), int(x)) for k, l, x in d["v_sin"])
    p = {(int(k), int(l)): int(x) for k, l, x in d["p_cos"]}
    Jc = {(int(k), int(l)): int(x) for k, l, x in d["J_cos"]}
    angle0 = M.RealPoly(0, [((k, l), (0, -(x << (sh - 1)))) for k, l, x in v])
    angle1 = M.RealPoly(0, [])
    a0 = M.RealPoly(int(d["p0"]) << sh, [(kk, (p[kk] << (sh - 1), 0)) for kk in sorted(p)])
    a1 = M.RealPoly(int(d["J0"]) << sh, [(kk, (Jc[kk] << (sh - 1), 0)) for kk in sorted(Jc)])
    return M.Embedding([0, 0], [angle0, angle1], [0, 0], [a0, a1])


def build_E(d, m):
    sh = PREC - d["scale_bits"]
    return sorted(((int(k), int(l)), (int(x) << sh, 0)) for k, l, x in d["E%d_re" % m])


def load(which):
    with open(os.path.join(DATA, "%s_rot.json" % which)) as f:
        return json.load(f)


def build(which, err, disp, cfgFull, cfgLow, expHalvings=12, expOrder=30, S=None, graph=None):
    B = A.FixedB(PREC)
    d = load(which)
    c = C.Cert()
    c.B, c.which, c.n = B, which, 2
    c.params = magParams(err, disp)
    c.jet = jet()
    c.jetOps = c.jet["prog"]
    dom = d["domain"]
    rhoH = F(dom["rho_H"])
    c.expHalvings, c.expOrder = expHalvings, expOrder
    c.weightH = M.Weight(rhoH, SL.weight_for(rhoH, expHalvings, expOrder))
    rho = c.params["rho"]
    c.weight = M.Weight(rho, SL.weight_for(rho, expHalvings, expOrder))
    c.centre = [F(dom["c1"]), F(dom["c2"])]
    c.radius = [F(dom["r1"]), F(dom["r2"])]
    c.freqBox = magBox()
    c.emb = build_embedding(B, d)
    ph = int(d["character_witness"]["pinHalvings"])
    c.wit = M.Witnesses([], [], [((2, 0), (build_E(d, 2), ph, PIN_ORDER)), ((3, 0), (build_E(d, 3), ph, PIN_ORDER))])
    c.gramInv, c.gramParity = SL.build_gram_inv(d)
    c.piEnc = SL.pi_enclosure(B)
    c.cfgFull, c.cfgLow = cfgFull, cfgLow
    c.torsInv = S
    c.graph = graph
    c.DKc = C.dkCache(B, 2, c.emb, c.weight, c.piEnc)
    c.jetOps_toy = SL.toy_ops(c.jetOps)
    return c
