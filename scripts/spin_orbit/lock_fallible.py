#!/usr/bin/env python3
"""LOCK-DATA (B1): the values the forced exp / inv / sqrt segments of the lock memoize (untrusted tooling).

For every `exp`, `inv` and `sqrt` slot of both chains, the inputs of the lock-owned routes of
`KAM/SpinOrbit/Data/LockN65/SegRoutes.lean`, computed by the bit-exact mirror on the run's own states:

  exp  (composeStep_exp_eq, expWitnessRadius_eq_of_pin, expWitnessRadiusOf_eq_of_residuals):
       k = nExp, the operand slot a, the pin ball `out`, mB, mEta, the residuals res[j], the radius r
  inv  (composeStep_inv_eq, invWitnessRadius_eq_of_delta): k = nInv, a, delta, t, r (none when the check fails)
  sqrt (composeStep_sqrt_eq, sqrtWitnessRadius_eq_of_residual): the slot, a, the residual bound e, r

    SO_LOCK_DATA=... SO_LOCK_SIZE=... python3 lock_fallible.py GENDIR OUT.pkl
"""
import os
import pickle
import sys
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import lock_seg as LSG       # noqa: E402
import sofx_model as M       # noqa: E402
import sofx_arith as A       # noqa: E402


def exp_values(B, n, W, cfg, pe, st, op, wit):
    k = st.nExp
    E = wit.expWit[k]
    g = M.toDeg(B, W, pe, 0, st.slot(B, W, op[1])[0])
    z, zr = M.expPinBall(B, g)
    out = A.certCExpReduced(B, z, zr, E[1], E[2])
    info = {}
    r = M.expWitnessRadiusOf(B, n, W, cfg.forWitness(1, k), g, E[0], out, info)
    return dict(op="exp", k=k, a=op[1], out=out, mB=info["mB"], mEta=info["mEta"], res=info["res"], r=r)


def inv_values(B, n, W, cfg, pe, st, op, wit):
    k = st.nInv
    Q = wit.invWit[k]
    b = st.slot(B, W, op[1])[0]
    cw = cfg.forWitness(2, k)
    d = M.oneSubSupUp(B, W, M.model_mul(B, W, cw, (2,), M.Model(0, Q, B.ofInt(0)), M.Model(0, b.poly, b.rad)))
    t = M.recipOneSubUp(B, d)
    r = M.invWitnessRadius(B, n, W, cw, b, Q)
    assert r is not None and B.blt(d, B.ofInt(1))
    return dict(op="inv", k=k, a=op[1], delta=d, t=t, r=r)


def sqrt_values(B, n, W, cfg, pe, st, op, wit):
    slot = len(st.slots)
    idx = next(i for i, e in enumerate(wit.sqrtWit) if e[0] == slot)
    S = wit.sqrtWit[idx][1]
    poly, s, d = S[0], F(S[1]), F(S[2])
    g = M.toDeg(B, W, pe, 0, st.slot(B, W, op[1])[0])
    cw = cfg.forWitness(3, slot)
    Wm = M.Model(0, poly, B.ofInt(0))
    res = M.model_add(B, W, g, M.model_mul(B, W, cw, (3,), M.constModel(B, n, -1, 0, 0),
                                           M.model_mul(B, W, cw, (3,), Wm, Wm)))
    e = M.supBound(B, W, res)
    r = M.sqrtWitnessRadius(B, n, W, cw, g, S)
    assert r == B.upMul(e, B.ofRatUp(1 / (s - d)))
    return dict(op="sqrt", slot=slot, idx=idx, a=op[1], e=e, r=r)


FUN = dict(exp=exp_values, inv=inv_values, sqrt=sqrt_values)


def main(gdir, out):
    c, d = LSG.lock_cert(gdir)
    B, n, W, pe = c.B, c.n, c.weight, c.piEnc
    res = {}
    for tag, cfg in (("cfgFull", c.cfgFull), ("cfgLow", c.cfgLow)):
        st = M.ComposeState()
        vals = {}
        for i, op in enumerate(c.jetOps):
            if op[0] in FUN:
                vals[i] = FUN[op[0]](B, n, W, cfg, pe, st, op, c.wit)
            assert M.composeStep(B, n, c.emb, c.wit, W, cfg, pe, st, op) is not None, (tag, i)
            if op[0] in FUN:
                # the memoized radius is the one the step used
                assert st.slots[-1][0].rad == vals[i]["r"], (tag, i)
        res[tag] = vals
        print(tag, {o: sum(1 for v in vals.values() if v["op"] == o) for o in FUN}, flush=True)
    pickle.dump(res, open(out, "wb"))


if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2])
