#!/usr/bin/env python3
"""LOCK-DATA, SOS option (a), additive form (UPDATE 4): packed advice for the two SOS squares under per-side keys,
and the mirror re-check of the graph margins with the K semantics (untrusted tooling; the kernel checks everything).

    SO_LOCK_DATA=... SO_LOCK_SIZE=... python3 lock_sosk.py GENDIR OUTGENDIR [BUDGET_EXP]

`checkRealLowerBoundK W cfg key f m₀ m g` (RealLowerK.lean) is `checkRealLowerBound` with the product key `key`
in place of `[7]`: the square `g g*` is looked up under `key` in `cfg.advice ++ [(key, .direct)]`.  The lock uses
`[7, 0]` (mono; no advice: direct, as before), `[7, 1]` (pLo) and `[7, 2]` (pHi), with packed entries for the last
two appended at the END of the cfgLow book (every other lookup is unchanged).  This script

  1. generates the packed advice of `g g*` for pLo and pHi (the mirror's generator, budget 10^-BUDGET_EXP),
  2. checks it with the exact landed checks (mulPacked through checkPackedProduct, every part and shard),
  3. evaluates the three graph checks with the K semantics (the advice found under each key) and prints the
     margins, beside the direct-product margins of the current certificate,
  4. only when all three pass: writes OUTGENDIR/gen.pkl = GENDIR's with the two entries appended to cfgLow.
"""
import os
import pickle
import sys
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.set_int_max_str_digits(0)
import lock_seg as LSG       # noqa: E402
import sofx_model as M       # noqa: E402
import sofx_check as C       # noqa: E402
import sofx_packed as PK     # noqa: E402

KEYS = {"mono": (7, 0), "pLo": (7, 1), "pHi": (7, 2)}


def realLowerModelK(B, W, cfg, key, f, m0, g):
    """sofx_check.realLowerModel with the product key `key` (and `cfg.advice ++ [(key, direct)]`)."""
    cfg2 = cfg.withExtra(key, ("direct",))
    gg = M.model_mul(B, W, cfg2, key, M.Model(0, g, B.ofInt(0)), M.Model(0, C.conjSorted(B, g), B.ofInt(0)))
    G = M.model_mul(B, W, cfg2, key, gg, C.ofConst(B, C.keyLen(g), B.ofInt(-2), B.ofInt(0)))
    c = B.ofRatUp(-2 * F(m0))
    ln = C.keyLen(g) if not f.poly else C.keyLen(f.poly)
    star = M.Model(f.deg, C.conjSorted(B, f.poly), f.rad)
    return M.model_add(B, W, M.model_add(B, W, M.model_add(B, W, f, star), G),
                       C.ofConst(B, ln, c, B.upAdd(c, B.neg(B.ofRatDown(-2 * F(m0))))))


def margin(B, W, model, m0, m):
    sb = M.supBound(B, W, model)
    rhs = B.ofRatDown(2 * (F(m0) - F(m)))
    return B.ble(sb, rhs), C.val(B, rhs) - C.val(B, sb)


def main(gdir, odir, bexp=16):
    c, _d = LSG.lock_cert(gdir)
    g = pickle.load(open(os.path.join(gdir, "gen.pkl"), "rb"))
    B, W = c.B, c.weight
    gr = c.graph
    fa = C.soGraphActionModel(B, c)
    fm = C.soGraphMonoModel(B, c)
    sides = {"mono": (fm, gr["mono0"], gr["mono"], gr["sosMono"]),
             "pLo": (fa, gr["pLo0"], gr["pLo"], gr["sosLo"]),
             "pHi": (M.negM(B, fa), -gr["pHi0"], -gr["pHi"], gr["sosHi"])}
    eng = PK.PackedEngine({"cfgFull": F(1, 10 ** 24), "cfgLow": F(1, 10 ** int(bexp))})
    root = c.cfgLow.root()
    new = {}
    for side in ("pLo", "pHi"):
        f, m0, m, sos = sides[side]
        gp = [((int(k[0]), int(k[1])), (int(v[0]), int(v[1]))) for k, v in sos]
        conj = C.conjSorted(B, gp)
        adv = eng.generate(B, W, root, KEYS[side], gp, conj)
        out = eng.mulPacked(B, W, adv, gp, conj)
        print(side, "packed advice", "OK" if out is not None else "FAILS %r" % eng.last_info.get("why"),
              "rem", float(eng.last_info.get("rem", 0)) if out is not None else None, flush=True)
        if out is None:
            raise SystemExit("packed advice for %s fails the landed check" % side)
        new[side] = adv
    # the K semantics: the cfgLow book with the two entries appended (as the Lean data will be)
    cfgK = c.cfgLow
    for side in ("pLo", "pHi"):
        cfgK = cfgK.withExtra(KEYS[side], new[side])
    ok = True
    for side in ("mono", "pLo", "pHi"):
        f, m0, m, sos = sides[side]
        gp = [((int(k[0]), int(k[1])), (int(v[0]), int(v[1]))) for k, v in sos]
        okD, mD = margin(B, W, C.realLowerModel(B, W, c.cfgLow, f, m0, gp), m0, m)
        okK, mK = margin(B, W, realLowerModelK(B, W, cfgK, KEYS[side], f, m0, gp), m0, m)
        print("%-4s direct: %s margin %.6e | K: %s margin %.6e" % (side, okD, float(mD), okK, float(mK)), flush=True)
        ok = ok and okK
    print("strict disp < mono * rhoInf:", c.params["disp"] < gr["mono"] * c.params["rhoInf"], flush=True)
    if not ok:
        raise SystemExit("K graph check FAILS: not adopted")
    os.makedirs(odir, exist_ok=True)
    g["books"]["cfgLow"] = list(g["books"]["cfgLow"]) + [(list(KEYS["pLo"]), new["pLo"]),
                                                        (list(KEYS["pHi"]), new["pHi"])]
    pickle.dump(g, open(os.path.join(odir, "gen.pkl"), "wb"))
    print("K GRAPH CHECK PASSES; written", os.path.join(odir, "gen.pkl"), flush=True)


if __name__ == "__main__":
    main(*sys.argv[1:])
