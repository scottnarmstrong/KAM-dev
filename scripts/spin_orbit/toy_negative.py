#!/usr/bin/env python3
"""Negative tests on the toy data (design §8 'Negative tests', the cases that apply to ℚ toys).

Untrusted tooling (SO-TOYGEN).  Each mutation of a passing toy must fail its intended sub-check in the Python
mirror; the landed predicates among them (checkWeight, checkPiEnclosure, the smallness inequality) are also
evaluated by Lean (optional BUILD_DIR).

    python3 toy_negative.py JETS.json OUTDIR [BUILD_DIR]
"""
import copy, json, sys
from fractions import Fraction as F
import toy_arith as A
import toy_check as K
import toy_gen as G
import toy_model as Mo


def fresh(base):
    c = {k: v for k, v in base.items() if not k.startswith("_") or k in ("_jet",)}
    return copy.deepcopy(c)


def mutations(bases):
    T2, T2d = bases["T2"], bases["T2d"]
    out = []

    def add(label, design_item, base, fn, intended):
        c = fresh(base)
        fn(c)
        out.append((label, design_item, c, intended))

    K.prepare(fresh_T2 := fresh(T2))
    inv_bound = K.check_invariance(fresh_T2)[1]["bound"]
    add("false residual bound (err = bound/2)", "§8.1", T2,
        lambda c: c["params"].__setitem__("err", inv_bound / 2), "checkInvariance")
    add("Gram witness B = 0", "§8.2", T2,
        lambda c: c.__setitem__("gramInv", [[Mo.p_zero(), Mo.p_zero()], [Mo.p_zero(), Mo.p_zero()]]), "checkGram")
    add("torsion witness S = 0", "§8.2", T2,
        lambda c: c.__setitem__("torsInv", [[(F(0), F(0))] * 3 for _ in range(3)]), "checkTorsion")
    add("mu = 0", "§8.3", T2, lambda c: c["params"].__setitem__("mu", F(0)), "checkStatic")
    add("character witness with wrong mean (E = 2)", "§8.4", T2d,
        lambda c: c["wit"].__setitem__("charWit", [((0, 0), (Mo.p_const((2, 0), 2), 0, 400))]), "checkInvariance")
    add("strip weight w < e^{2 pi rho} (w = 1)", "§8.5", T2,
        lambda c: c.__setitem__("weight", (c["weight"][0], F(1))), "checkStatic")
    add("denominator ball contains 0 on D (rhoH = 1/5, w_H >= 3)", "§8.6", T2d,
        lambda c: c.__setitem__("weightH", (F(1, 5), G.weight_for(F(1, 5), c["expHalvings"], c["expOrder"]))),
        "checkHamBounds")
    add("reciprocal witness with delta >= 1 (Q = 0)", "§8.6", T2d,
        lambda c: c["wit"].__setitem__("invWit", [Mo.p_zero()]), "checkInvariance")
    add("box does not exclude 0", "§8.7", T2,
        lambda c: c.__setitem__("freqBox", [(F(0), F(1)), (F(0), F(1))]), "checkStatic")
    add("ray margin violated (nu = 6/10 > (s-1) |omega|_lo = 1/2)", "§8.7", T2,
        lambda c: c["params"].__setitem__("nuRay", F(6, 10)), "checkStatic")

    def narrow(c):
        ce, rad, k, j = c["piEnc"]
        c["piEnc"] = (ce, rad / 4, k, j)
    add("pi enclosure narrower than the Machin bounds", "§8.8", T2, narrow, "checkStatic")

    def pad(c):
        S = [list(r) + [(F(0), F(0))] for r in c["torsInv"]] + [[(F(0), F(0))] * 3 + [(F(1), F(0))]]
        c["torsInv"] = S
    add("torsion witness of shape 4 x 4 at n = 2 (F7 analogue)", "§8.9", T2, pad, "checkTorsion")
    add("smallness: err = 10^6 threshold", "control", T2,
        lambda c: c["params"].__setitem__("err", G.threshold(c) * 10 ** 6), "checkSmallness")
    add("M below the ball bounds (M = 1)", "control", T2, lambda c: c["params"].__setitem__("M", F(1)),
        "checkHamBounds")
    add("sigma_K - mu < |DK| (sK = 1 + mu/2)", "control", T2,
        lambda c: c["params"].__setitem__("sK", 1 + c["params"]["mu"] / 2), "checkEmbedding")
    add("embedding leaves D (action centre shifted by the radius)", "control", T2,
        lambda c: c.__setitem__("centre", [c["centre"][0] + c["radius"][0], c["centre"][1]]), "checkEmbedding")
    return out


def lean_controls(build_dir, bases):
    import toy_lean_extract as X
    from toy_crosscheck import q
    T2 = bases["T2"]
    p = T2["params"]
    ce, rad, k, j = T2["piEnc"]
    args = "%d %d %s %s %s %s %s %s" % (2, p["tau"], q(p["rho"]), q(p["rhoInf"]), q(p["M"]), q(p["sK"]),
                                        q(p["sB"]), q(p["sT"]))
    big = G.threshold(T2) * 10 ** 6
    ex = [("checkWeight w = 1", "checkWeight ⟨%s, 1⟩ %d %d" % (q(T2["weight"][0]), T2["expHalvings"],
                                                               T2["expOrder"])),
          ("checkPiEnclosure narrowed", "checkPiEnclosure (⟨%s, %s, %d, %d⟩ : PiEnclosure ℚ)" % (
              q(ce), q(rad / 4), k, j)),
          ("smallness C1 at 10^6 threshold", "decide (isoC1Q %s %s %s %s * %s < %s ^ 4 * %s ^ (4 * %d))" % (
              args, q(p["mu"]), q(p["nuRay"]), q(p["gbar"]), q(big), q(p["gamma"]), q(p["rho"]), p["tau"]))]
    return X.run_bools(build_dir, ex)


def main():
    jets = json.load(open(sys.argv[1]))["jets"]
    outdir = sys.argv[2]
    bases = {"T2": G.build("T2", jets), "T2d": G.build("T2d", jets)}
    res = []
    for label, item, c, intended in mutations(bases):
        ok, rep = K.check(c)
        failed = [s for s in K.SUBS if not rep[s][0]]
        res.append(dict(test=label, design=item, toy=c["toy"], intended=intended, failed=failed,
                        passes_checker=ok, as_intended=(not ok) and intended in failed))
        print("%-62s %-16s failed: %s" % (label[:62], intended, ",".join(failed)), flush=True)
    doc = dict(tests=res, all_as_intended=all(r["as_intended"] for r in res))
    if len(sys.argv) > 3:
        lc = lean_controls(sys.argv[3], bases)
        doc["lean_controls"] = lc
        doc["lean_controls_all_false"] = all(r["value"] is False for r in lc)
    with open("%s/negative.json" % outdir, "w") as fh:
        json.dump(doc, fh, indent=1, sort_keys=True)
        fh.write("\n")
    print("all as intended:", doc["all_as_intended"], " lean controls false:", doc.get("lean_controls_all_false"))
    if not doc["all_as_intended"] or doc.get("lean_controls_all_false") is False:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
