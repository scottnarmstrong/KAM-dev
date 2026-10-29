#!/usr/bin/env python3
"""Cross-check the Python ball mirror and the extracted jets against the LANDED Lean code.

Untrusted tooling (SO-TOYGEN).  For every toy certificate in OUTDIR, evaluates the landed `Slp.balls` of the
landed `HamExpr.jet` on the certificate's domain D (via toy_lean_extract.py, `lake env lean` in BUILD_DIR) and
compares it slot by slot, exactly, with toy_arith.slp_balls; also re-extracts the jet programs and compares
them with JETS.json.

    python3 toy_crosscheck.py BUILD_DIR JETS.json OUTDIR
"""
import json, sys
from fractions import Fraction as F
import toy_arith as A
import toy_lean_extract as X


def q(x):
    x = F(x)
    return "(%d : ℚ)" % x.numerator if x.denominator == 1 else "((%d : ℚ) / %d)" % (x.numerator, x.denominator)


def landed_predicates(build_dir, certs):
    """The landed parts of checkStatic and the whole of checkSmallness, evaluated by Lean on the data."""
    ex = []
    for toy, c in certs:
        p, n = c["params"], c["n"]
        for wname in ("weight", "weightH"):
            ex.append(("%s %s" % (toy, wname), "checkWeight ⟨%s, %s⟩ %d %d" % (
                q(c[wname]["rho"]), q(c[wname]["w"]), c["expHalvings"], c["expOrder"])))
        pe = c["piEnc"]
        ex.append(("%s checkPiEnclosure" % toy, "checkPiEnclosure (⟨%s, %s, %d, %d⟩ : PiEnclosure ℚ)" % (
            q(pe["centre"]), q(pe["rad"]), pe["machinK"], pe["machinJ"])))
        if "freqProvider" in c:
            m, d, lo, hi = c["freqProvider"]["checkRootEnclosure"]
            ex.append(("%s checkRootEnclosure" % toy, "checkRootEnclosure %d %d %s %s" % (m, d, q(lo), q(hi))))
            co = "[" + ", ".join("[" + ", ".join(q(x) for x in row) + "]"
                                 for row in c["freqProvider"]["checkAlgBox_coeffs"]) + "]"
            box = "[" + ", ".join("(%s, %s)" % (q(a), q(b)) for a, b in c["freqBox"]) + "]"
            ex.append(("%s checkAlgBox" % toy, "checkAlgBox %d %s %s %s %s" % (n, co, q(lo), q(hi), box)))
        args = "%d %d %s %s %s %s %s %s" % (n, p["tau"], q(p["rho"]), q(p["rhoInf"]), q(p["M"]), q(p["sK"]),
                                            q(p["sB"]), q(p["sT"]))
        ex.append(("%s smallness C1" % toy, "decide (isoC1Q %s %s %s %s * %s < %s ^ 4 * %s ^ (4 * %d))" % (
            args, q(p["mu"]), q(p["nuRay"]), q(p["gbar"]), q(p["err"]), q(p["gamma"]), q(p["rho"]), p["tau"])))
        ex.append(("%s smallness C2" % toy, "decide (isoC2Q %s * %s <= %s * %s ^ 2 * %s ^ (2 * %d))" % (
            args, q(p["err"]), q(p["disp"]), q(p["gamma"]), q(p["rho"]), p["tau"])))
    return X.run_bools(build_dir, ex)


def main():
    build_dir, jets_path, outdir = sys.argv[1:4]
    J = json.load(open(jets_path))
    reqs, certs = [], []
    for toy in ("T2", "T2d", "T3", "TR"):
        c = json.load(open("%s/%s.json" % (outdir, toy)))["certificate"]
        reqs.append(dict(toy="T2" if toy == "TR" else toy, rhoH=c["weightH"]["rho"], wH=c["weightH"]["w"],
                         centre=c["centre"], radius=c["radius"], taylorN=c["cfgFull"]["taylorN"]))
        certs.append((toy, c))
    jets, balls = X.run(build_dir, reqs)
    res = {"jets_identical": {k: jets[k] == J["jets"][k] for k in J["jets"]}}
    for (toy, c), req, b in zip(certs, reqs, balls):
        jet = J["jets"][req["toy"]]
        py = A.slp_balls(c["n"], A.parse_ops(jet["ops"]), F(req["wH"]), [F(x) for x in req["centre"]],
                         [F(x) for x in req["radius"]], int(req["taylorN"]))
        ln = b["balls"]
        same = ln is not None and py is not None and len(ln) == len(py) and all(
            (F(l[0]), F(l[1]), F(l[2])) == (p[0][0], p[0][1], p[1]) for l, p in zip(ln, py))
        res[toy] = dict(slots=len(py) if py else None, lean_slots=len(ln) if ln else None, identical=same)
    res["landed_predicates"] = landed_predicates(build_dir, certs)
    with open("%s/lean_crosscheck.json" % outdir, "w") as fh:
        json.dump(res, fh, indent=1, sort_keys=True)
        fh.write("\n")
    print(json.dumps(res))
    bad = [r for r in res["landed_predicates"] if r["value"] is not True]
    if bad or not all(res["jets_identical"].values()) or not all(
            res[t]["identical"] for t in ("T2", "T2d", "T3", "TR")):
        raise SystemExit(1)


if __name__ == "__main__":
    main()
