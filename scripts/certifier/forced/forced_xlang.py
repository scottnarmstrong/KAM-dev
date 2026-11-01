#!/usr/bin/env python3
"""V2-TOOLS #6: cross-language agreement of the forced-toy producer/mirror (Python) with the Lean checker.

    python3 -I scripts/certifier/forced/forced_xlang.py [TAG ...] [--write-fixture]   (default: Tiny Micro TinyC2)

Exit status 0 iff every comparison agrees.  The Lean side is the compiled `#eval` of the built default modules; the
kernel-checked agreement is separate (every stage literal of <TAG>Stages is re-proved by `eq_of_matBeq`).  Compared,
per tag:
  jet      the whole jet program of the Hamiltonian, operation by operation (constants, degrees, keys, operands),
           and the slot tables v0, d1, d2, d3 (adv_jet.py against `HamExpr.jet`);
  sharp    sharpTest (sharp_q.py against Lean);
  claim    two-sided, per Hamiltonian sum (dh, dx, d2x, d2h) of the disc pass: the claim set exactly to the mirror's
           exact value must pass, and 10^-12 (relative) below it must fail; so a mirror that is optimistic or
           pessimistic by more than 10^-12 is caught (tags with a refined claim);
  cores    two-sided at the X* boundary of each witness, the other numbers fixed: the boundary is located in the
           mirror by exact bisection to a relative width 10^-5 (lo passes, hi fails there), and Lean must agree at lo
           and at hi, for refinedCore (route A refined, the sites of the witness), frozenCore (route A frozen),
           refinedBCore and frozenBCore (route B; the mirror is route_b_lean_mirror's routeBOk, the well-formedness
           tests and the c1 clause of finalB; the displacement clauses are not mirrored, and are far from binding at
           disp = 10^-3);
  stages   the stage literals recomputed from the pickle equal the emitted <TAG>Stages.lean byte for byte.
With --write-fixture the comparisons are written to scripts/certifier/fixtures/forced-toy/xlang.json.
"""
import json
import os
import sys
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(1, os.path.join(HERE, "..", "..", "spin_orbit"))
sys.path.insert(2, os.path.join(HERE, "..", "..", "apost_sharp"))
sys.setrecursionlimit(100000)

import forced_lean as FL            # noqa: E402
import forced_stages as FS          # noqa: E402
import forced_witness as FW         # noqa: E402
import route_b_lean_mirror as RB    # noqa: E402
import sharp_q as SQ                # noqa: E402
import v2_q as V                    # noqa: E402

ROOT = os.path.abspath(os.path.join(HERE, "..", "..", ".."))
FIX = os.path.join(ROOT, "scripts", "certifier", "fixtures", "forced-toy")
MOD = "KAM.CertificateSharp.V2.Tests.Forced."

PRELUDE = r"""
open KAM.Certificate in
def opStr : SlpOp → String
  | .const re im d => s!"const {re} {im} {d}"
  | .action j => s!"action {j}"
  | .char k => s!"char {k}"
  | .add a b => s!"add {a} {b}"
  | .mul a b => s!"mul {a} {b}"
  | .exp a => s!"exp {a}"
  | .inv a => s!"inv {a}"
  | .sqrt a => s!"sqrt {a}"
open KAM.Certificate in
def jetStr (e : HamExpr 2) : String := String.intercalate ";" (e.jet.prog.ops.map opStr)
"""


def fr(d):
    return {k: (F(v) if isinstance(v, str) else v) for k, v in d.items()}


def py_op(op):
    t = op[0]
    if t == "const":
        return "const %s %s %d" % (F(op[1]), F(op[2]), op[3])
    if t == "char":
        return "char [%s]" % ", ".join(str(x) for x in op[1])
    return " ".join([t] + [str(x) for x in op[1:]])


def bisect(ok, lo, hi, rel=F(1, 10 ** 5), steps=200):
    """lo passes, hi fails (exact rationals); shrink to hi/lo - 1 <= rel.  None if the mirror's bracket is not
    [pass, fail] (then only the comparison at the witness itself is made)."""
    if not (ok(lo) and not ok(hi)):
        return None
    for _ in range(steps):
        if hi / lo - 1 <= rel:
            break
        mid = (lo + hi) / 2
        mid = F(mid).limit_denominator(10 ** 30)
        if ok(mid):
            lo = mid
        else:
            hi = mid
    return lo, hi


def boundary_probes(name, ok, X0):
    """(label, X, mirror verdict): at the witness's own X*, and on both sides of the mirror's boundary."""
    out = [("%s at the witness's X*" % name, X0, bool(ok(X0)))]
    b = bisect(ok, X0, X0 * 10)
    if b is not None:
        out += [("%s at the boundary's passing side" % name, b[0], True),
                ("%s at the boundary's failing side" % name, b[1], False)]
    return out


def mirror_B(c, W, frozen, Xs):
    p, box = dict(c.params), c.freqBox
    R = {k: F(v) for k, v in W["R"].items()} if W.get("R") else None
    caps = {k: F(v) for k, v in W["caps"].items()}
    cl, cpl, cbl, ctail, cbtail = W["consts"]
    consts = ([F(x) for x in cl], [F(x) for x in cpl], [F(x) for x in cbl], F(ctail), F(cbtail))
    N = FW.numB(p, box, R, consts, caps, int(W["kp"]), frozen)
    I = FW.default_IB(p) if frozen else dict(iLt=R["bL"], iN=R["bN"], iNt=R["bNt"])
    m0 = RB.initB(I, p["sK"], p["sB"], p["mu"])
    σ = RB.capB(N, p["sT"], p["mu"], p["nu"])
    try:
        fails = RB.routeBOk(N, σ, m0, p["mu"] / 2, Xs) + RB.wf_fails(N, I, p["sT"], p["mu"])
        c1ok = RB.c1B(N, I, Xs) * p["err"] < p["gamma"] ** 4 * p["rho"] ** 4
    except ZeroDivisionError:
        return False
    extra = (p["sB"] - p["mu"] < caps["sB"]) if frozen else True
    return not fails and c1ok and extra


def b_term(W, frozen, Xs):
    Wx = dict(W, Xs=Xs, caps={k: F(v) for k, v in W["caps"].items()},
              consts=[[F(x) for x in W["consts"][0]], [F(x) for x in W["consts"][1]],
                      [F(x) for x in W["consts"][2]], F(W["consts"][3]), F(W["consts"][4])],
              kp=int(W["kp"]), J=int(W["J"]))
    if frozen:
        return "(%s : KAM.CertificateSharp.V2.RunBWit)" % FW.lean_runB(Wx)
    Wx["R"] = {k: F(v) for k, v in W["R"].items()}
    Wx["kappa"] = F(W["kappa"])
    Wx["sites"] = [tuple(fr(x) if x else None for x in t) for t in W["sites"]]
    return FW.lean_refinedB(Wx)


def check_tag(tag):
    c = FW.load(tag)
    p, box = dict(c.params), c.freqBox
    J = c.jet
    labels, expect, exprs = [], [], []

    def add(label, py, lean):
        labels.append(label)
        expect.append(py)
        exprs.append(lean)

    add("jet operations (%d)" % len(J["prog"]), ";".join(py_op(op) for op in J["prog"]), "jetStr %s.cert.ham" % tag)
    add("jet v0", str(J["v0"]), "%s.cert.ham.jet.v0" % tag)
    add("jet d1", str(J["d1"]).replace(" ", ""), "%s.cert.ham.jet.d1" % tag)
    add("jet d2", str(J["d2"]).replace(" ", ""), "%s.cert.ham.jet.d2" % tag)
    add("jet d3", str(J["d3"]).replace(" ", ""), "%s.cert.ham.jet.d3" % tag)
    add("sharpTest", str(SQ.sharpTest(dict(p))).lower(), "KAM.CertificateSharp.sharpTest %s.cert" % tag)
    wj = json.load(open(os.path.join(FIX, "%s_witness.json" % tag)))
    if "refinedA" in wj:
        WA = wj["refinedA"]
        R = {k: F(v) for k, v in WA["R"].items()}
        hv = {k: F(v) for k, v in wj["claim_values"]["ham"].items()}
        for key in ("dh", "dx", "d2x", "d2h"):
            for lab, val, exp in (("at the mirror value", hv[key], True),
                                  ("10^-12 below it", hv[key] * (1 - F(1, 10 ** 12)), False)):
                Rx = dict(R, **{key: val})
                Rs = "{ %s }" % ", ".join("%s := %s" % (k, FL.lq(Rx[k])) for k in
                                         ("dh", "dx", "d2x", "d2h", "bL", "bN", "bNt", "bT"))
                add("claim %s %s" % (key, lab), str(exp).lower(), "checkHamClaim %s.cert (%s : RefClaim)" % (tag, Rs))
        core = fr({k: v for k, v in WA["core"].items() if k != "R"})
        core["c"] = [F(x) for x in WA["core"]["c"]]
        core["cbar"] = [F(x) for x in WA["core"]["cbar"]]
        W = dict(core=core, R=R, kappa=F(WA["kappa"]), sites=[[fr(x) if x else None for x in t] for t in WA["sites"]])
        ok = lambda X: V.refinedCore(2, p, box, dict(core, Xs=X, R=R))
        for lab, X, exp in boundary_probes("refinedCore", ok, core["Xs"]):
            add("%s (X = %.6g)" % (lab, float(X)), str(exp).lower(), "refinedCore 2 %s.cert.params %s.cert.freqBox (%s)" %
                (tag, tag, FW.lean_refined_wit(dict(W, core=dict(core, Xs=X)))))
    if "frozenA" in wj:
        A = fr(wj["frozenA"])
        A["c"] = [F(x) for x in wj["frozenA"]["c"]]
        A["cbar"] = [F(x) for x in wj["frozenA"]["cbar"]]
        ok = lambda X: V.frozenCore(2, p, box, dict(A, Xs=X))
        for lab, X, exp in boundary_probes("frozenCore", ok, A["Xs"]):
            add("%s (X = %.6g)" % (lab, float(X)), str(exp).lower(), "frozenCore 2 %s.cert.params %s.cert.freqBox %s" %
                (tag, tag, FW.lean_frozenA(dict(A, Xs=X))))
    for key, frozen, core_fn in (("refinedB", False, "refinedBCore"), ("frozenB", True, "frozenBCore")):
        if key not in wj:
            continue
        WB = wj[key]
        X0 = F(WB["Xs"])
        ok = lambda X: mirror_B(c, WB, frozen, X)
        for lab, X, exp in boundary_probes(core_fn, ok, X0):
            add("%s (X = %.6g)" % (lab, float(X)), str(exp).lower(),
                "%s 2 %s.cert.params %s.cert.freqBox %s" % (core_fn, tag, tag, b_term(WB, frozen, X)))
    outs = FL.lean_eval([MOD + tag + "Data", "KAM.CertificateSharp.V2.RouteAll"],
                        ["KAM.CertificateSharp.V2.Forced", "KAM.Certificate", "KAM.CertificateSharp.V2"], exprs,
                        prelude=PRELUDE)
    res = []
    for lab, e, o in zip(labels, expect, outs):
        lean = o if lab.startswith("jet operations") else o.replace(" ", "")
        res.append(dict(tag=tag, check=lab, python=e, lean=lean, agree=e == lean))
    st = FS.stages(c)
    txt = FS.emit_stages(c, st, tag, MOD + tag + "Data")
    with open(os.path.join(ROOT, "KAM", "CertificateSharp", "V2", "Tests", "Forced", "%sStages.lean" % tag)) as fh:
        same = fh.read() == txt
    res.append(dict(tag=tag, check="stage literals regenerate byte for byte", python="", lean="", agree=same))
    return res


def main(argv):
    write = "--write-fixture" in argv
    tags = [a for a in argv if not a.startswith("--")] or ["Tiny", "Micro", "TinyC2"]
    allres = []
    for t in tags:
        allres += check_tag(t)
    for r in allres:
        shown = (lambda x: x[:28] + ("…" if len(x) > 28 else ""))
        print("%-7s %-62s %-6s python=%-30s lean=%s" % (r["tag"], r["check"][:62], "OK" if r["agree"] else "DIFFER",
                                                     shown(r["python"]), shown(r["lean"])))
    ok = all(r["agree"] for r in allres)
    if write:
        with open(os.path.join(FIX, "xlang.json"), "w") as fh:
            json.dump(allres, fh, indent=1)
    print("cross-language agreement:", "ALL AGREE" if ok else "DISAGREEMENT", "(%d comparisons)" % len(allres))
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
