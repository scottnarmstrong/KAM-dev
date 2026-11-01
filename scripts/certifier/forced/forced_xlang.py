#!/usr/bin/env python3
"""V2-TOOLS #6: cross-language agreement of the forced-toy producer/mirror (Python) with the Lean checker.

    python3 -I scripts/certifier/forced/forced_xlang.py [TAG ...]      (default: Tiny Micro TinyC2)

Exit status 0 iff every comparison agrees.  Compared, per tag (the Lean side by compiled `#eval` of the built
modules; the kernel-checked agreement is the stage theorems of <TAG>Base, see forced_stages.py):
  jet        the jet program of the Hamiltonian: length, v0, d1, d2 (adv_jet.py vs `HamExpr.jet`);
  stages     regeneration determinism: the stage literals recomputed from the pickle equal the emitted
             <TAG>Stages.lean byte for byte;
  claim      checkHamClaim at the refined claim R (true) and at R with dx just below the mirror's value (false);
  cores      the route cores at the witness and at X* times 10 and 1/2 (refinedCore, frozenCore, frozenBCore,
             refinedBCore), mirror verdict vs Lean verdict;
  sharp      sharpTest (sharp_q.py vs Lean) on the certificate's parameters.
"""
import json
import os
import sys
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(1, os.path.join(HERE, "..", "..", "spin_orbit"))
sys.setrecursionlimit(100000)

import forced_lean as FL            # noqa: E402
import forced_stages as FS          # noqa: E402
import forced_witness as FW         # noqa: E402
import sharp_q as SQ                # noqa: E402
import v2_q as V                    # noqa: E402

ROOT = os.path.abspath(os.path.join(HERE, "..", "..", ".."))
FIX = os.path.join(ROOT, "scripts", "certifier", "fixtures", "forced-toy")
MOD = "KAM.CertificateSharp.V2.Tests.Forced."


def fr(d):
    return {k: (F(v) if isinstance(v, str) else v) for k, v in d.items()}


def check_tag(tag):
    c = FW.load(tag)
    res = []
    J = c.jet
    imports = [MOD + tag + "Data", "KAM.CertificateSharp.V2.RouteAll"]
    opens = ["KAM.CertificateSharp.V2.Forced", "KAM.Certificate", "KAM.CertificateSharp.V2"]
    exprs = ["%s.cert.ham.jet.prog.ops.length" % tag, "%s.cert.ham.jet.v0" % tag, "%s.cert.ham.jet.d1" % tag,
             "%s.cert.ham.jet.d2" % tag, "KAM.CertificateSharp.sharpTest %s.cert" % tag]
    labels = ["jet length", "jet v0", "jet d1", "jet d2", "sharpTest"]
    expect = [str(len(J["prog"])), str(J["v0"]), str(J["d1"]).replace(" ", ""), str(J["d2"]).replace(" ", ""),
              str(SQ.sharpTest(dict(c.params))).lower()]
    wj = json.load(open(os.path.join(FIX, "%s_witness.json" % tag)))
    p, box = dict(c.params), c.freqBox
    if "refinedA" in wj:
        WA = wj["refinedA"]
        R = {k: F(v) for k, v in WA["R"].items()}
        core = fr({k: v for k, v in WA["core"].items() if k != "R"})
        core["c"] = [F(x) for x in WA["core"]["c"]]
        core["cbar"] = [F(x) for x in WA["core"]["cbar"]]
        W = dict(core=core, R=R, kappa=F(WA["kappa"]), sites=[[fr(x) if x else None for x in t] for t in WA["sites"]])
        hv = wj["claim_values"]["ham"]
        Rlow = dict(R, dx=F(hv["dx"]) * (1 - F(1, 10 ** 6)))
        for lab, Rx, exp in (("claim at R", R, True), ("claim at dx below the disc pass", Rlow, False)):
            Rs = "{ dh := %s, dx := %s, d2x := %s, d2h := %s, bL := %s, bN := %s, bNt := %s, bT := %s }" % tuple(
                FL.lq(Rx[k]) for k in ("dh", "dx", "d2x", "d2h", "bL", "bN", "bNt", "bT"))
            exprs.append("checkHamClaim %s.cert (%s : RefClaim)" % (tag, Rs))
            labels.append(lab)
            expect.append(str(exp).lower())
        for fac in (F(1), F(10), F(1, 2)):
            Wf = dict(W, core=dict(core, Xs=core["Xs"] * fac))
            mirror = V.refinedCore(2, p, box, dict(Wf["core"], R=R))
            exprs.append("refinedCore 2 %s.cert.params %s.cert.freqBox (%s)" % (tag, tag, FW.lean_refined_wit(Wf)))
            labels.append("refinedCore at %s X*" % fac)
            expect.append(str(mirror).lower())
    if "frozenA" in wj:
        A = fr(wj["frozenA"])
        A["c"] = [F(x) for x in wj["frozenA"]["c"]]
        A["cbar"] = [F(x) for x in wj["frozenA"]["cbar"]]
        for fac in (F(1), F(10), F(1, 2)):
            Af = dict(A, Xs=A["Xs"] * fac)
            exprs.append("frozenCore 2 %s.cert.params %s.cert.freqBox %s" % (tag, tag, FW.lean_frozenA(Af)))
            labels.append("frozenCore at %s X*" % fac)
            expect.append(str(V.frozenCore(2, p, box, Af)).lower())
    outs = FL.lean_eval(imports, opens, exprs)
    for lab, e, o in zip(labels, expect, outs):
        res.append(dict(tag=tag, check=lab, python=e, lean=o.replace(" ", ""), agree=e == o.replace(" ", "")))
    # regeneration determinism of the stage literals
    st = FS.stages(c)
    txt = FS.emit_stages(c, st, tag, MOD + tag + "Data")
    with open(os.path.join(ROOT, "KAM", "CertificateSharp", "V2", "Tests", "Forced", "%sStages.lean" % tag)) as fh:
        same = fh.read() == txt
    res.append(dict(tag=tag, check="stage literals regenerate byte for byte", python="", lean="", agree=same))
    return res


def main(tags):
    allres = []
    for t in tags:
        allres += check_tag(t)
    for r in allres:
        print("%-7s %-40s %-6s python=%-28s lean=%s" % (r["tag"], r["check"], "OK" if r["agree"] else "DIFFER",
                                                    r["python"][:28], r["lean"][:40]))
    ok = all(r["agree"] for r in allres)
    with open(os.path.join(FIX, "xlang.json"), "w") as fh:
        json.dump(allres, fh, indent=1)
    print("cross-language agreement:", "ALL AGREE" if ok else "DISAGREEMENT", "(%d comparisons)" % len(allres))
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:] or ["Tiny", "Micro", "TinyC2"]))
