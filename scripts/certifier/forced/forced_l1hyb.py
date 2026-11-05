#!/usr/bin/env python3
"""V2-CONSOL #6: emit the forced toy's l1-entry and hybrid-restart witnesses as Lean data.  Untrusted tooling.

    python3 -I scripts/certifier/forced/forced_l1hyb.py [TAG] [--rho1 R] [--prune DIGITS] [--no-lean-check]

Runs forced_l1.l1_witness (route A with the l1 entry on the strip rho1) and forced_hybrid.hybrid_witness (the hybrid
restart with the Newton step of a finer Picard torus), re-decides their rational parts with the compiled Lean
(`#eval`, through $FORCED_LEAN_PREFIX), and writes
  KAM/CertificateSharp/V2/Tests/Forced/<TAG>L1HybData.lean   the stage literals `msF` (the composition of the first
                                                             derivatives along K, full stage: `checkInvariance`'s,
                                                             read again by `checkL1E` and `hybCompOk`) and `mvF`
                                                             (the energy composition, `checkEnergy`'s), the witnesses
                                                             `l1Wit` and `hybWit`
  scripts/certifier/fixtures/forced-toy/<TAG>_l1.json, <TAG>_hybrid.json   the witnesses and the mirror's numbers.
The literals are re-proved in the kernel (`eq_of_optModelsBeq`), so a mirror drift fails the build.
"""
import argparse
import json
import os
import pickle
import sys
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
ROOT = os.path.abspath(os.path.join(HERE, "..", "..", ".."))

import forced_l1 as L1               # noqa: E402
import forced_hybrid as HY           # noqa: E402
import forced_emit as FE             # noqa: E402
import forced_stages as FS           # noqa: E402
import forced_witness as FW          # noqa: E402

LEAN_DIR = os.path.join(ROOT, "KAM", "CertificateSharp", "V2", "Tests", "Forced")
JSON_DIR = os.path.join(ROOT, "scripts", "certifier", "fixtures", "forced-toy")


def brk(text, width=FE.WIDTH):
    """break a one-line Lean term at its ', ' separators into lines of at most `width` columns.  A field of a
    structure instance must start at or right of the column of the instance's first field (Lean's `sepByIndent`),
    so a continuation line is indented to the innermost open `{ ` plus 2 (else 4 columns)."""
    parts = text.split(", ")
    lines, cur = [], ""
    for i, p in enumerate(parts):
        s = p + ("," if i < len(parts) - 1 else "")
        if cur and len(cur) + 1 + len(s) > width:
            lines.append(cur)
            cur = " " * indent_for("\n".join(lines)) + s
        else:
            cur = (cur + " " + s) if cur else s
    lines.append(cur)
    for ln in lines:
        assert len(ln) <= width, ln
    return "\n".join(lines)


def indent_for(done):
    """the column of the first field of the innermost structure instance still open after `done` (lines joined)."""
    stack = []
    col = 0
    for ch in done:
        if ch == "\n":
            col = 0
            continue
        if ch in "{⟨[(":
            stack.append((ch, col))
        elif ch in "}⟩])" and stack:
            stack.pop()
        col += 1
    opens = [c for ch, c in stack if ch == "{"]
    return 4 if not opens else opens[-1] + 2


def ldef(name, ty, term, doc):
    body = brk("  " + term)
    return "/-- %s -/\ndef %s : %s :=\n%s\n" % (doc, name, ty, body)


def data_module(tag, c, WL, WH):
    out = [FE.HEADER]
    out.append("public import KAM.CertificateSharp.V2.Tests.Forced.%sWitness\n" % tag)
    out.append("public import KAM.CertificateSharp.V2.RouteAL1Core\n")
    out.append("public import KAM.CertificateSharp.Hybrid.RestartQ\n\n")
    out.append("""/-!
# The forced toy `%(T)s` through the ℓ¹ entry and the hybrid restart (data)

Emitted by `scripts/certifier/forced/forced_l1hyb.py %(T)s` (the producers `forced_l1.py`,
`forced_hybrid.py`; fixtures `scripts/certifier/fixtures/forced-toy/%(T)s_l1.json`,
`%(T)s_hybrid.json`):

* `msF`, `mvF`: the compositions of the first derivatives of `H` and of `H` along `K` at the full
  stage (those of `checkInvariance` and `checkEnergy`), literals of the Python mirror, re-proved
  by their own kernel runs and read by `checkL1E` and `hybCompOk`;
* `l1Wit`: route A with the ℓ¹ entry on the strip `ρ' = %(rho1)s` (`L1.routeAL1`), `X⋆ = %(XL)s`;
* `hybWit`: the hybrid restart (`Hybrid.routeHybrid`) with the Newton step `hybDK` of a finer
  Picard torus (%(nst)d terms), restarted error `%(e1)s` against the base `%(e0)s`, and the
  route-A′ run of `refinedWitR` at the restart numbers (`ρ₁ = ρ`: the base run's sites).
-/

@[expose] public section

namespace KAM.CertificateSharp.V2.Forced.%(T)s

open KAM.Certificate KAM.CertificateSharp KAM.CertificateSharp.V2

""" % dict(T=tag, rho1=WL["rho1"], XL=WL["Xs"], nst=HY.step_terms(WH["dK"]), e1="%.3g" % float(WH["err1"]),
           e0="%.3g" % float(c.params["err"])))
    msF, mv = WH["aux"]["msF"], WH["aux"]["mv"]
    out.append(FS.models_def("msF", msF, "the composed first derivatives along `K` (full stage)") + "\n")
    out.append(FS.models_def("mvF", mv, "the composed energy along `K` (full stage)") + "\n")
    q = L1.FL.lq
    # route A with the l1 entry
    out.append(ldef("l1Claim", "L1.L1Claim", L1.lean_l1_claim(WL["L"]), "The ℓ¹ claim (`checkL1Claim`)."))
    w = WL["core"]
    core = ("{ Xs := %s, kp := %d, th := %s, c := [%s], cbar := [%s], ctail := %s, sB := %s, sT := %s, sLt := %s, "
            "sN := %s, sNt := %s, t := %s, J := %d }") % (
        q(w["Xs"]), w["kp"], q(w["th"]), ", ".join(q(x) for x in w["c"]), ", ".join(q(x) for x in w["cbar"]),
        q(w["ctail"]), q(w["sB"]), q(w["sT"]), q(w["sLt"]), q(w["sN"]), q(w["sNt"]), q(w["t"]), w["J"])
    out.append("\n" + ldef("l1Run", "FrozenWit", core, "The run of the ℓ¹ entry on the strip `ρ'` (tight caps)."))
    sites = "[%s]" % ", ".join("(%s, %s)" % (FW.lean_bite(x), FW.lean_bite(y)) for x, y in WL["sites"])
    out.append("\n" + ldef("l1Sites", "List (Option BiteWit × Option BiteWit)", sites,
                           "The certified small-divisor sites of the bites of the strip `ρ'`."))
    out.append("\n" + ldef("l1Base", "RefinedWit", "{ core := l1Run, R := Rclaim, κ := %s, sites := l1Sites }"
                           % q(WL["kappa"]), "C6's refined run on the strip `ρ'`, with the base claim."))
    out.append("\n" + ldef("l1Entry", "KAM.Sharp2.Examples.EntryQ", L1.lean_entry(WL["E"]),
                           "The entry record."))
    out.append("\n" + ldef("l1Wit", "L1.L1Wit", "{ base := l1Base, L := l1Claim, E := l1Entry, g0 := %s, gρ := %s }"
                           % (L1.lean_fib(WL["g0"]), L1.lean_fib(WL["gr"])),
                           "**The witness of route A with the ℓ¹ entry.**"))
    # the hybrid
    out.append("\n" + ldef("hybDK", "CertEmbedding ℚ", HY.lean_step_emb(WH["dK"]),
                           "The Newton step `ΔK̂` (`K' - K̂`, `K'` the finer Picard torus)."))
    out.append("\n" + ldef("hybClaims", "Hybrid.StepNumQ", HY.lean_stepnum(WH["cl"]),
                           "The step claims `(S1)–(S7)`."))
    st = "{ dK := hybDK, s1 := %s, W1 := %s, Winf := %s, WT := %s, cl := hybClaims, lH := %s, dw := %s }" % (
        q(WH["s1"]), L1.lean_weight(WH["W1"]), L1.lean_weight(WH["Winf"]), L1.lean_weight(WH["WT"]), q(WH["lH"]),
        q(WH["dw"]))
    out.append("\n" + ldef("hybStep", "Hybrid.HybStep", st, "The step data (format v1 `step`)."))
    out.append("\n" + ldef("hybParams1", "CertParams", HY.lean_params(WH["p1"]),
                           "The restart parameters (format v1 `restart.params1`)."))
    out.append("\n" + ldef("hybClaim1", "RefClaim", HY.lean_claim(WH["R1"]),
                           "The transferred refined claim of the restart (format v1 `witness1.base.R`)."))
    base = HY.FW_base_L8(c, tag)
    wR = WH["wR"]
    assert (wR["base"]["core"] == base["core"] and wR["base"]["kappa"] == base["kappa"] and wR["bF"] == base["bF"]
            and wR["bT"] == base["bT"]), "the restart must run the base L8' witness"
    out.append("\n/-- The restarted route-A′ run (format v1 `restart.witness1`): the base run `refinedWitR` with the\n"
               "transferred claim (its sites are the base run's). -/\n"
               "def hybWit1 : RefinedWitR :=\n  { refinedWitR with base := { refinedWitR.base with R := hybClaim1 } }\n")
    out.append("\n/-- **The hybrid witness.** -/\n"
               "def hybWit : Hybrid.HybWit :=\n  { R0 := Rclaim, step := hybStep, p1 := hybParams1, w1 := hybWit1 }\n")
    out.append("\nend KAM.CertificateSharp.V2.Forced.%s\n\nend\n" % tag)
    text = "".join(out)
    for ln in text.split("\n"):
        assert len(ln) <= FE.WIDTH, ln
    return text


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("tag", nargs="?", default="Tiny")
    ap.add_argument("--rho1", default="1/10")
    ap.add_argument("--prune", type=int, default=14)
    ap.add_argument("--no-lean-check", action="store_true")
    a = ap.parse_args()
    c = L1.ensure(a.tag)
    cache = os.path.join(L1.work_dir(), "l1hyb_%s_%s_%d.pkl" % (a.tag, a.rho1.replace("/", "_"), a.prune))
    if os.path.exists(cache):
        with open(cache, "rb") as fh:
            WL, WH = pickle.load(fh)
    else:
        WL = L1.l1_witness(c, a.tag, F(a.rho1))
        WH = HY.hybrid_witness(c, a.tag, a.prune)
        with open(cache, "wb") as fh:
            pickle.dump((WL, WH), fh)
    assert WH["R0"] == WL["R"]
    if not a.no_lean_check:
        r1 = L1.check_in_lean(a.tag, WL)
        r2 = HY.check_in_lean(a.tag, WH)
        print("compiled Lean, l1:", r1)
        print("compiled Lean, hybrid:", r2)
        assert all(r1.values()) and all(r2.values())
    with open(os.path.join(LEAN_DIR, "%sL1HybData.lean" % a.tag), "w") as fh:
        fh.write(data_module(a.tag, c, WL, WH))
    with open(os.path.join(JSON_DIR, "%s_l1.json" % a.tag), "w") as fh:
        json.dump(L1.report(WL), fh, indent=1, sort_keys=True, default=str)
    rep = dict((k, v) for k, v in WH.items() if k not in ("aux", "W1", "Winf", "WT", "h"))
    rep.update(W1=[WH["W1"].rho, WH["W1"].w], Winf=[WH["Winf"].rho, WH["Winf"].w], WT=[WH["WT"].rho, WH["WT"].w],
               transfer={k: v for k, v in WH["h"].items() if not isinstance(v, dict)}, lean=HY.lean_hyb_wit(WH))
    with open(os.path.join(JSON_DIR, "%s_hybrid.json" % a.tag), "w") as fh:
        json.dump(FW.jsonable(rep), fh, indent=1, sort_keys=True, default=str)
    print("wrote %sL1HybData.lean, %s_l1.json, %s_hybrid.json" % (a.tag, a.tag, a.tag))


if __name__ == "__main__":
    main()
