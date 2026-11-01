#!/usr/bin/env python3
"""S6 (RUNBOOK §7): the seal probe and the axiom check for the LP anchors.

usage: lp_axioms.py --root <tree> --manifest <manifest> --probe            > .lake/abi-scratch/LpSealProbe.lean
       lp_lean.sh <tree> .lake/abi-scratch/LpSealProbe.lean | lp_axioms.py --root <tree> --manifest <m> --verify

--probe writes a scratch Lean file importing every LP frozen theorem module (each imports its provider) and, for each
of the LP theorem anchors X with provider Pv: `example : type_of% @X := @Pv`, a meta check that the elaborated types
of X and Pv are `Expr.eqv` (alpha-equivalent), `#print axioms X` and `#print axioms Pv`; and `#print axioms` of every
LP frozen definition. --verify parses the Lean output: every anchor and provider must depend on exactly
[propext, Classical.choice, Quot.sound], every definition on a subset of those, every type check TYPE_EQV, and no
error. Exit 0 = ALL OK.
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

STD = ["propext", "Classical.choice", "Quot.sound"]
META = '''open Lean Meta Elab Command
/-- `#typeEqv a b`: whether the elaborated types of `a` and `b` are alpha-equivalent (`Expr.eqv`). -/
elab "#typeEqv " a:ident b:ident : command => do
  let env ← getEnv
  let some ca := env.find? a.getId | throwError "unknown {a.getId}"
  let some cb := env.find? b.getId | throwError "unknown {b.getId}"
  logInfo m!"TYPECHECK {a.getId} {b.getId}: {if ca.type.eqv cb.type then "TYPE_EQV" else "TYPE_NOT_EQV"}"
'''


def lp_entries(manifest: Path) -> list[dict]:
    m = json.loads(manifest.read_text())
    return [a for a in m["anchors"] if a["id"].startswith("planetary.d59.")]


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", required=True)
    ap.add_argument("--manifest", required=True)
    g = ap.add_mutually_exclusive_group(required=True)
    g.add_argument("--probe", action="store_true")
    g.add_argument("--verify", action="store_true")
    a = ap.parse_args()
    ents = lp_entries(Path(a.manifest))
    thms = [e for e in ents if e["kind"] == "theorem"]
    defs = [e for e in ents if e["kind"] == "definition"]
    if a.probe:
        out = [f"import {e['path'][:-5].replace('/', '.')}" for e in ents] + ["", META]
        for e in thms:
            x, pv = e["export"], e["implementation"]["export"]
            out += [f"example : type_of% @{x} := @{pv}", f"#typeEqv {x} {pv}", f"#print axioms {x}",
                    f"#print axioms {pv}", ""]
        out += [f"#print axioms {e['export']}" for e in defs]
        print("\n".join(out))
        return 0
    text = sys.stdin.read()
    ok = True
    if re.search(r"(?m)^[^\n]*: error", text):
        print("ERROR in the probe output")
        ok = False
    ax = {n: [x.strip() for x in a.replace("\n", " ").split(",") if x.strip()]
          for n, a in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", text)}
    noax = set(re.findall(r"'([^']+)' does not depend on any axioms", text))
    for e in thms:
        for n in (e["export"], e["implementation"]["export"]):
            got = ax.get(n)
            good = got is not None and sorted(got) == sorted(STD)
            ok &= good
            print(f"{'OK ' if good else 'BAD'} axioms {n}: {got}")
        tc = re.search(r"TYPECHECK " + re.escape(e["export"]) + r" " + re.escape(e["implementation"]["export"])
                       + r": (\w+)", text)
        good = bool(tc) and tc.group(1) == "TYPE_EQV"
        ok &= good
        print(f"{'OK ' if good else 'BAD'} type {e['export']} == {e['implementation']['export']}: "
              f"{tc.group(1) if tc else 'missing'}")
    for e in defs:
        n = e["export"]
        got = ax.get(n, [] if n in noax else None)
        good = got is not None and set(got) <= set(STD) and "sorryAx" not in got
        ok &= good
        print(f"{'OK ' if good else 'BAD'} axioms {n}: {got}")
    print(f"{len(thms)} anchors, {len(thms)} providers, {len(defs)} definitions")
    print("ALL OK" if ok else "FAILED")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
