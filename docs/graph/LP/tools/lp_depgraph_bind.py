#!/usr/bin/env python3
"""Bind the frozen LP anchors to graph node IDs, slices and waves (track LP, SPEC §1).

usage: python3 -I docs/graph/LP/tools/lp_depgraph_bind.py [--root .] [--out docs/graph/LP/packets/anchor-binding.tsv]

Reads only identity fields of `manifest/frozen-anchors.json` (id, kind, path, export, contract, abi_sha256,
source.range) and the `public import KAM.Frozen.*` lines of the LP frozen files (to find the reused frozen
definitions that LP files import directly). It never reads a proof body and never interprets manifest state.

Binding rules (SPEC §1, settled 2026-11-01 by package LP-GRAPH-W1):
- every anchor node ID is `<owning MAIN node>#<Lean short name>` (definitions, characterizations and the five
  headline theorems alike);
- the 128 D62 entries (`planetary.d59.*`) plus the reused frozen definitions that an LP frozen file imports directly
  (rule Q6: bound as LP's own anchor nodes, never imported);
- planar/dimension-free definitions and the reused ones go to slice LP-adef-pl, spatial ones to LP-adef-sp, theorem
  anchors to LP-athm; the wave is the wave whose closure first needs the anchor.
"""
import argparse
import json
import re
from pathlib import Path

GROUP = {
    "lpM:s1:data": "planeSq planeLength planeDot spaceDot spaceSq spaceLength",
    "lpM:s1:model": "Phase bodyVector NoCollision actualMasses IsMovingSolutionOn MovingUniqueOn spatialHamiltonian "
                    "SpatialNoCollision IsSpatialMovingSolutionOn SpatialMovingUniqueOn spatialMasses bodyVector3 "
                    "IsHamiltonianSolutionOn",
    "lpM:s1:chamber": "chamber OrderedActions",
    "lpM:s1:thresholds": "actionAxis eccDeficit pairFeasible pairObjective pairThreshold AdjIdx AdjIdx.upperIdx "
                         "orderedPairThreshold orderedCrossThreshold orderedStrongThreshold",
    "lpM:s1:elements": "strongAMD keplerPeri keplerApo SourceCanonicalPhase sourceStrongAMD sourceKeplerPeri "
                       "sourceKeplerApo keplerEnergy keplerAxis keplerAction keplerEccVector planeCross totalMomentum "
                       "spaceCross planetAngularMomentum3 angularMomentum3 spatialKeplerEnergy spatialKeplerAxis "
                       "spatialKeplerAction spatialKeplerEccVector SpatialNegativeEnergy SpatialElliptic "
                       "spatialKeplerPeri spatialKeplerApo SpatialSourceCanonicalPhase spatialSourceKeplerAxis "
                       "spatialSourceKeplerAction spatialSourceKeplerEccVector spatialSourceKeplerEcc "
                       "spatialSourcePlanetAngularMomentum spatialSourceAngularMomentum spatialSourceStrongAMD "
                       "spatialSourceKeplerPeri spatialSourceKeplerApo",
    "lpM:s1:dioph": "IsDiophantine",
    "lpM:L1": "barycentricPositions barycentricVelocities IsNewtonSolutionOn spatialBarycentricPositions "
              "spatialBarycentricVelocities IsSpatialNewtonSolutionOn spatialSourceBarycentricPositions "
              "spatialSourceBarycentricVelocities",
    "lpM:L16:defs": "oscVelocity oscParam oscEnergy oscAxis oscEccVector oscEcc oscPeri oscApo SourceOsculatingPhase "
                    "sourceOscVelocity sourceOscParam sourceOscEnergy sourceOscAxis sourceOscEccVector sourceOscEcc "
                    "sourceOscPeri sourceOscApo spatialOscVelocity spatialOscParam spatialOscEnergy spatialOscAxis "
                    "spatialOscEccVector spatialOscEcc spatialOscPeri spatialOscApo SpatialOscPhase "
                    "SpatialSourceOsculatingPhase spatialSourceOscVelocity spatialSourceOscParam "
                    "spatialSourceOscEnergy spatialSourceOscAxis spatialSourceOscEccVector spatialSourceOscEcc "
                    "spatialSourceOscPeri spatialSourceOscApo",
}
OWNER = {name: g for g, names in GROUP.items() for name in names.split()}
HEADLINE = {
    "planar_strongAMD_barrier": ("lpM:L5", 1, "LP0"),
    "planar_strongAMD_exponentialSafety": ("lpM:T15", 2, "LP1"),
    "planar_strongAMD_exponentialSafety_halfInteger": ("lpM:T15", 2, "LP1-H"),
    "spatial_strongAMD_exponentialSafety": ("lpM:T19", 3, "LP2"),
    "spatial_strongAMD_exponentialSafety_halfInteger": ("lpM:T19", 3, "LP2-H"),
}
# wave-2 reused definitions (statements of LP1/LP1-H/LP2/LP2-H); every other reused one is wave 1 or wave 3
REUSED_W2 = {"IsDiophantine", "actualMasses", "barycentricPositions", "barycentricVelocities", "IsMovingSolutionOn",
             "IsNewtonSolutionOn", "MovingUniqueOn"}


def short(export):
    for ns in ("KAM.Planetary.StrongAMD.", "KAM.Planetary.Spatial.", "KAM.Planetary.", "KAM.Iso.", "KAM."):
        if export.startswith(ns):
            return export[len(ns):]
    return export


def theorem_owner(s):
    if s in HEADLINE:
        return HEADLINE[s][0]
    if "Threshold" in s:
        return "lpM:L4"
    if "StrongAMD" in s or "eccDeficit" in s:
        return "lpM:L3"
    if "Osc" in s:
        return "lpM:L16"
    return "lpM:L2"


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--root", default=".")
    ap.add_argument("--out", default="docs/graph/LP/packets/anchor-binding.tsv")
    a = ap.parse_args()
    root = Path(a.root)
    m = json.loads((root / "manifest/frozen-anchors.json").read_text())
    by_path = {e["path"]: e for e in m["anchors"]}
    lp = [e for e in m["anchors"] if e["id"].startswith("planetary.d59.")]
    reused = {}
    for e in lp:
        for mod in re.findall(r"^public import (KAM\.Frozen\.\S+)", (root / e["path"]).read_text(), re.M):
            r = by_path.get(mod.replace(".", "/") + ".lean")
            if r and not r["id"].startswith("planetary.d59."):
                reused[r["id"]] = r
    rows = []
    for e, is_reused in [(e, False) for e in lp] + [(r, True) for r in sorted(reused.values(), key=lambda x: x["id"])]:
        s = short(e["export"])
        spatial = bool(re.search(r"spatial|Spatial|space|3$|IsHamiltonianSolutionOn", s))
        if e["kind"] == "theorem":
            owner, sl = theorem_owner(s), "LP-athm"
            wave = HEADLINE[s][1] if s in HEADLINE else 3 if spatial else 2 if "Osc" in s else 1
            role = HEADLINE[s][2] if s in HEADLINE else "characterization"
        else:
            owner = OWNER[s]
            sl = "LP-adef-sp" if spatial else "LP-adef-pl"
            wave = 3 if spatial else 2 if s in REUSED_W2 else 1
            role = "reused definition (Q6)" if is_reused else "definition"
        rng = e.get("source", {}).get("range", "-") if not is_reused else "reused: " + e["id"]
        rows.append([e["id"], e["kind"], e["export"], f"{owner}#{s}", sl, str(wave), role, e["contract"]["id"],
                     str(e["contract"]["version"]), e["path"], e["abi_sha256"], rng])
    hdr = ["manifest_id", "kind", "export", "node", "slice", "wave", "role", "contract_id", "contract_version", "path",
           "abi_sha256", "source_range"]
    out = root / a.out
    out.write_text("\t".join(hdr) + "\n" + "".join("\t".join(r) + "\n" for r in rows))
    from collections import Counter
    c = Counter((r[4], r[5]) for r in rows)
    print(f"wrote {out}: {len(rows)} anchors ({len(lp)} D62 entries, {len(reused)} reused definitions)")
    for k in sorted(c):
        print(f"  slice {k[0]} wave {k[1]}: {c[k]}")


if __name__ == "__main__":
    main()
