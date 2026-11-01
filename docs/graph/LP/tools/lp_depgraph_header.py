#!/usr/bin/env python3
"""Write docs/graph/LP/header.txt for the waves assembled so far (K/W header pattern).

usage: python3 -I docs/graph/LP/tools/lp_depgraph_header.py --wave N [--root .]

ROOTS are the theorem anchors of waves <= N (the five headline anchors and the 34 characterizations are roots, rule
Q2); FROZEN_ANCHORS are all anchors of waves <= N, from packets/anchor-binding.tsv. GLOBAL_REVIEWER and
GLOBAL_REVIEW_REF stay '-' until the global review (sol-global-LP) passes.
"""
import argparse
import csv
from pathlib import Path

ap = argparse.ArgumentParser()
ap.add_argument("--wave", type=int, required=True)
ap.add_argument("--root", default=".")
a = ap.parse_args()
g = Path(a.root) / "docs/graph/LP"
rows = [r for r in csv.DictReader(open(g / "packets/anchor-binding.tsv"), delimiter="\t") if int(r["wave"]) <= a.wave]
# frozen definitions outside every root closure (no frozen root statement and no source proof uses them; their
# coverage items are EXCLUDED, SPEC §7): not graph nodes, so not in FROZEN_ANCHORS
UNCONSUMED = {"lpM:L16:defs#sourceOscVelocity", "lpM:L16:defs#sourceOscParam", "lpM:L16:defs#spatialSourceOscVelocity"}
rows = [r for r in rows if r["node"] not in UNCONSUMED]
roots = [r["node"] for r in rows if r["kind"] == "theorem"]
anchors = [r["node"] for r in rows]
H = {
    "GRAPH_VERSION": "4",
    "ROOTS": ", ".join(roots),
    "CORPUS": "docs/tracks/LP/source/{MAIN,AMENDMENTS}.md pinned by SHA-256 in docs/graph/LP/CORPUS.sha256 (MAIN "
              "68e9167f...48c1b, 679 lines; AMENDMENTS c887d1e2...51881, 26 lines; N1 fixed in place, N2-N12 override "
              "the MAIN lines they cite)" + ("; wave 4: docs/tracks/LP/lp3/LP3-PLAN.md (1b58b704...ba06ba, 506 lines), the "
              "LP3 source under D65 (no separate LP3 source note)" if a.wave >= 4 else "") + "; branch inp-lp-graph off inp after the D62 freeze (main f46b94fb); waves 1-"
              + str(a.wave) + "; streamlined review (D65): one global review, no per-slice reviews; LEAN_STATUS set "
              "mechanically from LEAN_REFs that resolve on main; global review maud-lp-gglob-1 PASS WITH NOTES "
              "(docs/graph/LP/reviews/GLOBAL-review-1.md; D27 BYPASS confirmed); TOPOLOGY_STATUS stays PROPOSED "
              "outside the R1-reviewed wave-1 records, because D65 replaces slice review by the global review",
    "CONVENTIONS": "docs/graph/LP/SPEC.md §4: Euclidean ¦·¦ (planeLength, spaceLength) vs max norm on actions; period "
                   "2π angles (L13 converts to period one); G = 1, star mass 1, masses μν_i, max ν = 1, physical AMD "
                   "μC; C = ΣI - ¦L¦ orientation-free (N8, OD-1); thresholds on the chamber carrier OrderedActions "
                   "(n ≥ 2) with attained-minimum characterizations; C(0) ≤ B(I^0) - δ, conclusion C(t) ≤ B(I(t)) - "
                   "δ/2; frozen keplerEnergy is ν_i E_i; MAIN lemmas are d-generic (d ∈ {2,3}) and dimension-specific "
                   "frozen carriers attach at the anchors (SPEC §5 dimension rule); constants depend only on "
                   "(d, n, ν, 𝒜, δ, γ, τ), L5's d_⋆, d_pair only on (n, ν, U, m), chosen before μ and the state",
    "STANDING_ASSUMPTIONS": "-",
    "EXTERNAL_POLICY": "a closed list of Mathlib-level externals lpM:ext-* fixed in SPEC §3 (KIND external, "
                       "LEAN_STATUS EXTERNAL, located at the first appeal in MAIN); cross-track results that a proof "
                       "uses are IMPORTED nodes N:<node> / P:<node> (KIND external, source fields copied from that "
                       "track's graph, NOTE IMPORTED), never read through implementation files; any other unproved "
                       "fact is a step node with NOTE SOURCE_GAP",
    "FROZEN_ANCHORS": ", ".join(anchors),
    "FROZEN_MANIFEST": "manifest/frozen-anchors.json | sha256:auto",
    "WRITER": "kam-lp",
    # the ONE global review of D65 (PASS WITH NOTES, audited ef3c63d0; locator refinements applied by the writer)
    "GLOBAL_REVIEWER": "maud-lp-gglob-1",
    "GLOBAL_REVIEW_REF": "docs/graph/LP/reviews/GLOBAL-review-1.md",
}
(g / "header.txt").write_text("".join(f"{k}: {v}\n" for k, v in H.items()))
print(f"wrote {g / 'header.txt'}: {len(roots)} roots, {len(anchors)} anchors (waves <= {a.wave})")
