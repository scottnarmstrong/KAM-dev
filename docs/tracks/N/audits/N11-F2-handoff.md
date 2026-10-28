# N11-F2 prover handoff (branch inp-n11f2, 1d5683c5; offloaded package run by the main orchestrator)


## Files
- NEW `KAM/Nekhoroshev/Partial/CanonicalMap.lean` (~290 lines)
- NEW `KAM/Nekhoroshev/Partial/ExtFlow.lean`: the signed `def extFlow` (verbatim). It did not exist anywhere in KAM
  (F1's Composition.lean is not yet written; n11f1 worktree had no copy). **F1 must import ExtFlow and not redefine
  `extFlow`** (orchestrator: dedupe on merge). Not in design module list; added so F1/F2 share one copy.

## Problem (stop-and-report)
Signed `canonical_map` has no hypothesis giving `0 < b.c`. `b.c = 2π/lam²`, `lam = w/rB`, so `b.c = 0` when
`b.w = 0` or `b.rB = 0` (division by zero). E1's `symplectic` (consumed for `ExtCanonical b.c U Φ`) needs `0 < c`.
For c = 0 the statement is probably still true (q,p frozen; only the (θ,I)-block matters) but that needs a different
proof (the degenerate form is not preserved on directions with q,p components), not a wrapper of E1. I did not change
the signature. Request an owner ruling: either add `hc : 0 < b.c` (all consumers have it via `ExtNFHyp.radius_pos`,
`slow_width_pos`) or assign a c = 0 symplectic lemma.

## Delivered
- `canonical_map_core`: ALL signed clauses except `ExtCanonical b.c U Φ`, with the signed hypotheses exactly
  (images of Φ and Ψ on U into Dom(R-ρ,s-σ), holomorphy, fast/angle/slow displacement incl. `b.c*V/ρ`,
  integer-angle equivariance, Ψ∘Φ = id = Φ∘Ψ and Φ z ∈ U on Dom(R-2ρ,s-2σ), derivative estimate, reality).
- `canonical_map_of_pos`: the full signed conclusion with the extra hypothesis `hc : 0 < b.c` (distinct name;
  conditional helper, NOT standing in for `canonical_map`). Once the ruling is made, `canonical_map` is
  `canonical_map_of_pos` (or by_cases with the c=0 lemma).
- Approach: generic Part 5 flow (`flow_a/b/c/d`, `SmallField`) with gauge diag(σ⁻¹,ρ⁻¹); `vf` (N11-C) plus
  a Cauchy-loss θ-derivative bound for the e·σ fast bound; MVT along trajectories; `flow_real` (E1) with
  `real_system` for reality of `wfield`; `symplectic` (E1) for canonical.

## Checks
- `lake build KAM.Nekhoroshev.Partial.CanonicalMap` via gate: success, no warnings/sorry in my files.
- `scripts/lint_sources.sh`: check_lean_modules PASS, FROZEN-ANCHOR GUARD OK, ABI OK; it reports
  "KAM.lean is out of date" (generated; not edited by me, per rule).
- `#print axioms canonical_map_core`, `canonical_map_of_pos`: [propext, Classical.choice, Quot.sound].
- No maxHeartbeats; lines ≤100; no EuclideanSpace.

## Errata / deviations
- Deviation: extra module ExtFlow.lean; extra hypothesis only in `canonical_map_of_pos`. No source errata.

ORCHESTRATOR RULING (OVERNIGHT 21:15): the signed canonical_map now carries (hc : 0 < b.c) after phi (N11Signatures.lean lines 301-302; b.c = 2 pi/(w/r_B)^2 is 0 in Lean when w or r_B vanishes, and the source radii are positive). Commit 1d5683c5 renamed the prover's canonical_map_of_pos to the signed canonical_map. Check it against the AMENDED signature and judge whether hc is a faithful source positivity premise (no hidden proof content) and whether every consumer can discharge it. ExtFlow.lean holds the signed def extFlow, shared with N11-F1.

AUDIT FOCUS: design docs/tracks/N/design/N11-LEAN-DESIGN.md row N11-F2 (canonical-map a-e incl both map images and the slow displacement) and its node table; both N11 design audits; signatures /root/code/KAM-inp/.drafts/design/N11Signatures.lean. Flow/Symplectic*.lean are N11-E1 (in audit). Audit ONLY KAM/Nekhoroshev/Partial/{ExtFlow,CanonicalMap}.lean. Common to all: (a) every SIGNED declaration = signature file EXACTLY; (b) the slice COMPLETE: every graph node the design's node table maps to these modules is established (in the proof or as an export); an UNSIGNED export named after a graph node must state that node's literal conclusion, while a SIGNED declaration follows the signature file (where the design deliberately narrows it, check that every consumer's needs are met); (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no reused public HELPER short name, no harmful root shadow, lines <= 100.
