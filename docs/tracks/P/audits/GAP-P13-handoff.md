# GAP-P13 prover handoff (branch inp-gp13, 3223b514; off inp; graph-gap programme package run by the main orchestrator)


## Files (new, committed; KAM.lean not touched, so lint reports "KAM.lean is out of date" only)
- `KAM/Planetary/Hamiltonian/Part1Nodes.lean` (~245 lines)
- `KAM/Planetary/TwoScale/SumsNodes.lean` (~150 lines)

## Node -> declaration (all in `KAM.Planetary`, unsigned, no new hypotheses beyond source ones)
| node | declaration |
|---|---|
| bpP:p1:typical | `typical (d)`: (1) polar map on Phase 1 is `IsChart 1` on {R>0} + invariance under `+ fullShift k`; (2) `isChart_angleScale`; (3) `IsChart.comp` + `chartPullback_comp` |
| stepP:p1:pc-a | `pc_a c` (symplectic scaling, `det = c^d` literal (not abs), lattice formula) |
| stepP:p1:pc-b | `pc_b hc H z` (field identity with `fderiv`, and both component formulas as `fderiv.comp inr/inl`) |
| tt-an | `tt_an` (analytic + H differentiable) and `tt_an_range` (range in Ψ''range K ⊆ U) |
| tt-lat | `tt_lat_cyl` (a), `tt_lat_phys` (b) |
| tt-inj | `tt_inj_cyl` (a), `tt_inj_phys` (b) |
| tt-lag | `tt_lag` (chain rule, injective, Ω(D𝒦u,D𝒦v)=c·Ω(DK u,DK v)=0) |
| tt-flow | `tt_flow` |
| tt-dio | `tt_dio` (Diophantine clause (vii) of IsPhysicalTorus; (a) has none) |
| bpP:p3b#kam-bounds | `kam_bounds` (needs `0 < n`, to make 1/(8192 n) meaningful) |
| stepP:p3:sum-doubling | `sum_doubling` (abstract) and `PsiSteps.seq_sum_doubling` |
| stepP:p3:sum-weighted | `sum_weighted` (abstract, hyp `c*e0 ≤ 1/2`, weaker than strict) and `PsiSteps.seq_sum_weighted` |

## Approach
Clauses re-proved from public landed lemmas (`chart_field_differentiableAt_iff`, `chart_orbit`,
`fderiv_chart_comp_torus`, `IsChart.bijective_fderiv`); private `transport_core` and
`angleScale_symplectic` re-proved inline. `typical` (1) uses `disc_measure_chart` at a=0,b=1 after
rewriting the explicit map to `oscillatorPolar` (the rewriting equalities are proved inline).
Sums use `sums` (for the pointwise power bound) plus a geometric comparison.

## Checks
- `inp_lake_build.sh /root/code/KAM-inp-gp13 KAM.Planetary.Hamiltonian.Part1Nodes KAM.Planetary.TwoScale.SumsNodes`:
  "Build completed successfully", no warnings in the new files.
- `scripts/lint_sources.sh`: check_lean_modules PASS, frozen guard OK, ABI hashes OK; only message is the expected
  "KAM.lean is out of date" (not edited per rules).
- `#print axioms` of all 17 declarations: `[propext, Classical.choice, Quot.sound]`.
- Lines ≤ 100 cols; no heartbeat options.

## Notes / uncertainties
- `typical`(1): stated for `Phase 1` with the explicit map (q,p)=√(2R)(sin ψ, cos ψ) in the frozen order
  (first component = sin); equals `oscillatorPolar (a:=0) (b:=1)`. Matches the source.
- `tt_flow` needs only `K(θ+t w) ∈ O` at the single time t (weaker than source's all s).
- `tt_lat/inj` take (Q1)/(Q2) in the exact form used by `torus_transport_cyl/phys`.
- No suspected errata and no deviations. No design signals (all default heartbeats).

ORCHESTRATOR RULING (OVERNIGHT 01:20): graph-gap programme for the landed parts. This package appends UNSIGNED exports whose job is to state the LITERAL conclusion of each listed graph node, built from landed declarations. Package definition: section '**GAP-P13:**' of /root/code/KAM-inp/.drafts/briefs/offload-main/GAP-PLAN-P.md (its estimates are UNVERIFIED). KAM.lean regeneration is the sub-orchestrator's job at merge, not a finding.

AUDIT FOCUS: for EVERY node in the handoff's node table, read its NODE record in docs/graph/P/DEPGRAPH.md (SOURCE_HYPOTHESES, SOURCE_QUANTIFIERS, SOURCE_CONCLUSION) and the blueprint lines it cites, and give a per-node verdict: does the named declaration state that node's literal conclusion under only the source's hypotheses, with quantifiers in the source's order? A node whose export is weaker, conditional on an unsourced premise, or a different statement is a FAIL for that node; list each such node precisely. Audit ONLY KAM/Planetary/Hamiltonian/Part1Nodes.lean and KAM/Planetary/TwoScale/SumsNodes.lean. Common to all: (a) every SIGNED declaration = signature file EXACTLY; (b) the slice COMPLETE: every graph node the design's node table maps to these modules is established (in the proof or as an export); an UNSIGNED export named after a graph node must state that node's literal conclusion, while a SIGNED declaration follows the signature file (where the design deliberately narrows it, check that every consumer's needs are met); (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no reused public HELPER short name, no harmful root shadow, lines <= 100.
