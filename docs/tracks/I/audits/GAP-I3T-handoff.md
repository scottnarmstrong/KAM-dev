# GAP-I3T prover handoff (branch inp-gi3t, 2167804f; off inp; track I graph-gap programme package run by the main orchestrator)


Files: new `KAM/Iso/Charts/ToriIG1.lean` (~100 lines). No landed file touched.

Node `stepI:p3:tori-ig1` (was NOT_STARTED) -> declarations (all unsigned, no new premises):
- `KAM.Iso.Confinement.TorusOutput.realRestriction_analyticOnNhd` (hs : 0 < s0): T1 real-analyticity
  of `realRestriction K` on univ (via `KAM.analyticOnNhd_realRestriction`).
- `KAM.Iso.Confinement.TorusOutput.realHamiltonian_realRestriction_eq`: T3 at real theta,
  `realHamiltonian h f (realRestriction K x) = E` (copy of CF/Graph.lean:209-212 argument).
- `KAM.Iso.Charts.ToriSide.ig1_literal` (hs, T : ToriSide ...): T1 (holo, primary, real, real-analytic),
  T2 (invarianceError = 0; gamma, omega*, st with IsDiophantine gamma 2 omega*, omega_t = st • omega*,
  1 < st < sigmaOmegaConst), T3 (strip energy + real energy), T5 (frequency on ray, 2 < sc < 4 Mg/mh,
  ‖omega_t - ∇h(I)‖ ≤ C_K ε), plus omega* ≠ 0 and omega_t ≠ 0 (from Diophantine at k = e_0, st > 1).
These repair the `bpI:p3:tori` over-claim (T1 real-analytic, real-theta T3, omega± ≠ 0).
K_± := K_∞ is the `K` of `ToriSide` (built by `toriSide_of_applyOut`).

Not done: optional export 4 (`tori_ig1` restating `tori` with the strengthened clauses); `tori`'s
quantifier structure is unchanged and exports 1-3 already carry the node's literal conclusion.

Checks: `inp_lake_build.sh /root/code/KAM-inp-gi3t KAM.Iso.Charts.ToriIG1` -> "Built ... Build completed
successfully" (no warnings in my file). `#print axioms` of all three: propext, Classical.choice, Quot.sound.
`scripts/lint_sources.sh`: module check PASS, frozen guard OK, ABI OK; only message "KAM.lean is out of
date; run scripts/gen_root_imports.py" (expected: KAM.lean is generated, I did not edit it; orchestrator
must regenerate). No line > 100 cols.

Uncertainties: none mathematical. Errata/deviations: none. Design signals: none.
Note: `ApplyAux.rhoInf_pos` used because `Confinement.rhoInf_pos` is private.

ORCHESTRATOR RULING (OVERNIGHT 05:10): track I graph-gap programme (/root/code/KAM-inp/.drafts/briefs/offload-main/GAP-PLAN-I.md, section GAP-I3T): append-only exports stating literal node conclusions; also repairs the over-claim of the PROVED parent bpI:p3:tori (T1 real-analyticity, real-theta T3). KAM.lean regeneration is the sub-orchestrator's job at merge.

AUDIT FOCUS: read NODE stepI:p3:tori-ig1 and bpI:p3:tori in docs/graph/I/DEPGRAPH.md (SOURCE_HYPOTHESES, SOURCE_CONCLUSION) and the blueprint-I lines they cite. Verdict: does ig1_literal (or the named declaration) state tori-ig1's literal conclusion (T1-T5 as the node lists) under only the source's hypotheses, quantifiers in source order? Do the three exports together supply the T1 real-analyticity and real-theta T3 clauses that bpI:p3:tori claims (so its over-claim note can be cleared)? Is it acceptable that the optional restated tori_ig1 bundle was not written (i.e. does one declaration state the node)? An export taking a proved dependency's OUTPUT as a premise is a FAIL. Audit ONLY KAM/Iso/Charts/ToriIG1.lean. Common to all: (a) every SIGNED declaration = signature file EXACTLY; (b) the slice COMPLETE: every graph node the design's node table maps to these modules is established (in the proof or as an export); an UNSIGNED export named after a graph node must state that node's literal conclusion, while a SIGNED declaration follows the signature file (where the design deliberately narrows it, check that every consumer's needs are met); (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no reused public HELPER short name, no harmful root shadow, lines <= 100.
