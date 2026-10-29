# GAP-P6a prover handoff (branch inp-gp6a, fa91c8ee; off inp; graph-gap programme package run by the main orchestrator)


**File (new, only):** `KAM/Planetary/Newtonian/HamiltonNodes.lean` (~540 lines). No landed file edited. `KAM.lean` NOT regenerated
(lint reports "KAM.lean is out of date"; orchestrator regenerates).

All 8 nodes were NOT_STARTED in DEPGRAPH/AMENDMENTS on this branch: none already closed.

## Node -> declaration (namespace `KAM.Planetary`)
| node | declaration(s) |
|---|---|
| `bpP:p6:hamilton-eqs` | `hamilton_eqs_moving`, `hamilton_eqs_fixed` (block form on W for every real μ/ε, plus curve iff); parts `movingField_blocks`, `fixedField_blocks`, `hasDerivAt_movingField_iff`, `hasDerivAt_fixedField_iff` |
| `stepP:p6:he-dir` | `fderiv_movingHamiltonian_dir`, `fderiv_fixedHamiltonian_dir` (DT(p)δp, DV(q)δq in literal pair-sum form, and DH = DV+DT); calculus re-proved privately (`hasFDerivAt_hnShape`) |
| `stepP:p6:he-coef` | `fderiv_movingHamiltonian_partials`, `fderiv_fixedHamiltonian_partials` (∂_{p_i}, ∂_{q_i} as `fderiv` values) and the X_H block forms above |
| `stepP:p6:he-curve` | `hasDerivAt_iff_bodyVector` (generic), `hasDerivAt_movingField_iff`, `hasDerivAt_fixedField_iff` (iff) |
| `stepP:p6:rc-coords` | `rc_coords_moving` (a_i, b_i derivatives and all linear combinations, ∀ t ∈ J) |
| `bpP:p6:reconstruction-fixed#real-eps` | `fixedField_equations` (ε : ℝ arbitrary) |
| `stepP:p6:rf-eq` | `fixedField_rf_eq` (positivity, q', p', V' = -G m0 g + εG f) |
| `stepP:p6:sp-alg` | `sp_alg` (kinetic identity, potential agreement, difference μ|P|²/(2m0)) |

## Approach
Block forms re-derived from landed public `hamiltonianVectorField_moving/_fixed` (the private block lemmas of Reconstruction.lean were
re-proved). he-dir re-proves the derivative of the common shape with private copies of the Models.lean calculus (names `hn*`). rf-eq positivity
reuses landed `reconstruction_fixed`. Hypotheses are only the node's source hypotheses (NoCollision, curve derivative); no dependency output
is taken as a premise; quantifiers over all of W / all directions d / all t ∈ J; the curve clause stays an iff; ε, μ are arbitrary reals.
(rc-coords/rf-eq omit the source's unused hypotheses μ ≥ 0 resp. keep hm0, hm only where reconstruction_fixed needs them.)

## Checks
- `inp_lake_build.sh ... KAM.Planetary.Newtonian.HamiltonNodes`: Build completed successfully, no warnings in my file.
- `scripts/lint_sources.sh`: all checks pass except "KAM.lean is out of date" (generated; not edited by me).
- `#print axioms` of the 9 main theorems: `propext, Classical.choice, Quot.sound` only.
- No maxHeartbeats, no sorry, lines ≤ 100.

## Uncertainties / errata / deviations
- he-coef "coefficient of δq_i in the double sum" regrouping is delivered via the landed X_H block form (equivalent partial derivatives) rather than re-proving the pair-sum regrouping; he-dir itself is the literal pair-sum form.
- sp-alg states the kinetic part as the explicit expression read off the frozen `movingHamiltonian` (no separate function exists).
- No suspected errata.

ORCHESTRATOR RULING (OVERNIGHT 01:20, 01:35): graph-gap programme for the landed parts. This package appends UNSIGNED exports whose job is to state the LITERAL conclusion of each listed graph node, built from landed declarations; nodes already PROVED or BYPASSED in the graph are skipped. Package definition: section '**GAP-P6a:**' of /root/code/KAM-inp/.drafts/briefs/offload-main/GAP-PLAN-P.md. KAM.lean regeneration is the sub-orchestrator's job at merge, not a finding.

AUDIT FOCUS: for EVERY node in the handoff's node table, read its NODE record in docs/graph/P/DEPGRAPH.md (SOURCE_HYPOTHESES, SOURCE_QUANTIFIERS, SOURCE_CONCLUSION) and the blueprint lines it cites, and give a per-node verdict: does the named declaration state that node's literal conclusion under only the source's hypotheses, with quantifiers in the source's order? An export that takes a proved dependency's OUTPUT as a premise is a FAIL (export from the source hypotheses and build the dependency inside). A node whose export is weaker, conditional on an unsourced premise, or a different statement is a FAIL for that node; list each such node precisely. Audit ONLY KAM/Planetary/Newtonian/HamiltonNodes.lean. Common to all: (a) every SIGNED declaration = signature file EXACTLY; (b) the slice COMPLETE: every graph node the design's node table maps to these modules is established (in the proof or as an export); an UNSIGNED export named after a graph node must state that node's literal conclusion, while a SIGNED declaration follows the signature file (where the design deliberately narrows it, check that every consumer's needs are met); (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no reused public HELPER short name, no harmful root shadow, lines <= 100.
