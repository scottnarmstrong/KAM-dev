# GAP-I1c prover handoff (branch inp-gi1c, 8511ce72; off inp; track I graph-gap programme package run by the main orchestrator)


Files: new `KAM/Iso/Linear/FullRangeAnyOmega.lean` (~290 lines). No landed file edited.

## Node map
- `bpI:p1:reduced` (a)-(d), literal any omega -> `KAM.Iso.Linear.AnyOmega.reduced_anyOmega`
  (helpers `fi_dL_anyOmega`, `fi_LtOXN_anyOmega`, `fi_reduced_anyOmega`,
  `reducer_mulVec_isoResidual_anyOmega`).
- `bpI:p1:perturbation-noA5` (a)-(e), literal any omega (`‖ω‖ ≤ Θ`) ->
  `KAM.Iso.Linear.AnyOmega.perturbation_noA5_anyOmega`
  (helpers `norm_normalField_sub_le_strip_anyOmega`, `norm_torsion_sub_le_anyOmega`).
Both nodes were NOT_STARTED on the branch (checked in docs/graph/I/DEPGRAPH.md).

## Approach
Standing data is a `Setting` at its own frequency ω₀ (the source setting includes one); it supplies
only omega-free Hamiltonian facts (differentiableOn_ham, ham_symplectic, norm_linMat_le,
norm_linMat_sub_le, Params). The statement's ω is a separate arbitrary `Fin n → ℝ`, no Diophantine
hypothesis. The omega-dependent landed steps (fi_dL, fi_LtOXN, fi_reduced, the pointwise item (b),
pt-xn strip, pt-torsion) are re-proved with the landed proofs' bodies. No conclusion-shaped
premises; no re-proof of ham_mvt was needed.

## Checks
- `inp_lake_build.sh /root/code/KAM-inp-gi1c KAM.Iso.Linear.FullRangeAnyOmega`: Built, 3198 jobs, no warnings shown.
- `#print axioms` of both main theorems: `[propext, Classical.choice, Quot.sound]`.
- `scripts/lint_sources.sh`: check_lean_modules PASS, frozen guard OK, ABI OK; reports
  "KAM.lean is out of date" (expected: new module, KAM.lean is orchestrator-generated, not edited).
- Lines ≤ 100 cols; no maxHeartbeats; no sorry/axiom.

## Uncertainties / deviations / errata
- The Setting at ω₀ is a hypothesis (source setting data includes a Diophantine omega); the lemma
  does not require the statement's ω to be related to ω₀. If the owner wants no ω₀ at all, a
  Hamiltonian-only structure would be needed (~80+ lines, ham_mvt re-proof): not done.
- Source says tau >= 0 while Setting has tau >= n-1 (N1, unchanged, not addressed here).
- No new suspected source errata.

ORCHESTRATOR RULING (OVERNIGHT 05:10): the source states bpI:p1:reduced and perturbation-noA5 for ANY frequency omega, while the landed Lean (and GAP-I1a's reduced_src / perturbation_noA5_src) take a Diophantine omega (audit GAP-I1a-audit-1 F1). This package exports the literal any-omega statements. Plan: /root/code/KAM-inp/.drafts/briefs/offload-main/GAP-PLAN-I.md section GAP-I1c.

AUDIT FOCUS: for bpI:p1:reduced and bpI:p1:perturbation-noA5, read the NODE records in docs/graph/I/DEPGRAPH.md (graph:2389, :2712; SOURCE_HYPOTHESES, SOURCE_QUANTIFIERS, SOURCE_CONCLUSION) and blueprint-I lines 483-503, 566-577; per-node verdict: does reduced_anyOmega / perturbation_noA5_anyOmega state the literal conclusion for ARBITRARY omega (with only the source's bound, e.g. |omega| <= Theta) under only the source's hypotheses, quantifiers in source order? Is the use of a Setting at its own frequency omega_0 only for omega-free Hamiltonian facts legitimate (the source setting includes one), with no Diophantine assumption on the tested omega? An export taking a proved dependency's OUTPUT as a premise is a FAIL. Audit ONLY KAM/Iso/Linear/FullRangeAnyOmega.lean. Common to all: (a) every SIGNED declaration = signature file EXACTLY; (b) the slice COMPLETE: every graph node the design's node table maps to these modules is established (in the proof or as an export); an UNSIGNED export named after a graph node must state that node's literal conclusion, while a SIGNED declaration follows the signature file (where the design deliberately narrows it, check that every consumer's needs are met); (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no reused public HELPER short name, no harmful root shadow, lines <= 100.
