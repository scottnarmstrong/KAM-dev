# P4-TO prover handoff (branch inp-p4to, 4ecc0c8; off inp; offloaded package run by the main orchestrator; prover on claude-12)

Files: KAM/Planetary/PGMeasure/Tonelli.lean (new, ~70 lines), namespace KAM.Planetary.
Declarations (signatures verbatim): section_measure_le_of_pairwise_dist, ext_tonelli.
Approach: section lemma — E ⊆ Icc (sInf E) (sInf E + δ) (empty case separately), then volume_Icc.
ext_tonelli — Measure.volume_eq_prod, Measure.prod_apply, pointwise bound by P.indicator (const ofReal δ)
(sections empty off P), lintegral_indicator.
Checks: gate build KAM.Planetary.PGMeasure.Tonelli succeeded, no warnings in file; lint_sources.sh: module/frozen/ABI
checks PASS; only message "KAM.lean is out of date; run scripts/gen_root_imports.py" (expected: new module, KAM.lean not edited per brief — orchestrator must regenerate).
#print axioms of both: [propext, Classical.choice, Quot.sound].
Imports: Mathlib.MeasureTheory.Constructions.Pi, Mathlib.MeasureTheory.Measure.Lebesgue.Basic only.
Note: hypothesis `hd` is unused in both proofs (true without it for the stated conclusion); retained per signature, referenced via `have _ := hd` to avoid the unused-variable linter.
Uncertainties / errata / deviations: none. No heartbeat issues.

AUDIT FOCUS (design docs/tracks/P/design/P45-LEAN-DESIGN.md row P4-TO and its proof plan; audits DESIGN-P45-design-audit-{1,2,3}.md; signatures .drafts/design/P45Signatures.lean): (1) statements = design signatures (ext_tonelli, section_measure_le_of_pairwise_dist); (2) proofs sound (Mathlib product measure used correctly); no added premises; (3) hygiene (lint incl. 100-char lines). Audit ONLY KAM/Planetary/PGMeasure/Tonelli.lean.
