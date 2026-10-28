# P4-AF prover handoff (branch inp-p4af, 08e4801; contains inp-p4to (P4-TO, audited); offloaded package run by the main orchestrator; prover on claude-12)

Files: new KAM/Planetary/PGMeasure/AffineSlab.lean (~125 lines). Branch inp-p4af, committed.
Declarations: `KAM.Planetary.affine_slab` (bpP:p4:affine-slab; signature verbatim) plus helper `KAM.Planetary.affine_slab_of_coord`.
Approach: pick coordinate i with |ell i| = ‖ell‖ (max norm); split ℝⁿ⁺¹ = ℝ × ℝⁿ via piFinSuccAbove (Fubini, prod_apply_symm); each section lies in a slab bounded by KAM.Measure.volume_abs_affine_lt_le (slope ell i, offset ∑_{j≠i} ell_j y_j + c); integrate against indicator of cube. Did not need P4-TO Tonelli (direct Fubini, as in KAM/Measure/Slab).
Checks: gate build KAM.Planetary.PGMeasure.AffineSlab: success, no warnings. `#print axioms KAM.Planetary.affine_slab`: [propext, Classical.choice, Quot.sound]. scripts/lint_sources.sh: check_lean_modules PASS, FROZEN-ANCHOR GUARD OK, ABI HASHES OK; only note "KAM.lean is out of date" (expected: root not edited per rules).
Uncertainties/errata/deviations/design signals: none. No heartbeat issues. Hypotheses `hl`, `he` unused in the proof (`have _ := he` silences the linter; hl unused-but-bound in signature without warning).

AUDIT FOCUS (design docs/tracks/P/design/P45-LEAN-DESIGN.md row P4-AF and its proof plan; audits DESIGN-P45-design-audit-{1,2,3}.md; signatures .drafts/design/P45Signatures.lean): (1) statement = design signature (affine_slab), using P4-TO and KAM.Measure.volume_abs_affine_lt_le as designed; (2) proof sound; no added premises; (3) hygiene (lint incl. 100-char lines). Audit ONLY KAM/Planetary/PGMeasure/AffineSlab.lean.
