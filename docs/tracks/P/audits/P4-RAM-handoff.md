# P4-RA + P4-M prover handoff (branch inp-p4ra, f793767; contains P45-S, P4-S, P4-TO, P4-AF, P4-LT, P4-LI, P4-R0, P4-RB (all audited); offloaded package run by the main orchestrator; prover on claude-12)

## Session 1 (P4-RA alone, stopped before the helper ruling)

**Status:** stopped before writing any Lean. Nothing committed (branch inp-p4ra clean at 6e36995). No file created.

## Why
The brief says to copy the module's declarations VERBATIM from /root/code/KAM-inp/.drafts/design/P45Signatures.lean and never
change a signature. That file (and Appendix A of docs/tracks/P/design/P45-LEAN-DESIGN.md, and the three audits) contains
NO declaration owned by `KAM/Planetary/PGMeasure/ResonanceFast.lean`. The package row (design L489) reads only
"frequency-coordinate pullback and fast sections"; the only other text is the prose "Resonances" paragraph (design L260-269).
grep for `ResonanceFast`, `pullback`, `fast section` in the design, audits and signatures finds nothing further.
The final theorem (`two_scale_diophantine_measure`, P4-M) and its steps `dm-slow/dm-y/dm-A/dm-Bstruct/dm-B/dm-sum` are
"local to two_scale_diophantine_measure", so the P4-RA/P4-RB/P4-R0 split of those steps is not fixed by any signature.

## Combined session (P4-RAM)

All committed (last commit f793767). Gate build of `KAM.Planetary.PGMeasure.TwoScale` (imports everything below): OK, no
warnings in my files (one pre-existing warning in Hamiltonian/Diophantine.lean:124). No maxHeartbeats, sorry or axiom; no
design signals. `scripts/lint_sources.sh`: module check PASS, frozen guard OK, ABI hashes OK; only message "KAM.lean is out of
date" (generated, not edited). Lines <= 100; files: ResonanceFast 169, ResonanceFast/Pullback 102, ResonanceFast/Sections 166,
TwoScale 193.

`#print axioms` (scratch, not committed): two_scale_diophantine_measure, resonanceBad_eq, fast_modes_measure_le each
[propext, Classical.choice, Quot.sound].

## Signed declarations proved (TwoScale.lean), statements as in P45Signatures.lean
`measure_c1`, `measure_c2` (verbatim defs), `resonanceBad_eq` (verbatim; the only change is line wrapping at 100 chars),
`two_scale_diophantine_measure` (verbatim, line wrapped). `resonanceBad` itself is P4-S's (Setting.lean), unchanged.
No premise added; none of the signed statements looked false. Imports `KAM.Planetary.Hamiltonian.Diophantine`
(for `twoScaleDiophantine`; no DRAFT_SORRY/provider import).

## Internal helpers (distinct names; blueprint nodes of bpP:p4:two-scale-diophantine-measure)
- Pullback.lean (`stepP:p4:dm-y`): `pullMap` (y,xi)->(g y,xi), `pullMap_lip`, `volume_pullMap_image_le`
  (Lg^(a+b) factor via `KAM.lip_image`), `pushMap`, `pullMap_pushMap`, `mem_pullMap_image_of_resonant`.
- Sections.lean (`stepP:p4:dm-A`): `fastModes` (= K_A: blockFast k != 0, mu LN Lg |k|_1 <= ||k1||/2; complement of RB's
  `largeModes` inside k1 != 0), `fast_dev_y` (N1 + hglip), `fastSection_line_diam` (y_j sections have diameter <= 4 alpha;
  uses the exact l1 split, so no loss vs the blueprint).
- ResonanceFast.lean: `measurableSet_resonanceSet`, `prod_erase_box`, `volume_resonanceSet_fast_le` (per mode, via RB's
  `volume_le_of_line_diam`), `fast_modes_measure_le` (union over K_A <= ofReal(4 (2Ry)^(a-1) latticeS(a+b) tau alpha1 (2 lambda)^b),
  using `lattice_tail`(a)). Replaced the earlier untracked draft `resFast_coord_slice` (unneeded duplicate of `volume_le_of_line_diam`).
- TwoScale.lean: `latticeS_nonneg`, `resonanceBad_subset_union` (resonanceBad ⊆ slow set ∪ pullMap''⋃_{K_A} ∪ pullMap''⋃_{K_B};
  case split on blockFast k = 0 / largeModes / fastModes), then the Sum step (`stepP:p4:dm-sum`) with
  `slow_resonance_measure_le` (P4-R0), `fast_modes_measure_le` (here), `large_modes_measure_le` (P4-RB), core volume finite
  (compact) and positive.

## Uncertainties / errata / deviations
None found. Borelness of the pulled-back sets is not needed: `lip_image` is for outer measure; measurability is used only
for the Tonelli slices (`measurableSet_resonanceSet`, from N1/N2 and the frozen inverse via RB's `continuousOn_pullFreq`).

AUDIT FOCUS (design docs/tracks/P/design/P45-LEAN-DESIGN.md rows P4-RA and P4-M with the P4-M proof plan; audits DESIGN-P45-design-audit-{1,2,3,4}.md; signatures .drafts/design/P45Signatures.lean; blueprint-P p4 two-scale-diophantine-measure): (1) the SIGNED declarations measure_c1, measure_c2, resonanceBad (if touched), resonanceBad_eq, two_scale_diophantine_measure match P45Signatures.lean EXACTLY (byte-level type comparison); (2) the P4-RA fast-section results are INTERNAL helpers under the orchestrator ruling (distinct names, blueprint citations, no conclusion-shaped hypothesis, nothing signed restated or weakened); (3) the proof of two_scale_diophantine_measure is sound and genuinely consumes the slow (P4-R0), fast (P4-RA) and large (P4-RB) helpers; adapters correct; (4) axioms standard; (5) hygiene (lint incl. 100-char lines). Audit ONLY KAM/Planetary/PGMeasure/ResonanceFast*.lean and KAM/Planetary/PGMeasure/TwoScale.lean (compare with branch inp-p4rb).
