# P5-CG prover handoff (branch inp-p5cg, 670ab9a; contains inp-p5cl, inp-p5id (audited); offloaded package run by the main orchestrator; prover on claude-12)


**Files:** new `KAM/Planetary/PGAssembly/ComplexGlue.lean` (~150 lines). KAM.lean not edited (lint reports "KAM.lean is out of date" — expected; orchestrator regenerates).

**Declarations:** `KAM.Planetary.compact_real_complexification` (signature verbatim from P45Signatures.lean; node `bpP:p5:ext-loc` helper). Helpers: `local_complexifications_agree`, `exists_pos_le_finset`.

**Approach:** `local_real_complexification` at each x∈X (choice, junk data off X); finite subcover by half-radius real balls (`IsCompact.elim_nhds_subcover`); rho = least half-radius (≥ positive lower bound by Finset induction), M = 1 + ∑ M_i. Glue F z := F_{idx z} z with idx chosen among covering balls. Overlap agreement: complex ball overlap is convex (preconnected, open); componentwise real part of an overlap point lies in both real balls, so `real_slice_identity` applies. Hence G = F_i on B_i, giving differentiability, real-slice identity and bound.

**Checks:** `inp_lake_build.sh … KAM.Planetary.PGAssembly.ComplexGlue`: Build completed successfully, no warnings. `scripts/lint_sources.sh`: check_lean_modules PASS, FROZEN-ANCHOR GUARD OK, ABI HASHES OK (only the expected "KAM.lean out of date" note).
`#print axioms KAM.Planetary.compact_real_complexification`: [propext, Classical.choice, Quot.sound].

**Uncertainties / errata / deviations:** none. No heartbeat issues. Imports only ComplexLocal, RealSlice, Strip.Analytic, ActionNbhd def (no providers/DRAFT_SORRY).

AUDIT FOCUS (design docs/tracks/P/design/P45-LEAN-DESIGN.md row P5-CG and its proof plan; audits DESIGN-P45-design-audit-{1,2,3}.md; signatures .drafts/design/P45Signatures.lean): (1) statement = design signature (compact_real_complexification with uniform radius and bound); (2) proof sound (compact cover, P5-CL and P5-ID consumed as designed); no added premises; (3) hygiene (lint incl. 100-char lines). Audit ONLY KAM/Planetary/PGAssembly/ComplexGlue*.lean.
