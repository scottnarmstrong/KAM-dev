# P5-CUT prover handoff (branch inp-p5cut, 7b103ba; off inp; offloaded package run by the main orchestrator; prover on claude-10)


**Files:** new `KAM/Planetary/PGAssembly/CutMeasure.lean` (106 lines). Nothing else touched.

**Proved:** `finite_measure_coordinate_cut` (design P5-CUT row; `bpP:p5:st-ivt` helper), signature verbatim
(only prefixed by `open MeasureTheory in`; the signature file opens it globally).

**Approach:** with `F s = nu {x | x j ≤ s}`: right continuity from `tendsto_measure_biInter_gt`
(`cut_tendsto_right`); left continuity (`cut_tendsto_left`) from `tendsto_measure_iUnion_atTop` along
`a - 1/(n+1)`, the union differing from `{x j ≤ a}` by the null slice `{x j = a}`, then upgraded to the
one-sided limit by monotonicity of `F`; glue via `nhdsLT_sup_nhdsGE`; `ENNReal.continuousAt_toReal`.
`intermediate_value_Icc` is not needed here (it is used downstream in Strictness). Helper lemmas live in
namespace `KAM.Planetary.PGAssembly.CutMeasure`.

**Checks:** gate build `KAM.Planetary.PGAssembly.CutMeasure`: success, no warnings.
`#print axioms finite_measure_coordinate_cut`: `[propext, Classical.choice, Quot.sound]`.
`scripts/lint_sources.sh`: check_lean_modules PASS; one over-100-char line was reported and fixed
(rebuilt OK); "KAM.lean is out of date" is the generated root file (not edited, per rules).
No heartbeat overrides, no sorry/axiom, no EuclideanSpace.

**Uncertainties / errata / deviations:** none. Statement true as written; no design signals.

AUDIT FOCUS (design docs/tracks/P/design/P45-LEAN-DESIGN.md row P5-CUT and 'Revision 4'; audits DESIGN-P45-design-audit-{1,2,3,4}.md; signatures .drafts/design/P45Signatures.lean): (1) finite_measure_coordinate_cut = signature file exactly (the 'open MeasureTheory in' prefix must not change the elaborated type); abstract finite measure as designed; (2) proof sound (finite-measure limits, intermediate_value_Icc); no added premises; (3) hygiene. Audit ONLY KAM/Planetary/PGAssembly/CutMeasure.lean.
