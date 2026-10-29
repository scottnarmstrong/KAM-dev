# B14 prover handoff (branch inp-p11b-b14, c8772e97; offloaded package run by the main orchestrator)


**Files (new):** `KAM/Planetary/WeakKAM/CompositionStep.lean` (152 lines), `CompositionBound.lean` (~185),
`Composition.lean` (~190, facade for the signed declarations). Merged `inp-p11b-b12` (B12b) before the final step.

**Signed declarations (verbatim from P11BSignatures.lean):** `SelectionComposition` (structure),
`composition`, `sec_comp_data`. `composition` takes `parameter_selection_adapted` (B12b) and assembles via
`selectionComposition_of_output` (budget context from `free_radius` + `weakBudgetCtx_of`).
No unsigned graph-node exports (co-dom/co-deriv/co-disp/co-inc are local steps; here they are
`selectionComp_domain/_derivative/_angle,_action/_increment`).

**Approach:** stage domain `selectionCompDom`, open, nested (`r_{ν+1}+σ_ν ≤ r_ν`, `s`, `t`, `K` monotone),
`X_ν` maps Dom(ν+1) into Dom(ν). Induction on ν: holomorphy (DifferentiableOn.comp), chain rule
(`fderiv_comp`), product recursion `D-1 = (L-1)M + (M-1)` giving `exp(Σm)-1`, smallness via
`Real.exp_bound_div_one_sub_of_interval` and `exported_sums` (Σm ≤ 2⁻¹²), angle/action telescoping,
increment by `Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le` on the convex fibre, periodic/symplectic/real inductively.

**Checks:** gate build `KAM.Planetary.WeakKAM.Composition` succeeds, no warnings in my files; `scripts/lint_sources.sh`
passes the module/frozen/ABI checks; it reports "KAM.lean is out of date" (generated; orchestrator regenerates).
`#print axioms KAM.Planetary.composition`: `[propext, Classical.choice, Quot.sound]` (same for `selectionComp_increment`).
No `sorry`, no heartbeat options, lines ≤100.

**Deviations / uncertainties:** none to signatures. Earlier I wrote my own adapted selection (SelectionGen); removed
per the orchestrator note, B12b's export is used. Hypotheses of helpers: only `WeakBudgetCtx` (derived), no conclusion-shaped premises.
**Errata:** none found. No design signals (default heartbeats everywhere).

AUDIT FOCUS: design docs/tracks/P/design/P11B-LEAN-DESIGN.md row B14 (composition, sec-comp data, derivative product recursion; B10, B12, B13, HasFDerivAt.comp, increments_open) and its node table incl. co-* steps; P11B design audits; signatures /root/code/KAM-inp/.drafts/design/P11BSignatures.lean (SelectionComposition, composition, sec_comp_data). B14 contains B12 round 2 (in audit: parameter_selection_adapted) and B10. Audit ONLY KAM/Planetary/WeakKAM/Composition*.lean. Common to all: (a) every SIGNED declaration = signature file EXACTLY; (b) the slice COMPLETE: every graph node the design's node table maps to these modules is established (in the proof or as an export); an UNSIGNED export named after a graph node must state that node's literal conclusion, while a SIGNED declaration follows the signature file (where the design deliberately narrows it, check that every consumer's needs are met); (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no reused public HELPER short name, no harmful root shadow, lines <= 100.
