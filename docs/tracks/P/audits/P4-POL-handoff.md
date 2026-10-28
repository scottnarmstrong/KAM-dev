# P4-POL prover handoff (branch inp-p4pol, a7a3294; off inp; offloaded package run by the main orchestrator; prover on claude-12)

ORCHESTRATOR NOTE: the prover's last commit 9a65376 ('line-length lint fixes') accidentally truncated Polar.lean (737 -> 246 lines). The orchestrator restored the full c0c8e4e content in a7a3294, keeping the prover's wraps and wrapping three more lines; the module rebuilds. Audit the RESTORED file at HEAD.


## Files
- NEW `KAM/Planetary/PGMeasure/Polar.lean` (≈737 lines, single module). No other file touched. KAM.lean NOT regenerated (needs `scripts/gen_root_imports.py` by the orchestrator; lint reports "KAM.lean is out of date").

## Declarations (verbatim signatures)
`oscillatorPolar`, `oscillatorPolar_eq_polarMap` (proved by `rfl`), `polarCellMap`, `disc_measure_chart`, `disc_measure_image`, `disc_measure` (numeric volume + null-centre coverage, F6), `disc_measure_shell`.
Helper public lemmas: `hasFDerivAt_oscillatorPolar`, `abs_det_fderiv_oscillatorPolar`, `polarCellMap_injOn`, `oscillatorPolar_lattice`, `phase_ext_blocks`, simp lemmas `oscillatorPolar_*`/`polarCellMap_*` coordinates.

## Approach
- Chart: explicit componentwise Fréchet derivative (HasFDerivAt via `hasFDerivAt_pi'`, `Fin.addCases`); analyticity from sqrt/sin/cos; symplecticity by splitting the sum over `Fin (a+b)` into fast (identity) and slow (same identity as P7 `polar1_symplectic`); |det|=1 from P1 `abs_det_of_symplectic`; injectivity/lattice via `polar2_eq` (squaring) + `cos/sin` integer-shift lemma.
- `disc_measure_image`: P1 `IsChart.comp` (angleScale 2π ∘ oscillatorPolar) gives |det|=(2π)^(a+b); Mathlib `lintegral_abs_det_fderiv_eq_addHaar_image` and `measurable_image_of_fderivWithin`.
- `disc_measure`: cell \ polar image ⊆ {some slow (p_j,q_j)=0} (explicit preimage via `Complex.arg`), a null set (coordinate hyperplanes); volume via image formula and `volume_joinedActions` (Collar).
- `disc_measure_shell`: cover by null set ∪ ⋃_j polar image of box with j-th action capped at l; union bound; ENNReal arithmetic (b≥1 case, b=0 trivial).

## Checks
- `nice -n 5 inp_lake_build.sh /root/code/KAM-inp-p4pol KAM.Planetary.PGMeasure.Polar`: "Build completed successfully (9120 jobs)" on final commit; only pre-existing warnings in other files (KAM/Kepler/Mass.lean) plus unused-binder warnings on verbatim signature binders in `disc_measure_chart`.
- `scripts/lint_sources.sh`: check_lean_modules PASS, FROZEN-ANCHOR GUARD OK, ABI HASHES OK; only remaining complaint is "KAM.lean out of date" (generated). Over-100-char lines were fixed afterwards (awk finds none); lint not re-run in full after that fix.
- `#print axioms KAM.Planetary.disc_measure`: [propext, Classical.choice, Quot.sound] (checked pre-cleanup; other results use the same toolbox, no `#print axioms` for the others was run).
- No sorry/axiom/maxHeartbeats in the file.

## Uncertainties / errata / deviations
- No signature changes; no extra hypotheses; no errata found. `disc_measure_shell` hypothesis `hlr : l < r^2/2` and `hr` turn out not to be needed beyond the statement (unused in the proof apart from positivity of r²/2) — harmless.
- Only imports added beyond the brief: frozen Defs `CylinderCell`, `OscillatorAction`, and `PGMeasure.Collar` (for `volume_joinedActions`).
- Design signals: none (all proofs elaborate at default heartbeats; file well under 1500 lines).

AUDIT FOCUS (design docs/tracks/P/design/P45-LEAN-DESIGN.md row P4-POL, finding F6 and 'Revision 4'; audits DESIGN-P45-design-audit-{1,2,3,4}.md; signatures .drafts/design/P45Signatures.lean): (1) statements = signature file exactly (oscillatorPolar, oscillatorPolar_eq_polarMap, polarCellMap, disc_measure_chart, disc_measure_image, disc_measure, disc_measure_shell); disc_measure includes the null-centre coverage of cylinderCell by the polar image as well as its numeric volume (F6); (2) proofs sound (area formula, P1 IsChart, P7 polarMap reused, no duplicate Poincare chart, no change to its action domain); no added premises; (3) the orchestrator's restoration is faithful (compare with c0c8e4e); (4) hygiene. Audit ONLY KAM/Planetary/PGMeasure/Polar.lean.
