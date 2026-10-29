# B19 prover handoff (branch inp-p11b-b19, bd587502; contains B18 (passed), B17, B16; offloaded package run by the main orchestrator)


## Files
- New: `KAM/Planetary/WeakKAM/Evaluation.lean` (377 lines, all lines <= 100 cols). Nothing else changed.

## Signed declarations (verbatim from P11BSignatures.lean)
`selectionHalfCell`, `selectionClosedCell`, `selectionQuotient`, `SelectionEvaluationOutput`,
`evaluation_bilipschitz` (sorry-free), `situation`.
Graph nodes eb-bounds / eb-ext / eb-meas / eb-cpt are the fields `bilipschitz`/`inverse_bound`,
`extension*`, `image_*`/`measure_*`, `closed_image_compact`/`lattice_union`/`quotient_compact`.

## Approach
- `lipschitz_family` (B18) gives the record `L`. `mcshane_prod` (S = {z | z.2 ∈ Kinf}, Λ = 2⁻¹⁰) extends
  `defect b θ` to a global Λ-Lipschitz `Φ`. Packaged as `EvalExtData Kinf ev lam` (Φ, bounds, `ev = id+Φ` on
  Kinf-fibres, integer periodicity of `ev` from `L.periodic`); `E = id + Φ`.
- `lipeo_bounds`/`lipeo_onto`: bilipschitz, inverse bound, bijectivity. `lip_image_prod`: upper bound for `E`;
  LOWER bound through `E⁻¹` (Equiv.ofBijective symm) with Λ=(1-lam)⁻¹, giving factor (1-lam)^(2n)
  (not the reciprocal). `measure_coarse` follows from 2⁻¹ ≤ 1 - 2⁻¹⁰.
- Half cell = ⋃ compact inner boxes `selectionInnerBox H j` (angles in [0, 1-1/(j+1)]); image = ⋃ E''box_j
  (compact, hence closed / σ-compact / measurable). `volume (halfCell H) = volume H` (volume_pi_Ico).
- Closed cell image compact; `lattice_union` uses floor decomposition and periodicity of `ev` (NOT of Φ);
  quotient image equals the image of the closed cell (`AddCircle` invariance under integer translation), compact.

## Checks
- `inp_lake_build.sh <wt> KAM.Planetary.WeakKAM.Evaluation`: "Build completed successfully (9216 jobs)", no
  warnings from Evaluation.lean.
- `#print axioms KAM.Planetary.evaluation_bilipschitz`: [propext, Classical.choice, Quot.sound].
- `scripts/lint_sources.sh`: check_lean_modules PASS, FROZEN-ANCHOR GUARD OK, ABI HASHES OK; the only failure
  is "KAM.lean is out of date; run scripts/gen_root_imports.py" (new module; KAM.lean is not mine to edit).
- No sorry / maxHeartbeats / EuclideanSpace; no provider or DRAFT_SORRY imports (imports: Mathlib,
  ParameterLipschitz, KAM.Measure.{McShane,Lipeo,Lipschitz}).
- Short-name uniqueness grepped across KAM for all unsigned helpers (EvalExtData, selectionInnerBox,
  selectionHalfCell_eq, selectionClosedCell_eq, volume_selectionHalfCell, selectionHalfCell_subset,
  selectionClosedCell_subset, selectionClosedCell_compact, selectionInnerBox_compact,
  selectionHalfCell_eq_iUnion, selectionQuotient_add_lattice, continuous_selectionQuotient): all new.

## Uncertainties / errata / deviations
- None: signatures unchanged, no statement needed extra hypotheses. No design signals (default heartbeats).
- Regenerate KAM.lean (orchestrator) to include the new module.

AUDIT FOCUS: design docs/tracks/P/design/P11B-LEAN-DESIGN.md row B19 (evaluation-bilipschitz, half-cell, lattice/quotient compactness; B16, B17, B18, mcshane_prod, lipeo_onto, lip_image_prod) and its node table incl. eb-* steps; P11B design audits; signatures /root/code/KAM-inp/.drafts/design/P11BSignatures.lean. Audit ONLY KAM/Planetary/WeakKAM/Evaluation.lean. Common to all: (a) every SIGNED declaration = signature file EXACTLY; (b) the slice COMPLETE: every graph node the design's node table maps to these modules is established (in the proof or as an export); an UNSIGNED export named after a graph node must state that node's literal conclusion, while a SIGNED declaration follows the signature file (where the design deliberately narrows it, check that every consumer's needs are met); (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no reused public HELPER short name, no harmful root shadow, lines <= 100.
