# B12 prover handoff (branch inp-p11b-b12, 9e494720; contains B10 (in audit) and B09; offloaded package run by the main orchestrator)


## Files (all new)
- `KAM/Planetary/WeakKAM/SelectionRecord.lean` (87 lines): `SelectionOutput`, copied VERBATIM from the signature file.
- `KAM/Planetary/WeakKAM/SelectionTests.lean` (128): `SelectionCutoffSpec`, `selection_all_cutoffs`,
  `selectionFiniteTests`, `selection_stage_all`, `selection_tests_of_cutoffs` (non-signed helpers).
- `KAM/Planetary/WeakKAM/Selection.lean` (328): `parameter_selection` (signed, statement verbatim), plus
  helpers `selection_limit_series`, `selectionT_unbounded`, `selectionModeLength_pos`,
  `selectionVarpi_le_half`, `norm_selectionRe_le`, `selectionReal_mem_collar`, `selection_Kinf_subset`.
  No new public name collides with existing KAM names (grepped before defining).
KAM.lean not edited (lint reports it out of date: new modules, expected).

## Approach (graph nodes)
- `ps-iter`: `inductive_lemma` gives `o : SelectionIteration d f (adm_params d ε)`.
- One cutoff family χ_j for ALL stages (`selection_all_cutoffs`, via `smooth_cutoff` on each compact `K_j`), not
  the per-ν family of `finite_measure`. `selection_tests_of_cutoffs` re-proves, for this fixed χ and every ν,
  compactness, `H_ν ⊆ retained = K_{ν+1}`, and `meas K - loss ≤ meas H_ν`, reusing B09 internals
  (`selection_family_measure`, `selection_retained_of_tests`, `isCompact_selection_tests`) without editing B09.
- `ps-lim`: `selection_limit_series` applies `continuous_series_on_compact` (B11) twice on `K_∞ = ⋂ K_j` to
  Re Δω_j and Re Δh_j (envelopes `ell_j`, `2 ε_j`), gives uniform convergence, continuity, and the tails
  `‖ω* − Re ω_m‖ ≤ selectionTail` and `|h* − Re E_m| ≤ 4 ε_m` (needs ϖ ≤ 1/2, proved from the exponent).
- `ps-H`: `Hinf = ⋂_ν H_ν` (every nonzero mode has |k| ≤ T_ν eventually); `H_ν` compact, antitone;
  `tendsto_measure_iInter_atTop` gives `meas Hinf ≥ meas K − loss`. `Hinf ⊆ Kinf` from `H_ν ⊆ K_{ν+1}`.
- `ps-dio`: `limit_bridge` with u = extended(modeStage k) b, v = ω* b, tail ≤ γ T_m^{-τ-1} ≤ γ|k|^{-τ-1}
  (shell: |k| ≤ T_m); conclusion on `Hinf` only, `Kinf` and `Hinf` kept distinct in every field.

## Checks
- Gate build: `inp_lake_build.sh <wt> KAM.Planetary.WeakKAM.Selection` → success, no errors, no sorry in my files.
- `sh scripts/lint_sources.sh`: check_lean_modules PASS; FROZEN-ANCHOR GUARD OK; ABI HASHES OK; only note:
  "KAM.lean is out of date" (generated file, not mine).
- `#print axioms` of `parameter_selection`, `selection_limit_series`, `selection_tests_of_cutoffs`:
  `[propext, Classical.choice, Quot.sound]`.
- Lines ≤ 100 columns; files ≤ 328 lines; no maxHeartbeats, no EuclideanSpace, no provider/DRAFT_SORRY import.

## Uncertainties / errata / deviations
- None: signatures unchanged; no extra hypotheses; no source defect found. `finite_measure` (B09) itself is
  untouched; the record's `finite_measure` field comes from `selection_tests_of_cutoffs` with the shared χ.
- No heartbeat design signals.

AUDIT FOCUS: design docs/tracks/P/design/P11B-LEAN-DESIGN.md row B12 (parameter-selection and finite-test specifications; B10, B11, limit_bridge, tendsto_measure_iInter_atTop) and its node table incl. ps-* steps; P11B design audits; signatures /root/code/KAM-inp/.drafts/design/P11BSignatures.lean (SelectionOutput, parameter_selection). Iteration* is B10 (own audit). Audit ONLY KAM/Planetary/WeakKAM/Selection*.lean. Common to all: (a) every SIGNED declaration = signature file EXACTLY; (b) the slice COMPLETE: every graph node the design's node table maps to these modules is established (in the proof or as an export); an UNSIGNED export named after a graph node must state that node's literal conclusion, while a SIGNED declaration follows the signature file (where the design deliberately narrows it, check that every consumer's needs are met); (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no reused public HELPER short name, no harmful root shadow, lines <= 100.
