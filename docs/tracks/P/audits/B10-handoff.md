# B10 prover handoff (branch inp-p11b-b10, 05e6b5aa; contains B09 (passed); offloaded package run by the main orchestrator)


Branch `inp-p11b-b10` (off inp with b09 merged). All edits committed. No edit to `KAM.lean`,
`README.md`, `KAM/Frozen/`, `manifest/`, or any other package's file. No merge/push.

## Files (all new, 13 modules, 2153 lines, all <= 418 lines, all lines <= 100 columns)
`Iteration` (facade + signed exports) imports: `IterationRecord` (verbatim `SelectionIteration`),
`IterationAssemble` (coherent assembly), `IterationStep` (step fields), `IterationStage`
(`stepChain`, `stage_hyp`), `IterationRetained`, `IterationIncrement`, `IterationBase`,
`IterationAux`, `IterationPred`, `IterationFacts`, `IterationParam`, `IterationBridge`.

## Signed declarations (statements copied verbatim from `.drafts/design/P11BSignatures.lean`)
`SelectionIteration` (record), `inductive_lemma`, `inductive_lemma_adapted`,
`selection_iteration_parameter_blocks`, `selection_iteration_parameter_first`. All proved,
no `sorry`. Also the design's local supplier `selection_real_angle_derivative_on_collar`
(N1 gate; proved, see below).

## Approach
* Coherent recursion: `IterPre ν` / `IterPost ν` (the `SelectionIteration` fields at the index ν /
  at the step ν→ν+1), `IterPrefix ν`; `ChainAgree` records what a prefix reads, so prefixes
  transfer along the sequence. `selectionIteration_of_step` builds the sequence of prefixes by
  recursion (choice of one successor each time) and reads the infinite chain off it (one chain,
  not independent existentials). Base: `iterPre_base` (R₀ of `initial`). Step: `iterPrefix_step`.
* Step (`stepChain`): `K_{ν+1} := selectionRetained`, `Δω_ν,Δh_ν := p11DeltaW/H T_ν R_ν` on the
  WHOLE collar B_ν (`cutoff_delta`, `cutoff_delta_real`: from `p11_cutoff_coeff`, no divisor),
  `X_ν`, `R_{ν+1}` from the canonical step at `E=K_{ν+1}`, `t=t_{ν+1}`, `r=r_ν`, `δ=σ=σ_ν`,
  `q=Q`, `D=D_ν`, `L=2C₁` (`stageStep`, `StepFacts`, `stage_hyp`). C1/C2/C3 and the remainder
  recursion are `IterationFacts` (from B03 `strip_budget`/`schedule_props`, B13 `wbud_*`).
  Divisor on `K_{ν+1}` from B08 `finite_divisor`; nonemptiness of `K_{ν+1}` from the finite
  measure proof (see deviation 1); compactness of `K_{ν+1}` (`selectionRetained_isCompact`).
* `‖Dω_ν‖ ≤ 2C₁` derived from the chain alone (`selection_frequency_derivative_le`: `param_cauchy`
  at `t'=t_j/2`, `∑ 4ε_j/(s_j t_j) ≤ C₁`).
* Gradient of h is real at real points (`selection_gradient_real`).
* O1 = `chain`+`finite_divisor`; O2 = `increment_*`, `energy_bound`, `chain` fields; O3 = `map_*`;
  O4 = `map_parameter_bound` (joint, `param_cauchy_gen`, any j incl. 0) and the two helpers
  (separate A / α bounds, `param_cauchy_gen` applied to each component); O5 = `normal_form`.
* N1 collar supplier: `step_real_lipschitz_collar` (IterationParam) is the P11A
  `step_real_lipschitz` proof with `b` in the whole collar `E+t` (its proof only ever used
  `realInclusion b ∈ actionNbhd`), giving `real_angle_derivative` for every real
  `selectionReal b ∈ K_{ν+1}+t_{ν+1}`. `selection_real_angle_derivative_on_collar` exports it at the
  extended chain. P11A files untouched; no ODE argument was duplicated.

## Checks (all run, last on the final commit)
* `inp_lake_build.sh /root/code/KAM-inp-p11b-b10 KAM.Planetary.WeakKAM.Iteration` : "Build completed
  successfully (9197 jobs)" (also builds B09 FiniteMeasure* in this worktree for the first time).
* `sh scripts/lint_sources.sh`: `check_lean_modules: PASS`, `FROZEN-ANCHOR GUARD OK`,
  `ABI HASHES OK`, no long-line report, but prints `KAM.lean is out of date; run
  scripts/gen_root_imports.py` (expected: new modules; I may not edit `KAM.lean`; the orchestrator
  must regenerate it).
* `#print axioms` for `inductive_lemma`, `inductive_lemma_adapted`,
  `selection_iteration_parameter_blocks`, `selection_iteration_parameter_first`,
  `selection_real_angle_derivative_on_collar`, `iterPrefix_step`: only
  `[propext, Classical.choice, Quot.sound]`.
* No `sorry/axiom/unsafe/opaque`, no heartbeat or recursion option, no `EuclideanSpace`; unique
  short names checked by grep over KAM (only my own `ChainAgree.*` repeat).

## Deviations / notes
1. B09's `finite_measure` is stated only at `adm_params d ε`, but `inductive_lemma_adapted` needs the
   retained set at the adapted radius. I did not touch B09: `IterationRetained` repeats its
   proof (`selection_stage_close_gen`, `finite_measure_gen`) for the schedule
   `selectionSchedGen d s₀ ε₀` (free `s₀,ε₀`, hypothesis `SelectionAdmissibility`). Same proof,
   `adm_params d ε` and `selectionAdapted d ε` are instances (definitional). If B09 is later
   generalised, `IterationRetained` can be reduced to a re-export.
2. The iteration is proved at `selectionSchedGen d s₀ ε₀`, from `WeakBudgetCtx` (B13's context,
   built by `weakBudgetCtx_of`), then specialised (`selectionIteration_gen`).
3. `IterPre` carries one extra internal field `energy_real` (not in the record).
4. Graph steps il-p0 … il-map are local proof blocks (not exported), as the design specifies.
   Graph node `fr-other` (p11a4) is still discharged by B10/B12/B13 jointly (B07 note): the B10
   part is `inductive_lemma_adapted`.
5. Hypothesis `WeakBudgetCtx` is not conclusion-shaped (admissibility A1–A6 + schedule data).

## Suspected errata in sources
None found in the pinned sources used by B10.

## Design signals
No heartbeat problem: every declaration elaborates at default heartbeats; the largest proof
(`iterPost_step`) is about 150 lines.

AUDIT FOCUS: design docs/tracks/P/design/P11B-LEAN-DESIGN.md row B10 (inductive-lemma, coherent prefix recursion, O1-O5; parameter_blocks/parameter_first; B03, B06, B07, B08, B09, B13; cutoff, canonical_step, affine_flow) and its node table; P11B design audits; signatures /root/code/KAM-inp/.drafts/design/P11BSignatures.lean. Check in particular that the infinite chain is ONE coherent chain (not independent existentials per index) as the design requires, and the N1-gate supplier selection_real_angle_derivative_on_collar. Audit ONLY KAM/Planetary/WeakKAM/Iteration*.lean. Common to all: (a) every SIGNED declaration = signature file EXACTLY; (b) the slice COMPLETE: every graph node the design's node table maps to these modules is established (in the proof or as an export); an UNSIGNED export named after a graph node must state that node's literal conclusion, while a SIGNED declaration follows the signature file (where the design deliberately narrows it, check that every consumer's needs are met); (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no reused public HELPER short name, no harmful root shadow, lines <= 100.
