# P23-14 prover handoff (branch inp-p2314, cfa7c03; contains inp-p2312 (P23-12, P23-10, P23-05) and P23-02/03/07 via inp; offloaded package run by the main orchestrator; prover on claude-12; two sessions)

## Session 1

Branch inp-p2314. **The declarations `step` and `iterative`-facing `KamHyp`-next assembly are not proved.**
`KamHyp` itself is defined verbatim (with `realFreq`, `dioBase`, `omegaSet`). `step` is not in the tree (no sorry, no stub).
This is an honest partial delivery: infrastructure and the sub-steps of `bpP:p3:step` that were proved.

## Files (all new, KAM/Planetary/TwoScale/)
- `Setting.lean` — `realFreq`, `dioBase`, `omegaSet`, `structure KamHyp` (copied verbatim from P23Signatures.lean).
- `StepFreq.lean` — `isOpen_actionNbhd'`, `actionNbhd_mono`, `freq_im_zero`/`freq_realInclusion_eq` (frequency real at real points from `RealOn`), `coord_mvt`.
- `StepNonres.lean` — constants facts from `KamHyp` (`K_pos`, `R_pos`, `R_le_γ₁/γ₂`, `E_le_M/Mhat`, `eHat_small : 2^14 Ê < 1`, …),
  `freq_diff_bounds` (mean value), `dotC_block_le`, `nonres_arith`, **`twoDiv_of_kamHyp`** (node `stepP:p3:st-nonres`, divisors `alpha₁/alpha₂ = (2/3)γᵢ/K^τ`).
- `StepAvg.lean` — `small_avg` (`64eKE < α₂R`, `E ≤ α₂R/(128K)`; node `st-small`), **`KamHyp.avgHyp`** (the `AvgHyp` of P23-12 `avg` at radius `rhoHat p`, so `avg` applies).
- `StepConst.lean` — **`cutoff_next_le`** (K₊ ≤ 24K), **`rhoHat_next_ge`**, `xval_le`, **`eHat_next_le`** (`8/9 (4s)^(2(τ+1)) Ê²`), **`eHat_next_lt`**, **`small_next`** (nodes `st-const`, `st-quad`; also `ĉÊ₊<1`).
- `StepHess.lean` — `g_bounds` (Cauchy: ‖∂g‖ ≤ 2A/r, ‖∂²g‖ ≤ 16A/r²), `freq_add`, `fderiv_freq_add`, `freq_g_fderiv`.
- `StepPerturb.lean` — `perturb_equiv` (A+B invertible, inverse `A⁻¹∘N⁻¹`, ‖N⁻¹‖ ≤ 2).
- `StepHess2.lean` — `beta_facts`, **`hessian_next`**: for `hp = h + g` on `actionNbhd D (R/4)`: `‖D freq hp‖ ≤ 2M`, last rows ≤ 2M̂, inverse `A` with `≤ 2M̄`, first rows `≤ 2M̄₁`, last rows `≤ 2M̄₂` (exactly the Hessian clause of `step`; nodes `st-dg`, `st-U`).

## Not done (needed to finish `step`)
1. Apply `avg` (via `KamHyp.avgHyp`, `small_avg.1`) and derive: `‖g‖ ≤ 5/4 E` (needs `‖coeff f I 0‖ ≤ E` from `WBound`), displacement bounds (st-disp), `fs` class/bound with `e^{-Ks/6} ≤ xval`.
2. Injectivity of `freq hp` on `actionNbhd D (R/8)` (P23-03 `ball`, `ext_ift`).
3. `ihat` (ball, `ext_ift`, reality for `Dp ⊆ ℝⁿ`), sup bound `10 (M̄ᵢ/M̄) Ê R`, Lipschitz via P23-07 `lip_sup` (`640 n Ê`).
4. Assemble `KamHyp Dp sbar (nextScale p) hp fs` (real_h/real_f/f_class/f_bound on `coefficientDom Dp (R/16) (sbar+s/12)`, holo, injective, hessian via `hessian_next`, `small` via `small_next`, L-bound `initialL ≤ 2L`, widths) and the full conjunction of `step`.

## Checks
- Gate builds succeeded for Setting, StepFreq, StepNonres, StepAvg, StepConst, StepHess, StepPerturb, StepHess2 (final combined rebuild: see end of this file).

## Session 2 (whole package)

Branch inp-p2314. `KamHyp` (Setting.lean) and `step` (Step.lean) are stated verbatim as in
P23Signatures.lean (statement text checked equal programmatically) and proved with no sorry.
`#print axioms KAM.Planetary.step` = [propext, Classical.choice, Quot.sound].

## Files (all KAM/Planetary/TwoScale/, each < 270 lines)
Session 1: Setting (`realFreq`, `dioBase`, `omegaSet`, `KamHyp`), StepFreq, StepNonres (`twoDiv_of_kamHyp`, st-nonres),
StepAvg (`small_avg` st-small, `KamHyp.avgHyp`), StepConst (st-const, st-quad), StepHess, StepPerturb, StepHess2
(`hessian_next`, st-dg/st-U).
Session 2 (new):
- StepSchwarz — Schwarz reflection on a real-centred polydisc (`polydisc_identity`, `schwarz_scalar`, `schwarz_vec`).
- StepMono — monotonicity of `InClass`/`WBound`/`coefficientDom` in the base set; `norm_coeff_zero_le`.
- StepInj — `g_deriv_bounds`, `freq_g_le`, `freq_g_lip`, **`freq_inj`** (st-inj; uses P23-03 `ball`).
- StepIhat — `inv_coord`, **`ihat_exists`** (st-ihat; `ext_ift`, coordinatewise block bounds `10 M̄ᵢE/R`).
- StepReal — `hp_realOn`, **`ihat_real`** (ĩ₊ real on D via Schwarz reflection + injectivity).
- StepDisp — `disp_first/last/theta` (st-disp, constants 3/4 (M̂/M)Ê R, 3/4 Ê R, 3/4 Ê s).
- StepNext — `exp_cutoff_le`, **`next_hyp`** (`KamHyp Dp sbar (nextScale p) hp fs`).
- StepDp — Dp generic facts (`dp_subset_tube`, `dp_nbhd_subset`, `dp_freq_image`), `ihat_const`.
- Step — **`step`**: avg (P23-12) → g bounds → ihat → Dp → next KamHyp; Lipschitz via P23-07 `lip_sup`.

## Approach notes
- `‖g‖ ≤ 5/4 E` from avg's `‖g − coeff f I 0‖ ≤ E/4` and `‖coeff f I 0‖ ≤ E` (`norm_coeff_zero_le`).
- Block bounds of ĩ₊ − id are NOT taken from `ball` part 2 (full norm only): they use the mean value inequality
  (`coord_mvt`) for the inverse `G` of ω₊ on an image ball, whose derivative is `A.symm` (rows ≤ 2M̄ᵢ).
- Reality of ĩ₊(I), I ∈ D: no Schwarz reflection existed in the repo; proved here (coordinatewise 1D identity
  theorem, pattern of `strip_identity`), applied to the vector `freq hp` on `ball (ι I) (R/8)`.
- Displacement constants come out as 3E (avg) rather than 9E (source), so the step bounds follow with room.

## Checks
- Gate builds: `KAM.Planetary.TwoScale.Step` (imports every module) succeeds; no sorry/axiom/maxHeartbeats.
- `scripts/lint_sources.sh`: line-length, module, frozen-anchor, ABI pass; only message "KAM.lean is out of date"
  (expected, KAM.lean not edited).
- `#print axioms KAM.Planetary.step`, `KamHyp.freq_inj`, `KamHyp.ihat_real`: propext, Classical.choice, Quot.sound.
- Remaining warnings are session-1 style (deprecated `if_pos`/`if_neg`/`add_apply`, one unused variable).

## Uncertainties / errata / deviations
- No signature changed. No errata found in P3a step proofs beyond session 1 notes (Hessian bound of g needs no
  factor n; source `80nE/R²` is weaker). Source says displacement `9E/(α s)`; avg here gives `3E`, constants kept
  as in the signature (true, stronger intermediate).
- Note for consumers: `step`'s ihat is existential (G ∘ ω₀ with G from `ext_ift`); only its stated properties are
  specified, and it is meaningful only on `actionNbhd D (R/16)`.

AUDIT FOCUS (design docs/tracks/P/design/P23-LEAN-DESIGN.md revision 2 row P23-14 and proof plan; audits DESIGN-P23-design-audit-{1,2}.md; signatures .drafts/design/P23Signatures.lean; blueprint-P p3a step): (1) KamHyp and step match the signatures EXACTLY; the G2/G3 gaps are paid as the design states; (2) proofs sound (nonresonance, Hessian, inverse images, block constants; P23-12 avg, P23-03 ball/ext_ift, P23-07 lip_sup consumed as designed); no added premises; (3) hygiene (lint incl. 100-char lines). Audit ONLY KAM/Planetary/TwoScale/{Setting,Step*}.lean (compare with branch inp-p2312).
