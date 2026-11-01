/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.KamStep.NewHamTransport
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Lipschitz dependence of the flow quantities on time (blueprint-W `bpW:w5:new-ham` step `n-field`)

Off-frontier, source-faithful infrastructure (W5-STEP); the dependency graph is still being built.

For the smoothing flow of `X = ι ∘ Z` with `FlowHyp`: `‖Ψ^t - Ψ^{t'}‖ ≤ M|t-t'|`,
`‖φ^t - φ^{t'}‖ ≤ M|t-t'|` (for `‖ι g‖ ≤ ‖g‖`) and
`‖DΨ^t - DΨ^{t'}‖ ≤ (M/δ) e^{M/δ} |t-t'|`; these feed `smoothing_integral`.
-/

@[expose] public section

open Set Metric Filter Topology MeasureTheory intervalIntegral
open scoped Interval

namespace KAM.Wave

variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [CompleteSpace G]
  {ι : G →L[ℂ] F} {Z : F → G} {V U : Set F} {M δ : ℝ}
  (h : FlowHyp (smoothField ι Z) V U M δ) (hZ : DifferentiableOn ℂ Z V)
  (hb : ∀ z ∈ V, ‖Z z‖ ≤ M)
include h hZ hb

omit [CompleteSpace G] in
theorem norm_smoothDisp_time_sub_le {w : F} (hw : w ∈ U) {t t' : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1)
    (ht' : t' ∈ Icc (-1 : ℝ) 1) :
    ‖smoothDisp ι Z t w - smoothDisp ι Z t' w‖ ≤ M * |t - t'| := by
  unfold smoothDisp
  have hc := continuousOn_smooth_integrand h hZ hw
  have h1 : IntervalIntegrable (fun τ => Z (holoFlow (smoothField ι Z) τ w)) volume 0 t :=
    (hc.mono (uIcc_subset_Icc' ht)).intervalIntegrable
  have h2 : IntervalIntegrable (fun τ => Z (holoFlow (smoothField ι Z) τ w)) volume 0 t' :=
    (hc.mono (uIcc_subset_Icc' ht')).intervalIntegrable
  rw [integral_interval_sub_left h1 h2]
  refine norm_integral_le_of_norm_le_const fun τ hτ => ?_
  have hτ' : τ ∈ Icc (-1 : ℝ) 1 := by
    have := uIoc_subset_uIcc hτ
    exact (uIcc_subset_Icc ht' ht) this
  exact hb _ (h.mem_V_of_ball hw (holoFlow_mem_ball h hw hτ'))

theorem norm_flow_time_sub_le (hι : ∀ g, ‖ι g‖ ≤ ‖g‖) {w : F} (hw : w ∈ U) {t t' : ℝ}
    (ht : t ∈ Icc (-1 : ℝ) 1) (ht' : t' ∈ Icc (-1 : ℝ) 1) :
    ‖holoFlow (smoothField ι Z) t w - holoFlow (smoothField ι Z) t' w‖ ≤ M * |t - t'| := by
  rw [holoFlow_smooth_eq h hZ hw ht, holoFlow_smooth_eq h hZ hw ht']
  have : w + ι (smoothDisp ι Z t w) - (w + ι (smoothDisp ι Z t' w)) =
      ι (smoothDisp ι Z t w - smoothDisp ι Z t' w) := by rw [map_sub]; abel
  rw [this]
  exact (hι _).trans (norm_smoothDisp_time_sub_le h hZ hb hw ht ht')

omit [CompleteSpace G] in
theorem norm_fderiv_smoothDisp_time_sub_le (hL : 0 ≤ M / δ) {w : F} (hw : w ∈ U) {t t' : ℝ}
    (ht : t ∈ Icc (-1 : ℝ) 1) (ht' : t' ∈ Icc (-1 : ℝ) 1) :
    ‖fderiv ℂ (smoothDisp ι Z t) w - fderiv ℂ (smoothDisp ι Z t') w‖ ≤
      M / δ * Real.exp (M / δ) * |t - t'| := by
  set φ := holoFlow (smoothField ι Z) with hφ
  set g : ℝ → F →L[ℂ] G := fun σ => (fderiv ℂ Z (φ σ w)).comp (fderiv ℂ (φ σ) w) with hg
  have hG : ContinuousOn g (Icc (-1 : ℝ) 1) :=
    ((continuousOn_fderiv_of_holomorphic h.isOpen_V hZ).comp (continuousOn_holoFlow_time h hw)
      fun σ hσ => h.mem_V_of_ball hw (holoFlow_mem_ball h hw hσ)).clm_comp
      (continuousOn_fderiv_holoFlow_time h hw)
  have e1 := (hasFDerivAt_smoothDisp h hZ hb hw ht).fderiv
  have e2 := (hasFDerivAt_smoothDisp h hZ hb hw ht').fderiv
  rw [e1, e2]
  have h1 : IntervalIntegrable g volume 0 t := (hG.mono (uIcc_subset_Icc' ht)).intervalIntegrable
  have h2 : IntervalIntegrable g volume 0 t' := (hG.mono (uIcc_subset_Icc' ht')).intervalIntegrable
  rw [integral_interval_sub_left h1 h2]
  refine norm_integral_le_of_norm_le_const fun σ hσ => ?_
  have hσ' : σ ∈ Icc (-1 : ℝ) 1 := (uIcc_subset_Icc ht' ht) (uIoc_subset_uIcc hσ)
  have hz := holoFlow_mem_ball h hw hσ'
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  have h1' : ‖fderiv ℂ Z (φ σ w)‖ ≤ M / δ :=
    norm_fderiv_le_div_of_ball_subset h.delta_pos h.M_pos.le hZ hb (h.ball_subset_V hw hz)
  have h2' := norm_fderiv_holoFlow_le h hw hσ'
  have : |σ| ≤ 1 := abs_le.mpr ⟨hσ'.1, hσ'.2⟩
  exact mul_le_mul h1' (h2'.trans (Real.exp_le_exp.mpr (by nlinarith))) (norm_nonneg _) hL

/-- The transported field at time `t`. -/
noncomputable def yfam (ι : G →L[ℂ] F) (Z : F → G) (Zg : ℝ → F → G) (t : ℝ) (w : F) : G :=
  transSolve (transNop ι Z t w) (Zg t (holoFlow (smoothField ι Z) t w))

/-- **`‖y‖ ≤ ‖u‖/(1-q)`**. -/
theorem norm_transSolve_le {N : G →L[ℂ] G} {q : ℝ} (hq : q < 1) (hN : ‖N‖ ≤ q) (u : G) :
    ‖transSolve N u‖ ≤ ‖u‖ / (1 - q) := by
  have hN1 : ‖N‖ < 1 := lt_of_le_of_lt hN hq
  have hs := transSolve_spec hN1 u
  set y := transSolve N u
  have h1 : ‖y‖ ≤ ‖u‖ + q * ‖y‖ := by
    have : y = u - N y := by rw [← hs]; abel
    calc ‖y‖ = ‖u - N y‖ := by rw [← this]
      _ ≤ ‖u‖ + ‖N y‖ := norm_sub_le _ _
      _ ≤ ‖u‖ + q * ‖y‖ := by
        have := (N.le_opNorm y).trans (mul_le_mul_of_nonneg_right hN (norm_nonneg y))
        linarith
  rw [le_div_iff₀ (by linarith)]
  nlinarith

omit [CompleteSpace F] in
theorem norm_transSolve_sub_le {N N' : G →L[ℂ] G} {q : ℝ} (hq : q < 1) (hN : ‖N‖ ≤ q)
    (hN' : ‖N'‖ ≤ q) (u u' : G) :
    ‖transSolve N u - transSolve N' u'‖ ≤
      (‖u - u'‖ + ‖N - N'‖ * ‖transSolve N u‖) / (1 - q) := by
  have hN1 : ‖N‖ < 1 := lt_of_le_of_lt hN hq
  have hN1' : ‖N'‖ < 1 := lt_of_le_of_lt hN' hq
  have hs := transSolve_spec hN1 u
  have hs' := transSolve_spec hN1' u'
  set y := transSolve N u
  set y' := transSolve N' u'
  have e : (y - y') + N' (y - y') = (u - u') - (N - N') y := by
    rw [map_sub, ContinuousLinearMap.sub_apply]
    have h1 : y + N y = u := hs
    have h2 : y' + N' y' = u' := hs'
    rw [← h1, ← h2]
    abel
  have h1 : ‖y - y'‖ ≤ ‖(u - u') - (N - N') y‖ + q * ‖y - y'‖ := by
    have : y - y' = ((u - u') - (N - N') y) - N' (y - y') := by rw [← e]; abel
    calc ‖y - y'‖ = ‖((u - u') - (N - N') y) - N' (y - y')‖ := by rw [← this]
      _ ≤ ‖(u - u') - (N - N') y‖ + ‖N' (y - y')‖ := norm_sub_le _ _
      _ ≤ ‖(u - u') - (N - N') y‖ + q * ‖y - y'‖ := by
        have := (N'.le_opNorm (y - y')).trans (mul_le_mul_of_nonneg_right hN' (norm_nonneg _))
        linarith
  have h2 : ‖(u - u') - (N - N') y‖ ≤ ‖u - u'‖ + ‖N - N'‖ * ‖y‖ :=
    (norm_sub_le _ _).trans (add_le_add_right ((N - N').le_opNorm y) _)
  rw [le_div_iff₀ (by linarith)]
  nlinarith [norm_nonneg (y - y')]

end KAM.Wave
