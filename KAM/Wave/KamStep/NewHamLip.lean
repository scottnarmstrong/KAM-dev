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

omit h hZ hb in
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

omit [CompleteSpace F] h hZ hb in
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

/-- **The transported field is Lipschitz in time** (uniformly in `w`); the family `Zg` is only
controlled on an open set `V₂ ⊆ V` containing the trajectory of `w` and the balls `B(z, δ)` of its
points. -/
theorem norm_yfam_time_sub_le (hι : ∀ g, ‖ι g‖ ≤ ‖g‖) (hL : 0 ≤ M / δ) {Zg : ℝ → F → G}
    {V₂ : Set F} (hV₂ : IsOpen V₂) {δ₂ : ℝ} (hδ₂ : 0 < δ₂) (hMδ₂ : M < δ₂)
    {q Y0 Lt : ℝ} (hq : q < 1) (hY0 : 0 ≤ Y0) (hLt : 0 ≤ Lt)
    (hZg : ∀ t ∈ Icc (0 : ℝ) 1, DifferentiableOn ℂ (Zg t) V₂)
    (hZgb : ∀ t ∈ Icc (0 : ℝ) 1, ∀ z ∈ V₂, ‖Zg t z‖ ≤ Y0)
    (hZgt : ∀ t ∈ Icc (0 : ℝ) 1, ∀ t' ∈ Icc (0 : ℝ) 1, ∀ z ∈ V₂,
      ‖Zg t z - Zg t' z‖ ≤ Lt * |t - t'|)
    {w : F} (hw : w ∈ U) (hballV₂ : ∀ z ∈ ball w δ₂, ball z δ₂ ⊆ V₂)
    (hN : ∀ t ∈ Icc (0 : ℝ) 1, ‖transNop ι Z t w‖ ≤ q)
    {t t' : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (ht' : t' ∈ Icc (0 : ℝ) 1) :
    ‖yfam ι Z Zg t w - yfam ι Z Zg t' w‖ ≤
      ((Y0 / δ₂ * M + Lt) + M / δ * Real.exp (M / δ) * (Y0 / (1 - q))) / (1 - q) * |t - t'| := by
  have htI : t ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [ht.1], ht.2⟩
  have htI' : t' ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [ht'.1], ht'.2⟩
  have hδ := h.delta_pos
  set φ := holoFlow (smoothField ι Z) with hφ
  have hflow := norm_flow_time_sub_le h hZ hb hι hw htI htI'
  have hbt : φ t w ∈ ball w δ₂ := by
    rw [mem_ball_iff_norm]
    refine lt_of_le_of_lt (norm_holoFlow_sub_le h hw htI) ?_
    have : |t| ≤ 1 := abs_le.mpr ⟨htI.1, htI.2⟩
    nlinarith [h.M_pos]
  have hbt' : φ t' w ∈ ball w δ₂ := by
    rw [mem_ball_iff_norm]
    refine lt_of_le_of_lt (norm_holoFlow_sub_le h hw htI') ?_
    have : |t'| ≤ 1 := abs_le.mpr ⟨htI'.1, htI'.2⟩
    nlinarith [h.M_pos]
  have hmemt : φ t w ∈ V₂ := hballV₂ _ hbt (mem_ball_self hδ₂)
  have hmemt' : φ t' w ∈ V₂ := hballV₂ _ hbt' (mem_ball_self hδ₂)
  have hlip : ∀ x ∈ ball w δ₂, ∀ y ∈ ball w δ₂, ‖Zg t x - Zg t y‖ ≤ Y0 / δ₂ * ‖x - y‖ :=
    lipschitz_of_margin hδ₂ hY0 hV₂ (hZg t ht) (hZgb t ht) (convex_ball w δ₂) hballV₂
  have hu : ‖Zg t (φ t w) - Zg t' (φ t' w)‖ ≤ (Y0 / δ₂ * M + Lt) * |t - t'| := by
    calc ‖Zg t (φ t w) - Zg t' (φ t' w)‖
        = ‖(Zg t (φ t w) - Zg t (φ t' w)) + (Zg t (φ t' w) - Zg t' (φ t' w))‖ := by
          congr 1; abel
      _ ≤ ‖Zg t (φ t w) - Zg t (φ t' w)‖ + ‖Zg t (φ t' w) - Zg t' (φ t' w)‖ := norm_add_le _ _
      _ ≤ Y0 / δ₂ * ‖φ t w - φ t' w‖ + Lt * |t - t'| := by
          refine add_le_add (hlip _ hbt _ hbt') (hZgt t ht t' ht' _ hmemt')
      _ ≤ Y0 / δ₂ * (M * |t - t'|) + Lt * |t - t'| := by
          gcongr
      _ = (Y0 / δ₂ * M + Lt) * |t - t'| := by ring
  have hNd : ‖transNop ι Z t w - transNop ι Z t' w‖ ≤ M / δ * Real.exp (M / δ) * |t - t'| := by
    have h1 := norm_fderiv_smoothDisp_time_sub_le h hZ hb hL hw htI htI'
    have hιn : ‖ι‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun g => by
      simpa using hι g
    unfold transNop
    rw [← ContinuousLinearMap.sub_comp]
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    calc _ ≤ (M / δ * Real.exp (M / δ) * |t - t'|) * ‖ι‖ :=
          mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
      _ ≤ (M / δ * Real.exp (M / δ) * |t - t'|) * 1 :=
          mul_le_mul_of_nonneg_left hιn (by positivity)
      _ = _ := mul_one _
  have hyb : ‖transSolve (transNop ι Z t w) (Zg t (φ t w))‖ ≤ Y0 / (1 - q) :=
    (norm_transSolve_le hq (hN t ht) _).trans
      (div_le_div_of_nonneg_right (hZgb t ht _ hmemt) (by linarith))
  have h := norm_transSolve_sub_le hq (hN t ht) (hN t' ht') (Zg t (φ t w)) (Zg t' (φ t' w))
  unfold yfam
  refine h.trans ?_
  rw [div_mul_eq_mul_div]
  refine div_le_div_of_nonneg_right ?_ (by linarith)
  have hprod : ‖transNop ι Z t w - transNop ι Z t' w‖ *
      ‖(transSolve (transNop ι Z t w)) (Zg t (φ t w))‖ ≤
      (M / δ * Real.exp (M / δ) * |t - t'|) * (Y0 / (1 - q)) :=
    mul_le_mul hNd hyb (norm_nonneg _) (by positivity)
  nlinarith

end KAM.Wave
