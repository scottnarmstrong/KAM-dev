/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.Analysis.Calculus.ParametricIntegral
public import KAM.Strip.Cauchy
public import KAM.Strip.Limits

/-!
# External facts of blueprint-N Part 4: parametric integrals, Cauchy, Weierstrass

* `bpN:p4:ext-param` (`holomorphic_parametric_integral`): a parametric integral over a compact
  set of a jointly continuous family, holomorphic in the parameter with jointly continuous
  derivative, is holomorphic in the parameter and may be differentiated under the integral.
* `bpN:p4:general-cauchy` (`general_cauchy`): the open-ball Cauchy estimate `‖DG(v)‖ ≤ M / R`.
* `bpN:p4:ext-weier` (`uniform_limit_holomorphic`): a uniform limit of holomorphic maps on an
  open set is holomorphic, and the derivatives converge uniformly on `{z | closedBall z η ⊆ U}`.
-/

@[expose] public noncomputable section

open Set Metric

namespace KAM.Weighted

open MeasureTheory

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W] [NormedSpace ℝ W]
  [IsScalarTower ℝ ℂ W] [CompleteSpace W] [FiniteDimensional ℂ W]

-- The signature keeps the instance block `[CompleteSpace W] [FiniteDimensional ℂ W]` (the
-- consumers supply it); the proof does not need it, so the unused-variable lint is silenced.
set_option linter.unusedSectionVars false in
/-- `bpN:p4:ext-param`: holomorphic dependence on a parameter (compact `Q`, e.g. a box). -/
theorem holomorphic_parametric_integral {p q : ℕ} {Q : Set (Fin p → ℝ)} (hQ : IsCompact Q)
    {U : Set (Fin q → ℂ)} (hU : IsOpen U) {G : (Fin p → ℝ) → (Fin q → ℂ) → W}
    (hG : ContinuousOn (fun y : (Fin p → ℝ) × (Fin q → ℂ) => G y.1 y.2) (Q ×ˢ U))
    (hGd : ∀ x ∈ Q, DifferentiableOn ℂ (G x) U)
    (hDG : ContinuousOn (fun y : (Fin p → ℝ) × (Fin q → ℂ) => fderiv ℂ (G y.1) y.2) (Q ×ˢ U)) :
    DifferentiableOn ℂ (fun I => ∫ x in Q, G x I) U ∧
      ∀ I ∈ U, fderiv ℂ (fun I' => ∫ x in Q, G x I') I = ∫ x in Q, fderiv ℂ (G x) I := by
  have hQm : MeasurableSet Q := hQ.isClosed.measurableSet
  have hfin : (volume.restrict Q) Set.univ < ⊤ := by
    rw [Measure.restrict_apply_univ]
    exact hQ.measure_lt_top
  -- the derivative of the integral at a point `I₀ ∈ U`
  have key : ∀ I₀ ∈ U, HasFDerivAt (fun I => ∫ x in Q, G x I)
      (∫ x in Q, fderiv ℂ (G x) I₀) I₀ := by
    intro I₀ hI₀
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU I₀ hI₀
    have hη : closedBall I₀ (ε / 2) ⊆ U :=
      (closedBall_subset_ball (by linarith)).trans hball
    have hcomp : IsCompact (Q ×ˢ closedBall I₀ (ε / 2)) := hQ.prod (isCompact_closedBall _ _)
    obtain ⟨C, hC⟩ := hcomp.exists_bound_of_continuousOn
      (hDG.mono (Set.prod_mono (Subset.refl Q) hη))
    have hsU : ball I₀ (ε / 2) ⊆ U := (ball_subset_closedBall).trans hη
    have hcontx : ∀ x ∈ ball I₀ (ε / 2), ContinuousOn (fun a => G a x) Q := fun x hx =>
      (hG.comp (continuous_id.prodMk continuous_const).continuousOn
        (fun a ha => ⟨ha, hsU hx⟩))
    refine (hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℂ) (μ := volume.restrict Q)
      (F := fun x a => G a x) (F' := fun x a => fderiv ℂ (G a) x) (bound := fun _ => C)
      (ball_mem_nhds I₀ (half_pos hε)) ?_ ?_ ?_ ?_ ?_ ?_)
    · filter_upwards [ball_mem_nhds I₀ (half_pos hε)] with x hx
      exact (hcontx x hx).aestronglyMeasurable hQm
    · exact (hcontx I₀ (mem_ball_self (half_pos hε))).integrableOn_compact hQ
    · refine ContinuousOn.aestronglyMeasurable ?_ hQm
      exact (hDG.comp (continuous_id.prodMk continuous_const).continuousOn
        (fun a ha => ⟨ha, hI₀⟩))
    · refine (ae_restrict_iff' hQm).2 (Filter.Eventually.of_forall fun a ha x hx => ?_)
      exact hC (a, x) ⟨ha, ball_subset_closedBall hx⟩
    · have : IsFiniteMeasure (volume.restrict Q) := ⟨hfin⟩
      exact integrable_const C
    · refine (ae_restrict_iff' hQm).2 (Filter.Eventually.of_forall fun a ha x hx => ?_)
      exact ((hGd a ha).differentiableAt (hU.mem_nhds (hsU hx))).hasFDerivAt
  exact ⟨fun I hI => (key I hI).differentiableAt.differentiableWithinAt,
    fun I hI => (key I hI).fderiv⟩

/-- `bpN:p4:general-cauchy` (C.1), the open-ball form: from `KAM.norm_fderiv_le_of_closedBall`
by `δ ↑ R`. -/
theorem general_cauchy {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F] {G : E → F} {v : E} {R M : ℝ}
    (hR : 0 < R) (hG : DifferentiableOn ℂ G (ball v R)) (hM : ∀ a ∈ ball v R, ‖G a‖ ≤ M) :
    ‖fderiv ℂ G v‖ ≤ M / R := by
  have h : ∀ δ : ℝ, 0 < δ → δ < R → ‖fderiv ℂ G v‖ * δ ≤ M := by
    intro δ hδ hδR
    have hsub : closedBall v δ ⊆ ball v R := closedBall_subset_ball hδR
    have := KAM.norm_fderiv_le_of_closedBall_bound isOpen_ball hG hδ hsub
      (fun w hw => hM w (hsub hw))
    rwa [le_div_iff₀ hδ] at this
  rw [le_div_iff₀ hR]
  have hlim : Filter.Tendsto (fun δ : ℝ => ‖fderiv ℂ G v‖ * δ) (nhdsWithin R (Iio R))
      (nhds (‖fderiv ℂ G v‖ * R)) :=
    ((continuous_const.mul continuous_id).tendsto R).mono_left nhdsWithin_le_nhds
  refine le_of_tendsto hlim ?_
  filter_upwards [Ioo_mem_nhdsLT hR] with δ hδ using h δ hδ.1 hδ.2

/-- `bpN:p4:ext-weier`: uniform limits of holomorphic maps; derivatives converge uniformly on
`{z | closedBall z η ⊆ U}` (by `general_cauchy` applied to `K j - K l`, then
`KAM.uniform_limits`). -/
theorem uniform_limit_holomorphic {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F] {U : Set E} (hU : IsOpen U)
    {K : ℕ → E → F} {K₀ : E → F} (hK : ∀ j, DifferentiableOn ℂ (K j) U)
    (hconv : TendstoUniformlyOn K K₀ Filter.atTop U) :
    DifferentiableOn ℂ K₀ U ∧ ∀ η : ℝ, 0 < η →
      TendstoUniformlyOn (fun j z => fderiv ℂ (K j) z) (fderiv ℂ K₀) Filter.atTop
        {z | closedBall z η ⊆ U} := by
  -- uniform Cauchy estimate for the derivatives on `{z | closedBall z η ⊆ U}`
  have hcauchy : ∀ η : ℝ, 0 < η → UniformCauchySeqOn (fun j z => fderiv ℂ (K j) z)
      Filter.atTop {z | closedBall z η ⊆ U} := by
    intro η hη
    rw [Metric.uniformCauchySeqOn_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1
      (Metric.tendstoUniformlyOn_iff.1 hconv (ε * η / 4) (by positivity))
    refine ⟨N, fun a ha b hb z hz => ?_⟩
    have hzU : ∀ w ∈ closedBall z η, w ∈ U := fun w hw => hz hw
    have hbound : ∀ w ∈ closedBall z η, ‖(K a w - K b w : F)‖ ≤ ε * η / 2 := by
      intro w hw
      have h1 := hN a ha w (hzU w hw)
      have h2 := hN b hb w (hzU w hw)
      rw [dist_eq_norm] at h1 h2
      calc ‖(K a w - K b w : F)‖ = ‖(K₀ w - K b w) - (K₀ w - K a w)‖ := by
            congr 1; abel
        _ ≤ ‖K₀ w - K b w‖ + ‖K₀ w - K a w‖ := norm_sub_le _ _
        _ ≤ ε * η / 2 := by linarith
    have hd := general_cauchy hη (((hK a).sub (hK b)).mono (ball_subset_closedBall.trans hz))
      (fun w hw => hbound w (ball_subset_closedBall hw))
    have hzU' : z ∈ U := hz (mem_closedBall_self hη.le)
    have hfd : fderiv ℂ (fun w => K a w - K b w) z = fderiv ℂ (K a) z - fderiv ℂ (K b) z :=
      fderiv_sub ((hK a).differentiableAt (hU.mem_nhds hzU'))
        ((hK b).differentiableAt (hU.mem_nhds hzU'))
    rw [dist_eq_norm, ← hfd]
    calc ‖fderiv ℂ (fun w => K a w - K b w) z‖ ≤ ε * η / 2 / η := hd
      _ < ε := by
        rw [div_lt_iff₀ hη]
        nlinarith
  -- a ball around every point of `U` lies in `U`
  have hball : ∀ z ∈ U, ∃ ε : ℝ, 0 < ε ∧ ball z ε ⊆ U := fun z hz => by
    obtain ⟨ε, hε, h⟩ := Metric.isOpen_iff.1 hU z hz
    exact ⟨ε, hε, h⟩
  -- pointwise limits of the derivatives, Cauchy in the complete space `E →L[ℂ] F`
  have hlim : ∀ z ∈ U, ∃ L : E →L[ℂ] F,
      Filter.Tendsto (fun j => fderiv ℂ (K j) z) Filter.atTop (nhds L) := by
    intro z hz
    obtain ⟨ε, hε, h⟩ := hball z hz
    have hsub : closedBall z (ε / 2) ⊆ U := (closedBall_subset_ball (by linarith)).trans h
    exact cauchySeq_tendsto_of_complete
      ((hcauchy (ε / 2) (half_pos hε)).cauchySeq (x := z) hsub)
  choose! Λ hΛ using hlim
  have hunif : ∀ η : ℝ, 0 < η → TendstoUniformlyOn (fun j z => fderiv ℂ (K j) z) Λ
      Filter.atTop {z | closedBall z η ⊆ U} := fun η hη =>
    (hcauchy η hη).tendstoUniformlyOn_of_tendsto fun z hz =>
      hΛ z (hz (mem_closedBall_self hη.le))
  -- local application of `KAM.uniform_limits` on small balls
  have hloc : ∀ z ∈ U, DifferentiableAt ℂ K₀ z ∧ fderiv ℂ K₀ z = Λ z := by
    intro z₀ hz₀
    obtain ⟨ε, hε, h⟩ := hball z₀ hz₀
    have hVU : ball z₀ (ε / 2) ⊆ U := (ball_subset_ball (by linarith)).trans h
    have hVS : ball z₀ (ε / 2) ⊆ {z | closedBall z (ε / 4) ⊆ U} := by
      intro w hw x hx
      apply h
      rw [mem_ball, dist_eq_norm]
      have h1 : ‖x - w‖ ≤ ε / 4 := by simpa [mem_closedBall, dist_eq_norm] using hx
      have h2 : ‖w - z₀‖ < ε / 2 := by simpa [mem_ball, dist_eq_norm] using hw
      calc ‖x - z₀‖ = ‖(x - w) + (w - z₀)‖ := by congr 1; abel
        _ ≤ ‖x - w‖ + ‖w - z₀‖ := norm_add_le _ _
        _ < ε := by linarith
    obtain ⟨hd, hfd⟩ := KAM.uniform_limits isOpen_ball (fun j => (hK j).mono hVU)
      (fun x hx => hconv.tendsto_at (hVU hx))
      ((hunif (ε / 4) (by linarith)).mono hVS)
    have hmem : ball z₀ (ε / 2) ∈ nhds z₀ := ball_mem_nhds z₀ (half_pos hε)
    exact ⟨(hd.differentiableAt hmem), hfd z₀ (mem_ball_self (half_pos hε))⟩
  refine ⟨fun z hz => (hloc z hz).1.differentiableWithinAt, fun η hη => ?_⟩
  refine (hunif η hη).congr_right fun z hz => ?_
  exact ((hloc z (hz (mem_closedBall_self hη.le))).2).symm

end KAM.Weighted
