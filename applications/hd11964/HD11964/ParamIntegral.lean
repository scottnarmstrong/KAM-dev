/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib

/-!
# Smooth parametric interval integrals (HD11964-CHI, piece 0)

Mathlib differentiates under the integral sign once
(`intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le`); this file iterates it.

* `continuousOn_intervalIntegral`: if `(x, t) ↦ G x t` is continuous on `U × ℝ`, `U` open in a
  finite-dimensional space, then `x ↦ ∫_a^b G x t dt` is continuous on `U`.
* `hasFDerivAt_intervalIntegral`: if it is `C¹` there, the derivative is the integral of the
  partial derivative `(∂_{(x,t)} G).comp inl`.
* `contDiffOn_intervalIntegral`: if it is `C^∞` there, so is `x ↦ ∫_a^b G x t dt` (induction on
  the order; the domination comes from compactness of `closedBall × [a, b]`).
-/

@[expose] public noncomputable section

open Set Filter Topology MeasureTheory Metric
open scoped ContDiff

namespace HD11964.Cover

variable {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]

/-- A function continuous on `U × ℝ` is bounded on `closedBall x₀ ε × [a, b]` for a small closed
ball inside `U`. -/
theorem exists_closedBall_bound {E : Type} [NormedAddCommGroup E] {U : Set H} (hU : IsOpen U)
    {f : H × ℝ → E} (hf : ContinuousOn f (U ×ˢ univ)) {x₀ : H} (hx₀ : x₀ ∈ U) (a b : ℝ) :
    ∃ ε > 0, closedBall x₀ ε ⊆ U ∧ ∃ C, ∀ x ∈ closedBall x₀ ε, ∀ t ∈ uIcc a b, ‖f (x, t)‖ ≤ C := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU x₀ hx₀
  have hsub : closedBall x₀ (ε / 2) ⊆ U :=
    (closedBall_subset_ball (by linarith)).trans hball
  refine ⟨ε / 2, by positivity, hsub, ?_⟩
  have hK : IsCompact (closedBall x₀ (ε / 2) ×ˢ uIcc a b) :=
    (isCompact_closedBall _ _).prod isCompact_uIcc
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hf.mono (prod_mono hsub (subset_univ _)))
  exact ⟨C, fun x hx t ht => hC (x, t) ⟨hx, ht⟩⟩

omit [NormedSpace ℝ H] [FiniteDimensional ℝ H] in
/-- The slices of a function continuous on `U × ℝ` are continuous. -/
theorem continuous_slice {E : Type} [NormedAddCommGroup E] {U : Set H} {G : H → ℝ → E}
    (hG : ContinuousOn (fun p : H × ℝ => G p.1 p.2) (U ×ˢ univ)) {x : H} (hx : x ∈ U) :
    Continuous fun t => G x t :=
  hG.comp_continuous (continuous_const.prodMk continuous_id) fun _ => ⟨hx, mem_univ _⟩

/-- **Continuity of a parametric interval integral.** -/
theorem continuousOn_intervalIntegral {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set H} (hU : IsOpen U) {G : H → ℝ → E}
    (hG : ContinuousOn (fun p : H × ℝ => G p.1 p.2) (U ×ˢ univ)) (a b : ℝ) :
    ContinuousOn (fun x => ∫ t in a..b, G x t) U := by
  intro x₀ hx₀
  obtain ⟨ε, hε, hsub, C, hC⟩ := exists_closedBall_bound hU hG hx₀ a b
  have hnhds : closedBall x₀ ε ∈ 𝓝 x₀ := closedBall_mem_nhds x₀ hε
  refine (intervalIntegral.continuousAt_of_dominated_interval (bound := fun _ => C) ?_ ?_ ?_ ?_)
    |>.continuousWithinAt
  · filter_upwards [hnhds] with x hx
    exact (continuous_slice hG (hsub hx)).aestronglyMeasurable
  · filter_upwards [hnhds] with x hx
    exact Eventually.of_forall fun t ht => hC x hx t (uIoc_subset_uIcc ht)
  · exact intervalIntegrable_const
  · refine Eventually.of_forall fun t _ => ?_
    have hc : ContinuousAt (fun p : H × ℝ => G p.1 p.2) (x₀, t) :=
      hG.continuousAt ((hU.prod isOpen_univ).mem_nhds ⟨hx₀, mem_univ t⟩)
    exact ContinuousAt.comp (f := fun x : H => (x, t)) (x := x₀) hc
      (continuous_id.prodMk continuous_const).continuousAt

/-- **The derivative of a parametric interval integral** of a `C¹` integrand. -/
theorem hasFDerivAt_intervalIntegral {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {U : Set H} (hU : IsOpen U) {G : H → ℝ → E}
    (hG : ContDiffOn ℝ 1 (fun p : H × ℝ => G p.1 p.2) (U ×ˢ univ)) (a b : ℝ) {x₀ : H}
    (hx₀ : x₀ ∈ U) :
    HasFDerivAt (fun x => ∫ t in a..b, G x t)
      (∫ t in a..b, (fderiv ℝ (fun p : H × ℝ => G p.1 p.2) (x₀, t)).comp
        (ContinuousLinearMap.inl ℝ H ℝ)) x₀ := by
  have hopen : IsOpen (U ×ˢ (univ : Set ℝ)) := hU.prod isOpen_univ
  have hDc : ContinuousOn (fun p : H × ℝ => (fderiv ℝ (fun q : H × ℝ => G q.1 q.2) p).comp
      (ContinuousLinearMap.inl ℝ H ℝ)) (U ×ˢ univ) :=
    (hG.continuousOn_fderiv_of_isOpen hopen le_rfl).clm_comp continuousOn_const
  obtain ⟨ε, hε, hsub, C, hC⟩ := exists_closedBall_bound hU hDc hx₀ a b
  have hnhds : closedBall x₀ ε ∈ 𝓝 x₀ := closedBall_mem_nhds x₀ hε
  refine intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ) (μ := volume)
    (F := fun x t => G x t)
    (F' := fun x t => (fderiv ℝ (fun p : H × ℝ => G p.1 p.2) (x, t)).comp
      (ContinuousLinearMap.inl ℝ H ℝ))
    (bound := fun _ => C) hnhds ?_ ?_ ?_ ?_ intervalIntegrable_const ?_
  · filter_upwards [hnhds] with x hx
    exact (continuous_slice hG.continuousOn (hsub hx)).aestronglyMeasurable
  · exact (continuous_slice hG.continuousOn hx₀).intervalIntegrable _ _
  · exact (continuous_slice (G := fun x t => (fderiv ℝ (fun q : H × ℝ => G q.1 q.2) (x, t)).comp
      (ContinuousLinearMap.inl ℝ H ℝ)) hDc hx₀).aestronglyMeasurable
  · exact Eventually.of_forall fun t ht x hx => hC x hx t (uIoc_subset_uIcc ht)
  · refine Eventually.of_forall fun t _ x hx => ?_
    have hd : DifferentiableAt ℝ (fun p : H × ℝ => G p.1 p.2) (x, t) :=
      (hG.differentiableOn one_ne_zero).differentiableAt (hopen.mem_nhds ⟨hsub hx, mem_univ t⟩)
    exact hd.hasFDerivAt.comp x (hasFDerivAt_prodMk_left (𝕜 := ℝ) x t)

/-- `C^n` parametric interval integrals, by induction on `n`. -/
theorem contDiffOn_intervalIntegral_nat (n : ℕ) :
    ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {U : Set H},
      IsOpen U → ∀ {G : H → ℝ → E}, ContDiffOn ℝ n (fun p : H × ℝ => G p.1 p.2) (U ×ˢ univ) →
      ∀ a b : ℝ, ContDiffOn ℝ n (fun x => ∫ t in a..b, G x t) U := by
  induction n with
  | zero =>
    intro E _ _ _ U hU G hG a b
    exact contDiffOn_zero.mpr (continuousOn_intervalIntegral hU hG.continuousOn a b)
  | succ n ih =>
    intro E _ _ _ U hU G hG a b
    have h1 : ContDiffOn ℝ 1 (fun p : H × ℝ => G p.1 p.2) (U ×ˢ univ) :=
      hG.of_le (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n))
    rw [show ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 by norm_cast,
      contDiffOn_succ_iff_fderiv_of_isOpen hU]
    refine ⟨fun x hx => (hasFDerivAt_intervalIntegral hU h1 a b hx).differentiableAt
      |>.differentiableWithinAt, fun h => by simp at h, ?_⟩
    have hD : ContDiffOn ℝ n (fun p : H × ℝ => (fderiv ℝ (fun q : H × ℝ => G q.1 q.2) p).comp
        (ContinuousLinearMap.inl ℝ H ℝ)) (U ×ˢ univ) :=
      (hG.fderiv_of_isOpen (hU.prod isOpen_univ) (by push_cast; exact le_rfl)).clm_comp
        contDiffOn_const
    refine (ih (E := H →L[ℝ] E) hU
      (G := fun x t => (fderiv ℝ (fun q : H × ℝ => G q.1 q.2) (x, t)).comp
        (ContinuousLinearMap.inl ℝ H ℝ)) hD a b).congr fun x hx => ?_
    exact (hasFDerivAt_intervalIntegral hU h1 a b hx).fderiv

/-- **`C^∞` parametric interval integrals.** -/
theorem contDiffOn_intervalIntegral {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {U : Set H} (hU : IsOpen U) {G : H → ℝ → E}
    (hG : ContDiffOn ℝ ∞ (fun p : H × ℝ => G p.1 p.2) (U ×ˢ univ)) (a b : ℝ) :
    ContDiffOn ℝ ∞ (fun x => ∫ t in a..b, G x t) U :=
  contDiffOn_infty.mpr fun n =>
    contDiffOn_intervalIntegral_nat n hU (hG.of_le (by exact_mod_cast le_top)) a b

end HD11964.Cover

end
