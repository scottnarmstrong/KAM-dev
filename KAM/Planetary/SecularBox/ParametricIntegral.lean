/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import KAM.Frozen.Planetary.Defs.Phase

/-!
# Smooth dependence of a compact-box integral on a parameter (P14, package S4)

`secular_parametric_integral`: if `g` is jointly `C^k` on `U ×ˢ univ` (`U` open) and `Q` is compact,
then `w ↦ ∫ F in Q, g w F` is `C^k` on `U`.  Mathlib has only the first-derivative theorem
`hasFDerivAt_integral_of_dominated_of_fderiv_le`; the finite-order statement is proved by induction
on `k`, with the continuous derivative bounded on a compact parameter neighbourhood times `Q`.
-/

@[expose] public section

open Set Metric MeasureTheory
open scoped ContDiff

namespace KAM.Planetary

universe u

set_option linter.unusedSectionVars false

section General

variable {E P H : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  [NormedAddCommGroup P] [NormedSpace ℝ P] [MeasurableSpace P] [OpensMeasurableSpace P]
  [SecondCountableTopology P]
  [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]

/-- Continuity of a compact integral in the parameter, for a jointly continuous integrand. -/
theorem sb_param_integral_continuousOn {U : Set E} (hU : IsOpen U) {Q : Set P}
    (hQ : IsCompact Q) {μ : Measure P} [IsFiniteMeasureOnCompacts μ] {G : E × P → H}
    (hG : ContinuousOn G (U ×ˢ univ)) :
    ContinuousOn (fun w => ∫ F in Q, G (w, F) ∂μ) U := by
  have hQm : MeasurableSet Q := hQ.isClosed.measurableSet
  intro w₀ hw₀
  refine ContinuousAt.continuousWithinAt ?_
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU w₀ hw₀
  have hη : closedBall w₀ (ε / 2) ⊆ U :=
    (closedBall_subset_ball (by linarith)).trans hball
  have hcomp : IsCompact (closedBall w₀ (ε / 2) ×ˢ Q) :=
    (isCompact_closedBall _ _).prod hQ
  obtain ⟨C, hC⟩ := hcomp.exists_bound_of_continuousOn
    (hG.mono (Set.prod_mono hη (Set.subset_univ Q)))
  have hsU : ball w₀ (ε / 2) ⊆ U := ball_subset_closedBall.trans hη
  have hcontx : ∀ x ∈ U, ContinuousOn (fun a => G (x, a)) Q := fun x hx =>
    hG.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun a _ => ⟨hx, mem_univ a⟩)
  have : IsFiniteMeasure (μ.restrict Q) := ⟨by
    rw [Measure.restrict_apply_univ]; exact hQ.measure_lt_top⟩
  refine continuousAt_of_dominated (bound := fun _ => C) ?_ ?_ ?_ ?_
  · filter_upwards [ball_mem_nhds w₀ (half_pos hε)] with x hx
    exact (hcontx x (hsU hx)).aestronglyMeasurable hQm
  · filter_upwards [ball_mem_nhds w₀ (half_pos hε)] with x hx
    exact (ae_restrict_iff' hQm).2 (Filter.Eventually.of_forall fun a ha =>
      hC (x, a) ⟨ball_subset_closedBall hx, ha⟩)
  · exact integrable_const C
  · refine (ae_restrict_iff' hQm).2 (Filter.Eventually.of_forall fun a ha => ?_)
    exact (hG.continuousAt ((hU.prod isOpen_univ).mem_nhds ⟨hw₀, mem_univ a⟩)).comp
      (f := fun x : E => (x, a)) (continuousAt_id.prodMk continuousAt_const)

/-- First-order differentiation under a compact integral, with the derivative in integral form. -/
theorem sb_param_integral_hasFDerivAt {U : Set E} (hU : IsOpen U) {Q : Set P}
    (hQ : IsCompact Q) {μ : Measure P} [IsFiniteMeasureOnCompacts μ] {G : E × P → H}
    (hG : ContDiffOn ℝ 1 G (U ×ˢ univ)) {w₀ : E} (hw₀ : w₀ ∈ U) :
    HasFDerivAt (fun w => ∫ F in Q, G (w, F) ∂μ)
      (∫ F in Q, (fderiv ℝ G (w₀, F)).comp (ContinuousLinearMap.inl ℝ E P) ∂μ) w₀ := by
  have hQm : MeasurableSet Q := hQ.isClosed.measurableSet
  have hUU : IsOpen (U ×ˢ (univ : Set P)) := hU.prod isOpen_univ
  have hGc : ContinuousOn G (U ×ˢ univ) := hG.continuousOn
  have hD : ContinuousOn
      (fun p : E × P => (fderiv ℝ G p).comp (ContinuousLinearMap.inl ℝ E P)) (U ×ˢ univ) :=
    ((hG.fderiv_of_isOpen hUU (m := 0) (by simp)).clm_comp contDiffOn_const).continuousOn
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU w₀ hw₀
  have hη : closedBall w₀ (ε / 2) ⊆ U :=
    (closedBall_subset_ball (by linarith)).trans hball
  have hcomp : IsCompact (closedBall w₀ (ε / 2) ×ˢ Q) :=
    (isCompact_closedBall _ _).prod hQ
  obtain ⟨C, hC⟩ := hcomp.exists_bound_of_continuousOn
    (hD.mono (Set.prod_mono hη (Set.subset_univ Q)))
  have hsU : ball w₀ (ε / 2) ⊆ U := ball_subset_closedBall.trans hη
  have hcontx : ∀ x ∈ U, ContinuousOn (fun a => G (x, a)) Q := fun x hx =>
    hGc.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun a _ => ⟨hx, mem_univ a⟩)
  have : IsFiniteMeasure (μ.restrict Q) := ⟨by
    rw [Measure.restrict_apply_univ]; exact hQ.measure_lt_top⟩
  have hder : ∀ x ∈ U, ∀ a : P, HasFDerivAt (fun x => G (x, a))
      ((fderiv ℝ G (x, a)).comp (ContinuousLinearMap.inl ℝ E P)) x := by
    intro x hx a
    have hd : DifferentiableAt ℝ G (x, a) :=
      (hG.differentiableOn one_ne_zero).differentiableAt (hUU.mem_nhds ⟨hx, mem_univ a⟩)
    exact hd.hasFDerivAt.comp x (hasFDerivAt_prodMk_left x a)
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ) (μ := μ.restrict Q)
    (F := fun x a => G (x, a))
    (F' := fun x a => (fderiv ℝ G (x, a)).comp (ContinuousLinearMap.inl ℝ E P))
    (bound := fun _ => C) (ball_mem_nhds w₀ (half_pos hε)) ?_ ?_ ?_ ?_ ?_ ?_
  · filter_upwards [ball_mem_nhds w₀ (half_pos hε)] with x hx
    exact (hcontx x (hsU hx)).aestronglyMeasurable hQm
  · exact (hcontx w₀ hw₀).integrableOn_compact hQ
  · refine ContinuousOn.aestronglyMeasurable ?_ hQm
    exact hD.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun a _ => ⟨hw₀, mem_univ a⟩)
  · refine (ae_restrict_iff' hQm).2 (Filter.Eventually.of_forall fun a ha x hx => ?_)
    exact hC (x, a) ⟨ball_subset_closedBall hx, ha⟩
  · exact integrable_const C
  · exact Filter.Eventually.of_forall fun a x hx => hder x (hsU hx) a

/-- Finite-order smoothness of a compact-box integral in the parameter. -/
theorem sb_param_integral_contDiffOn {U : Set E} (hU : IsOpen U) {Q : Set P}
    (hQ : IsCompact Q) {μ : Measure P} [IsFiniteMeasureOnCompacts μ] :
    ∀ (k : ℕ) {H : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
      {G : E × P → H}, ContDiffOn ℝ k G (U ×ˢ univ) →
      ContDiffOn ℝ k (fun w => ∫ F in Q, G (w, F) ∂μ) U := by
  intro k
  induction k with
  | zero =>
    intro H _ _ _ G hG
    exact (contDiffOn_zero.2 (sb_param_integral_continuousOn hU hQ
      (contDiffOn_zero.1 hG)))
  | succ k ih =>
    intro H _ _ _ G hG
    have hUU : IsOpen (U ×ˢ (univ : Set P)) := hU.prod isOpen_univ
    have h1 : ContDiffOn ℝ 1 G (U ×ˢ univ) := hG.of_le (by exact_mod_cast Nat.le_add_left 1 k)
    have hD : ContDiffOn ℝ k
        (fun p : E × P => (fderiv ℝ G p).comp (ContinuousLinearMap.inl ℝ E P)) (U ×ˢ univ) :=
      (hG.fderiv_of_isOpen hUU (m := k) (by push_cast; exact le_rfl)).clm_comp contDiffOn_const
    have hderiv : ∀ w ∈ U, HasFDerivAt (fun w => ∫ F in Q, G (w, F) ∂μ)
        (∫ F in Q, (fderiv ℝ G (w, F)).comp (ContinuousLinearMap.inl ℝ E P) ∂μ) w :=
      fun w hw => sb_param_integral_hasFDerivAt hU hQ h1 hw
    have hdiff : DifferentiableOn ℝ (fun w => ∫ F in Q, G (w, F) ∂μ) U :=
      fun w hw => (hderiv w hw).differentiableAt.differentiableWithinAt
    have hcast : ((k + 1 : ℕ) : WithTop ℕ∞) = (k : WithTop ℕ∞) + 1 := by push_cast; rfl
    rw [hcast, contDiffOn_succ_iff_fderiv_of_isOpen hU]
    refine ⟨hdiff, by simp, ?_⟩
    have := ih (G := fun p : E × P => (fderiv ℝ G p).comp (ContinuousLinearMap.inl ℝ E P)) hD
    exact this.congr fun w hw => (hderiv w hw).fderiv

end General

/-- Real compact parameter integral; owns p8:e-diff's required instance here. -/
theorem secular_parametric_integral {d q : ℕ} {U : Set (Phase d)} (hU : IsOpen U)
    {Q : Set (Fin q → ℝ)} (hQ : IsCompact Q) {g : Phase d → (Fin q → ℝ) → ℝ}
    (k : ℕ) (hg : ContDiffOn ℝ k (fun p : Phase d × (Fin q → ℝ) => g p.1 p.2)
      (U ×ˢ univ)) :
    ContDiffOn ℝ k (fun w => ∫ F in Q, g w F) U :=
  sb_param_integral_contDiffOn (μ := volume) hU hQ k hg

end KAM.Planetary
