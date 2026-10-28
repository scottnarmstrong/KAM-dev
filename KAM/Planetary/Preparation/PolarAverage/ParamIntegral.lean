/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Strip.Regularity

/-!
# Holomorphic dependence of a parameter integral (P11A-P6 helper)

If `f : E × A → ℂ` is holomorphic on an open set `W`, `γ : α → A` is continuous, and `K ⊆ α` is
compact with `(q, γ a) ∈ W` for all `q` in an open set `U` and `a ∈ K`, then
`q ↦ ∫ a in K, f (q, γ a)` is holomorphic on `U`.

Differentiation under the integral sign uses the Cauchy-type bound on the derivative: `fderiv f`
is continuous (holomorphy implies smoothness in finite dimension), hence bounded on the compact
set `closedBall q₀ ε × γ(K)`.
-/

@[expose] public section

open Set MeasureTheory Metric Filter
open scoped Topology

namespace KAM.Planetary

/-- `q ↦ ∫ a in K, f (q, γ a)` is holomorphic on `U`. -/
theorem p11_differentiableOn_paramIntegral
    {E A α : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup A] [NormedSpace ℂ A] [FiniteDimensional ℂ A]
    [MeasurableSpace A] [BorelSpace A]
    [MeasurableSpace α] [TopologicalSpace α] [OpensMeasurableSpace α] [T2Space α]
    {μ : Measure α} [IsLocallyFiniteMeasure μ] {K : Set α} (hK : IsCompact K)
    {γ : α → A} (hγ : Continuous γ) {U : Set E} (hU : IsOpen U)
    {W : Set (E × A)} (hW : IsOpen W) {f : E × A → ℂ} (hf : DifferentiableOn ℂ f W)
    (hmem : ∀ q ∈ U, ∀ a ∈ K, (q, γ a) ∈ W) :
    DifferentiableOn ℂ (fun q => ∫ a in K, f (q, γ a) ∂μ) U := by
  intro q₀ hq₀
  have : ProperSpace E := FiniteDimensional.proper_rclike ℂ E
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU q₀ hq₀
  have hε2 : closedBall q₀ (ε / 2) ⊆ U := (closedBall_subset_ball (by linarith)).trans hεU
  have hKm : MeasurableSet K := hK.measurableSet
  have hfc : Continuous fun p : E × α => (p.1, γ p.2) := by fun_prop
  have hS : IsCompact ((fun p : E × α => (p.1, γ p.2)) '' (closedBall q₀ (ε / 2) ×ˢ K)) :=
    ((isCompact_closedBall q₀ (ε / 2)).prod hK).image hfc
  have hSW : ((fun p : E × α => (p.1, γ p.2)) '' (closedBall q₀ (ε / 2) ×ˢ K)) ⊆ W := by
    rintro _ ⟨⟨q, a⟩, ⟨hq, ha⟩, rfl⟩
    exact hmem q (hε2 hq) a ha
  have hfd : ContinuousOn (fderiv ℂ f) W :=
    (KAM.differentiableOn_fderiv_of_isOpen hW hf).continuousOn
  obtain ⟨C, hC⟩ := (hS.image_of_continuousOn (hfd.mono hSW)).isBounded.exists_norm_le
  let F : E → α → ℂ := fun q a => f (q, γ a)
  let L : E →L[ℂ] E × A := ContinuousLinearMap.inl ℂ E A
  let F' : E → α → E →L[ℂ] ℂ := fun q a => (fderiv ℂ f (q, γ a)).comp L
  have hFcont : ∀ q ∈ U, ContinuousOn (F q) K := by
    intro q hq
    refine hf.continuousOn.comp (by fun_prop) ?_
    intro a ha
    exact hmem q hq a ha
  have hLn : ‖L‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
    simp [L]
  have hF'b : ∀ q ∈ ball q₀ (ε / 2), ∀ a ∈ K, ‖F' q a‖ ≤ C := by
    intro q hq a ha
    have hmemS : fderiv ℂ f (q, γ a) ∈
        (fderiv ℂ f) '' ((fun p : E × α => (p.1, γ p.2)) '' (closedBall q₀ (ε / 2) ×ˢ K)) :=
      ⟨_, ⟨(q, a), ⟨ball_subset_closedBall hq, ha⟩, rfl⟩, rfl⟩
    have h1 := hC _ hmemS
    calc ‖F' q a‖ ≤ ‖fderiv ℂ f (q, γ a)‖ * ‖L‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ C * 1 := by
        have hC0 : 0 ≤ C := (norm_nonneg _).trans h1
        gcongr
      _ = C := mul_one _
  have hint : HasFDerivAt (fun q => ∫ a, F q a ∂(μ.restrict K))
      (∫ a, F' q₀ a ∂(μ.restrict K)) q₀ := by
    have : IsFiniteMeasure (μ.restrict K) := ⟨by simpa using hK.measure_lt_top⟩
    refine hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℂ) (s := ball q₀ (ε / 2))
      (bound := fun _ => C) (ball_mem_nhds q₀ (half_pos hε)) ?_ ?_ ?_ ?_ ?_ ?_
    · filter_upwards [ball_mem_nhds q₀ (half_pos hε)] with q hq
      exact (hFcont q (hεU (ball_subset_ball (half_le_self hε.le) hq))).aestronglyMeasurable hKm
    · exact (hFcont q₀ hq₀).integrableOn_compact hK
    · refine Measurable.aestronglyMeasurable ?_
      have h1 : Measurable fun a : α => (q₀, γ a) := by fun_prop
      have h2 := (measurable_fderiv ℂ f).comp h1
      exact (ContinuousLinearMap.precomp ℂ L).continuous.measurable.comp h2
    · exact ae_restrict_of_forall_mem hKm fun a ha q hq => hF'b q hq a ha
    · exact integrable_const C
    · refine ae_restrict_of_forall_mem hKm fun a ha q hq => ?_
      have hqU : q ∈ U := hε2 (ball_subset_closedBall hq)
      have hd : HasFDerivAt f (fderiv ℂ f (q, γ a)) (q, γ a) :=
        (hf.differentiableAt (hW.mem_nhds (hmem q hqU a ha))).hasFDerivAt
      exact hd.comp q ((hasFDerivAt_id q).prodMk (hasFDerivAt_const (γ a) q))
        |>.congr_fderiv (by ext v; simp [F', L])
  exact hint.differentiableAt.differentiableWithinAt

end KAM.Planetary
