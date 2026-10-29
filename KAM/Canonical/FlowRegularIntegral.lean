/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Parametric interval integrals over `[0, t]` with holomorphic dependence

Helper module of `KAM.Canonical.FlowRegular` (blueprint-N Part 5, node `bpN:p5:flow`
(b)). For a family `g : ℝ → E → G` on `[-1, 1] × U` (`U` open in a
finite-dimensional complex space `E`) that is jointly continuous, holomorphic in the second
variable, and has jointly continuous derivative, the map `(t, z) ↦ ∫ τ in 0..t, g τ z` is again
of this kind, and its `z`-derivative is the integral of the `z`-derivatives (differentiation
under the integral sign).

The integral over `[0, t]` is reduced to the fixed interval `[0, 1]` by `τ = t σ`.

* `KAM.Canonical.ParamHyp`: the three regularity conditions on `[-1, 1] × U`;
* `KAM.Canonical.ParamHyp.intervalIntegral`: stability under `∫ τ in 0..t`, with the derivative
  formula;
* `KAM.Canonical.ParamHyp.id_add`: the same for the Picard map `z + ∫ τ in 0..t, g τ z`.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory
open scoped Topology

namespace KAM.Canonical

section Param

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

/-- Rescaling `τ = t σ`: the integral over `[0, t]` is `t` times an integral over `[0, 1]`. -/
theorem intervalIntegral_eq_smul_mul {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (f : ℝ → G) (t : ℝ) :
    ∫ τ in (0 : ℝ)..t, f τ = t • ∫ σ in (0 : ℝ)..1, f (t * σ) := by
  by_cases ht : t = 0
  · simp [ht]
  · rw [intervalIntegral.integral_comp_mul_left (a := 0) (b := 1) f ht, smul_smul,
      mul_inv_cancel₀ ht, one_smul]
    simp

/-- `t σ` stays in `[-1, 1]` for `t ∈ [-1, 1]` and `σ ∈ [0, 1]`. -/
theorem mul_mem_Icc_neg_one_one {t σ : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) (hσ : σ ∈ Icc (0 : ℝ) 1) :
    t * σ ∈ Icc (-1 : ℝ) 1 := by
  constructor
  · nlinarith [mul_nonneg (by linarith [ht.1] : 0 ≤ t + 1) hσ.1, hσ.2]
  · nlinarith [mul_nonneg (by linarith [ht.2] : 0 ≤ 1 - t) hσ.1, hσ.2]

omit [NormedSpace ℂ E] [FiniteDimensional ℂ E] in
/-- A slice `σ ↦ g (t σ) z` of a family continuous on `[-1, 1] × U` is continuous on `[0, 1]`. -/
theorem continuousOn_slice {G : Type*} [TopologicalSpace G] {U : Set E} {g : ℝ → E → G}
    (hg : ContinuousOn (fun p : ℝ × E => g p.1 p.2) (Icc (-1 : ℝ) 1 ×ˢ U)) {t : ℝ}
    (ht : t ∈ Icc (-1 : ℝ) 1) {z : E} (hz : z ∈ U) :
    ContinuousOn (fun σ : ℝ => g (t * σ) z) (Icc 0 1) := by
  have h1 : Continuous (fun σ : ℝ => (t * σ, z)) :=
    (continuous_const.mul continuous_id).prodMk continuous_const
  exact hg.comp h1.continuousOn (fun σ hσ => ⟨mul_mem_Icc_neg_one_one ht hσ, hz⟩)

omit [NormedSpace ℂ E] [FiniteDimensional ℂ E] in
/-- For fixed `σ ∈ [0, 1]`, `(t, z) ↦ g (t σ) z` is continuous on `[-1, 1] × U`. -/
theorem continuousOn_scale {G : Type*} [TopologicalSpace G] {U : Set E} {g : ℝ → E → G}
    (hg : ContinuousOn (fun p : ℝ × E => g p.1 p.2) (Icc (-1 : ℝ) 1 ×ˢ U)) {σ : ℝ}
    (hσ : σ ∈ Icc (0 : ℝ) 1) :
    ContinuousOn (fun y : ℝ × E => g (y.1 * σ) y.2) (Icc (-1 : ℝ) 1 ×ˢ U) := by
  have h1 : Continuous (fun y : ℝ × E => (y.1 * σ, y.2)) :=
    (continuous_fst.mul continuous_const).prodMk continuous_snd
  exact hg.comp h1.continuousOn (fun y hy => ⟨by
    simpa [mul_comm] using mul_mem_Icc_neg_one_one hy.1 hσ, hy.2⟩)

/-- Continuity of `(t, z) ↦ ∫ σ in 0..1, g (t σ) z` on `[-1, 1] × U`. -/
theorem continuousOn_integral_mul {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {U : Set E} (hU : IsOpen U) {g : ℝ → E → G}
    (hg : ContinuousOn (fun p : ℝ × E => g p.1 p.2) (Icc (-1 : ℝ) 1 ×ˢ U)) :
    ContinuousOn (fun p : ℝ × E => ∫ σ in (0 : ℝ)..1, g (p.1 * σ) p.2) (Icc (-1 : ℝ) 1 ×ˢ U) := by
  have : ProperSpace E := FiniteDimensional.proper ℂ E
  intro x₀ hx₀
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hU x₀.2 hx₀.2
  have hcl : closedBall x₀.2 (r / 2) ⊆ U := (closedBall_subset_ball (by linarith)).trans hball
  have hK : IsCompact (Icc (-1 : ℝ) 1 ×ˢ closedBall x₀.2 (r / 2)) :=
    isCompact_Icc.prod (isCompact_closedBall _ _)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hg.mono (prod_mono subset_rfl hcl))
  refine intervalIntegral.continuousWithinAt_of_dominated_interval (bound := fun _ => C) ?_ ?_
    intervalIntegrable_const ?_
  · refine Filter.eventually_of_mem self_mem_nhdsWithin fun x hx => ?_
    rw [Set.uIoc_of_le zero_le_one]
    exact ((continuousOn_slice hg hx.1 hx.2).mono Ioc_subset_Icc_self).aestronglyMeasurable
      measurableSet_Ioc
  · have hmem : {y : ℝ × E | y.2 ∈ closedBall x₀.2 (r / 2)} ∈ 𝓝 x₀ :=
      continuous_snd.continuousAt.preimage_mem_nhds (closedBall_mem_nhds _ (half_pos hr))
    refine Filter.eventually_of_mem (inter_mem_nhdsWithin _ hmem) fun x hx => ?_
    refine Filter.Eventually.of_forall fun σ hσ => ?_
    rw [Set.uIoc_of_le zero_le_one] at hσ
    exact hC (x.1 * σ, x.2) ⟨mul_mem_Icc_neg_one_one hx.1.1 (Ioc_subset_Icc_self hσ), hx.2⟩
  · refine Filter.Eventually.of_forall fun σ hσ => ?_
    rw [Set.uIoc_of_le zero_le_one] at hσ
    exact continuousOn_scale hg (Ioc_subset_Icc_self hσ) x₀ hx₀

/-- Continuity of the integral `(t, z) ↦ ∫ τ in 0..t, g τ z` on `[-1, 1] × U`. -/
theorem continuousOn_intervalIntegral {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {U : Set E} (hU : IsOpen U) {g : ℝ → E → G}
    (hg : ContinuousOn (fun p : ℝ × E => g p.1 p.2) (Icc (-1 : ℝ) 1 ×ˢ U)) :
    ContinuousOn (fun p : ℝ × E => ∫ τ in (0 : ℝ)..p.1, g τ p.2) (Icc (-1 : ℝ) 1 ×ˢ U) := by
  have h : (fun p : ℝ × E => ∫ τ in (0 : ℝ)..p.1, g τ p.2) =
      fun p : ℝ × E => p.1 • ∫ σ in (0 : ℝ)..1, g (p.1 * σ) p.2 :=
    funext fun p => intervalIntegral_eq_smul_mul (fun τ => g τ p.2) p.1
  rw [h]
  exact continuousOn_fst.smul (continuousOn_integral_mul hU hg)

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]

/-- Differentiation under the integral sign for `z ↦ ∫ σ in 0..1, g (t σ) z`. -/
theorem hasFDerivAt_integral_mul {U : Set E} (hU : IsOpen U) {g : ℝ → E → G}
    (hg : ContinuousOn (fun p : ℝ × E => g p.1 p.2) (Icc (-1 : ℝ) 1 ×ˢ U))
    (hgd : ∀ τ ∈ Icc (-1 : ℝ) 1, DifferentiableOn ℂ (g τ) U)
    (hDg : ContinuousOn (fun p : ℝ × E => fderiv ℂ (g p.1) p.2) (Icc (-1 : ℝ) 1 ×ˢ U))
    {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) {z₀ : E} (hz₀ : z₀ ∈ U) :
    HasFDerivAt (fun z => ∫ σ in (0 : ℝ)..1, g (t * σ) z)
      (∫ σ in (0 : ℝ)..1, fderiv ℂ (g (t * σ)) z₀) z₀ := by
  have : ProperSpace E := FiniteDimensional.proper ℂ E
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hU z₀ hz₀
  have hcl : closedBall z₀ (r / 2) ⊆ U := (closedBall_subset_ball (by linarith)).trans hball
  have hsU : ball z₀ (r / 2) ⊆ U := ball_subset_closedBall.trans hcl
  have hK : IsCompact (Icc (-1 : ℝ) 1 ×ˢ closedBall z₀ (r / 2)) :=
    isCompact_Icc.prod (isCompact_closedBall _ _)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hDg.mono (prod_mono subset_rfl hcl))
  have hcontx : ∀ z ∈ U, ContinuousOn (fun σ : ℝ => g (t * σ) z) (Icc 0 1) :=
    fun z hz => continuousOn_slice hg ht hz
  have hcontD : ∀ z ∈ U, ContinuousOn (fun σ : ℝ => fderiv ℂ (g (t * σ)) z) (Icc 0 1) :=
    fun z hz => continuousOn_slice (g := fun τ z => fderiv ℂ (g τ) z) hDg ht hz
  have hfin : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) 1)) :=
    ⟨by simp⟩
  have key : HasFDerivAt (fun z => ∫ σ in Ioc (0 : ℝ) 1, g (t * σ) z)
      (∫ σ in Ioc (0 : ℝ) 1, fderiv ℂ (g (t * σ)) z₀) z₀ := by
    refine hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℂ)
      (μ := volume.restrict (Ioc (0 : ℝ) 1)) (F := fun z σ => g (t * σ) z)
      (F' := fun z σ => fderiv ℂ (g (t * σ)) z) (bound := fun _ => C)
      (ball_mem_nhds z₀ (half_pos hr)) ?_ ?_ ?_ ?_ ?_ ?_
    · filter_upwards [ball_mem_nhds z₀ (half_pos hr)] with z hz
      exact ((hcontx z (hsU hz)).mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
    · exact (hcontx z₀ hz₀).integrableOn_Icc.mono_set Ioc_subset_Icc_self
    · exact ((hcontD z₀ hz₀).mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
    · refine (ae_restrict_iff' measurableSet_Ioc).2
        (Filter.Eventually.of_forall fun σ hσ z hz => ?_)
      exact hC (t * σ, z) ⟨mul_mem_Icc_neg_one_one ht (Ioc_subset_Icc_self hσ),
        ball_subset_closedBall hz⟩
    · exact integrable_const C
    · refine (ae_restrict_iff' measurableSet_Ioc).2
        (Filter.Eventually.of_forall fun σ hσ z hz => ?_)
      exact ((hgd _ (mul_mem_Icc_neg_one_one ht (Ioc_subset_Icc_self hσ))).differentiableAt
        (hU.mem_nhds (hsU hz))).hasFDerivAt
  simpa only [intervalIntegral.integral_of_le zero_le_one] using key

/-- The regularity conditions on `[-1, 1] × U` shared by the Picard iterates and the flow: joint
continuity, holomorphy in the space variable, and joint continuity of the space derivative. -/
structure ParamHyp (U : Set E) (y : ℝ → E → G) : Prop where
  cont : ContinuousOn (fun p : ℝ × E => y p.1 p.2) (Icc (-1 : ℝ) 1 ×ˢ U)
  diff : ∀ t ∈ Icc (-1 : ℝ) 1, DifferentiableOn ℂ (y t) U
  contD : ContinuousOn (fun p : ℝ × E => fderiv ℂ (y p.1) p.2) (Icc (-1 : ℝ) 1 ×ˢ U)

/-- The integral `∫ τ in 0..t, g τ z` of a `ParamHyp` family is again one, and its space derivative
is the integral of the space derivatives. -/
theorem ParamHyp.intervalIntegral [CompleteSpace G] {U : Set E} (hU : IsOpen U) {g : ℝ → E → G}
    (hg : ParamHyp U g) :
    ParamHyp U (fun t z => ∫ τ in (0 : ℝ)..t, g τ z) ∧
    ∀ t ∈ Icc (-1 : ℝ) 1, ∀ z ∈ U, HasFDerivAt (fun w => ∫ τ in (0 : ℝ)..t, g τ w)
      (∫ τ in (0 : ℝ)..t, fderiv ℂ (g τ) z) z := by
  have hD : ∀ t ∈ Icc (-1 : ℝ) 1, ∀ z ∈ U, HasFDerivAt (fun w => ∫ τ in (0 : ℝ)..t, g τ w)
      (∫ τ in (0 : ℝ)..t, fderiv ℂ (g τ) z) z := by
    intro t ht z hz
    have h := (hasFDerivAt_integral_mul hU hg.cont hg.diff hg.contD ht hz).const_smul t
    have e1 : (fun w => ∫ τ in (0 : ℝ)..t, g τ w) =
        fun w => t • ∫ σ in (0 : ℝ)..1, g (t * σ) w :=
      funext fun w => intervalIntegral_eq_smul_mul (fun τ => g τ w) t
    have e2 : ∫ τ in (0 : ℝ)..t, fderiv ℂ (g τ) z = t • ∫ σ in (0 : ℝ)..1, fderiv ℂ (g (t * σ)) z :=
      intervalIntegral_eq_smul_mul (fun τ => fderiv ℂ (g τ) z) t
    rw [e1, e2]
    exact h
  refine ⟨⟨continuousOn_intervalIntegral hU hg.cont, fun t ht z hz =>
    (hD t ht z hz).differentiableAt.differentiableWithinAt, ?_⟩, hD⟩
  have := continuousOn_intervalIntegral hU (g := fun τ z => fderiv ℂ (g τ) z) hg.contD
  refine this.congr fun p hp => ?_
  exact (hD p.1 hp.1 p.2 hp.2).fderiv

/-- The Picard map `z + ∫ τ in 0..t, g τ z` of a `ParamHyp` family is again one, with derivative
`id + ∫ τ in 0..t, D g τ z`. -/
theorem ParamHyp.id_add [CompleteSpace E] {U : Set E} (hU : IsOpen U) {g : ℝ → E → E}
    (hg : ParamHyp U g) :
    ParamHyp U (fun t z => z + ∫ τ in (0 : ℝ)..t, g τ z) ∧
    ∀ t ∈ Icc (-1 : ℝ) 1, ∀ z ∈ U, fderiv ℂ (fun w => w + ∫ τ in (0 : ℝ)..t, g τ w) z =
      ContinuousLinearMap.id ℂ E + ∫ τ in (0 : ℝ)..t, fderiv ℂ (g τ) z := by
  obtain ⟨hI, hD⟩ := hg.intervalIntegral hU
  have hder : ∀ t ∈ Icc (-1 : ℝ) 1, ∀ z ∈ U, fderiv ℂ (fun w => w + ∫ τ in (0 : ℝ)..t, g τ w) z =
      ContinuousLinearMap.id ℂ E + ∫ τ in (0 : ℝ)..t, fderiv ℂ (g τ) z := by
    intro t ht z hz
    exact ((hasFDerivAt_id z).add (hD t ht z hz)).fderiv
  refine ⟨⟨continuousOn_snd.add hI.cont, fun t ht => differentiableOn_id.add (hI.diff t ht), ?_⟩,
    hder⟩
  have hc : ContinuousOn (fun p : ℝ × E => ContinuousLinearMap.id ℂ E +
      fderiv ℂ (fun z => ∫ τ in (0 : ℝ)..p.1, g τ z) p.2) (Icc (-1 : ℝ) 1 ×ˢ U) :=
    continuousOn_const.add hI.contD
  refine hc.congr fun p hp => ?_
  rw [hder p.1 hp.1 p.2 hp.2]
  show _ = ContinuousLinearMap.id ℂ E + fderiv ℂ (fun z => ∫ τ in (0 : ℝ)..p.1, g τ z) p.2
  rw [(hD p.1 hp.1 p.2 hp.2).fderiv]

end Param

end KAM.Canonical
