/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Strip.Cauchy
public import KAM.Strip.Regularity

/-!
# P Part 5: continuity of derivatives of a holomorphic family in a real parameter

If `F μ` is holomorphic on an open `U` for every `μ` in a compact `T` and `(μ, z) ↦ F μ z` is
continuous on `T × U`, then every iterated derivative `(μ, z) ↦ iteratedFDeriv ℂ n (F μ) z` is
continuous on `T × U` (Cauchy estimate on the difference `F μ - F μ₀`, then induction).
Design `docs/tracks/P/design/P45-LEAN-DESIGN.md`, package P5-JET.
-/

@[expose] public noncomputable section

open Set Metric Filter Topology
open scoped ContDiff

namespace KAM.Planetary

variable {E W : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]

theorem continuousOn_fderiv_family {T : Set ℝ} (hT : IsCompact T) {U : Set E} (hU : IsOpen U)
    {F : ℝ → E → W} (hd : ∀ μ ∈ T, DifferentiableOn ℂ (F μ) U)
    (hc : ContinuousOn (fun p : ℝ × E => F p.1 p.2) (T ×ˢ U)) :
    ContinuousOn (fun p : ℝ × E => fderiv ℂ (F p.1) p.2) (T ×ˢ U) := by
  have : ProperSpace E := FiniteDimensional.proper ℂ E
  rintro ⟨μ0, z0⟩ ⟨hμ0, hz0⟩
  obtain ⟨e0, he0, hball⟩ := Metric.isOpen_iff.1 hU z0 hz0
  set η : ℝ := e0 / 4 with hη
  have hηpos : 0 < η := by positivity
  have hcl : closedBall z0 (2 * η) ⊆ U :=
    (closedBall_subset_ball (by rw [hη]; linarith)).trans hball
  have hK : IsCompact (T ×ˢ closedBall z0 (2 * η)) := hT.prod (isCompact_closedBall _ _)
  have huc := hK.uniformContinuousOn_of_continuous (hc.mono (prod_mono (Subset.refl T) hcl))
  have hfd0 : ContinuousOn (fderiv ℂ (F μ0)) U :=
    (KAM.differentiableOn_fderiv_of_isOpen hU (hd μ0 hμ0)).continuousOn
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  obtain ⟨δ2, hδ2, h2⟩ := Metric.continuousWithinAt_iff.1 (hfd0 z0 hz0) (ε / 2) (by positivity)
  obtain ⟨δ1, hδ1, h1⟩ := Metric.uniformContinuousOn_iff.1 huc (ε * η / 4) (by positivity)
  refine ⟨min (min δ1 δ2) η, by positivity, ?_⟩
  rintro ⟨μ, z⟩ ⟨hμ, hzU⟩ hdist
  rw [Prod.dist_eq, max_lt_iff] at hdist
  obtain ⟨hdμ, hdz⟩ := hdist
  have hdμ1 : dist μ μ0 < δ1 :=
    hdμ.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hdz2 : dist z z0 < δ2 := hdz.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hdzη : dist z z0 < η := hdz.trans_le (min_le_right _ _)
  have hsub : closedBall z η ⊆ closedBall z0 (2 * η) := by
    intro w hw
    rw [mem_closedBall] at hw ⊢
    have := dist_triangle w z z0
    linarith
  have hDd : DifferentiableOn ℂ (fun w => F μ w - F μ0 w) U := (hd μ hμ).sub (hd μ0 hμ0)
  have hA : ∀ w ∈ closedBall z η, ‖F μ w - F μ0 w‖ ≤ ε * η / 4 := by
    intro w hw
    have hwK : (μ, w) ∈ T ×ˢ closedBall z0 (2 * η) := ⟨hμ, hsub hw⟩
    have hwK0 : (μ0, w) ∈ T ×ˢ closedBall z0 (2 * η) := ⟨hμ0, hsub hw⟩
    have := h1 _ hwK _ hwK0 (by rw [Prod.dist_eq]; simpa using hdμ1)
    rw [dist_eq_norm] at this
    exact this.le
  have hz' : z ∈ U := hzU
  have hb := KAM.norm_fderiv_le_of_closedBall_bound hU hDd hηpos (hsub.trans hcl) hA
  have hq : ε * η / 4 / η = ε / 4 := by field_simp
  rw [hq] at hb
  have hfs : fderiv ℂ (fun w => F μ w - F μ0 w) z = fderiv ℂ (F μ) z - fderiv ℂ (F μ0) z :=
    fderiv_sub ((hd μ hμ).differentiableAt (hU.mem_nhds hz'))
      ((hd μ0 hμ0).differentiableAt (hU.mem_nhds hz'))
  rw [hfs] at hb
  have hh2 := h2 hzU hdz2
  show dist (fderiv ℂ (F μ) z) (fderiv ℂ (F μ0) z0) < ε
  calc dist (fderiv ℂ (F μ) z) (fderiv ℂ (F μ0) z0)
      ≤ dist (fderiv ℂ (F μ) z) (fderiv ℂ (F μ0) z) +
        dist (fderiv ℂ (F μ0) z) (fderiv ℂ (F μ0) z0) := dist_triangle _ _ _
    _ < ε := by
      rw [dist_eq_norm]
      linarith

/-- Every iterated derivative of a holomorphic family is jointly continuous. -/
theorem continuousOn_iteratedFDeriv_family {T : Set ℝ} (hT : IsCompact T) {U : Set E}
    (hU : IsOpen U) :
    ∀ (n : ℕ) {F : ℝ → E → ℂ}, (∀ μ ∈ T, DifferentiableOn ℂ (F μ) U) →
      ContinuousOn (fun p : ℝ × E => F p.1 p.2) (T ×ˢ U) →
      ∀ m : Fin n → E,
        ContinuousOn (fun p : ℝ × E => iteratedFDeriv ℂ n (F p.1) p.2 m) (T ×ˢ U)
  | 0, F, _, hc, m => by
    have : ∀ p : ℝ × E, iteratedFDeriv ℂ 0 (F p.1) p.2 m = F p.1 p.2 := fun p => by
      rw [iteratedFDeriv_zero_apply]
    simp only [this]
    exact hc
  | n + 1, F, hd, hc, m => by
    set u : E := m (Fin.last n) with hu
    have hFd : ∀ μ ∈ T, DifferentiableOn ℂ (fun z => fderiv ℂ (F μ) z u) U := fun μ hμ =>
      (KAM.differentiableOn_fderiv_of_isOpen hU (hd μ hμ)).clm_apply
        (differentiableOn_const u)
    have hFc : ContinuousOn (fun p : ℝ × E => fderiv ℂ (F p.1) p.2 u) (T ×ˢ U) :=
      ((continuousOn_fderiv_family hT hU hd hc).clm_apply continuousOn_const)
    have := continuousOn_iteratedFDeriv_family hT hU n
      (F := fun μ z => fderiv ℂ (F μ) z u) hFd hFc (Fin.init m)
    refine this.congr fun p hp => ?_
    have hcd : ContDiffOn ℂ ∞ (F p.1) U :=
      KAM.contDiffOn_infty_of_differentiableOn hU (hd _ hp.1)
    have hcd' : ContDiffOn ℂ ∞ (fderiv ℂ (F p.1)) U := hcd.fderiv_of_isOpen hU (by simp)
    have hat : ContDiffAt ℂ (n : ℕ∞) (fderiv ℂ (F p.1)) p.2 :=
      (hcd'.contDiffAt (hU.mem_nhds hp.2)).of_le (by exact_mod_cast le_top)
    have h := (ContinuousLinearMap.apply ℂ ℂ u).iteratedFDeriv_comp_left hat (le_refl _)
    have h' := congrArg (fun L => L (Fin.init m)) h
    simp only [ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply,
      ContinuousLinearMap.apply_apply] at h'
    rw [iteratedFDeriv_succ_apply_right]
    exact h'.symm

end KAM.Planetary

end
