/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Weighted.Parametric
public import KAM.Planetary.PlanarTorsion.RealFlow.PicardComplex

/-!
# Planar quartic torsion: Picard data from a holomorphic map (package R2)

Blueprint P, Part 11b (`bpP:p11b:e-ode`, package R2).  A map `F : ℂⁿ → ℂⁿ` holomorphic on a ball
`B(c, R)` is bounded and Lipschitz on `B(c, R / 2)` (Cauchy estimates,
`KAM.Weighted.general_cauchy`), so `P11cPicardData` holds for suitable `M, L, T, r`.
-/

@[expose] public noncomputable section

open Set Metric

namespace KAM.Planetary

variable {n : ℕ}

theorem p11c_picardData_exists {F : (Fin n → ℂ) → Fin n → ℂ} {c : Fin n → ℂ} {R : ℝ}
    (hR : 0 < R) (hF : DifferentiableOn ℂ F (ball c R)) :
    ∃ M L T r : ℝ, 0 < T ∧ 0 < r ∧ P11cPicardData F c (R / 2) M L T r := by
  obtain ⟨M₀, hM₀⟩ := (isCompact_closedBall c (3 * R / 4)).exists_bound_of_continuousOn
    (hF.continuousOn.mono (closedBall_subset_ball (by linarith)))
  set M := max M₀ 0 with hM
  have hM0 : 0 ≤ M := le_max_right _ _
  have hb : ∀ z ∈ ball c (3 * R / 4), ‖F z‖ ≤ M := fun z hz =>
    (hM₀ z (ball_subset_closedBall hz)).trans (le_max_left _ _)
  set L := M / (R / 4) with hL
  have hL0 : 0 ≤ L := div_nonneg hM0 (by positivity)
  have hder : ∀ a ∈ ball c (R / 2), ‖fderiv ℂ F a‖ ≤ L := by
    intro a ha
    have hsub : ball a (R / 4) ⊆ ball c (3 * R / 4) := by
      intro z hz
      rw [mem_ball_iff_norm] at hz ha ⊢
      have : ‖z - c‖ ≤ ‖z - a‖ + ‖a - c‖ := by
        calc ‖z - c‖ = ‖(z - a) + (a - c)‖ := by congr 1; abel
          _ ≤ _ := norm_add_le _ _
      linarith
    refine KAM.Weighted.general_cauchy (by positivity)
      (hF.mono (hsub.trans (ball_subset_ball (by linarith)))) fun z hz => hb z (hsub hz)
  have hlip : ∀ a ∈ ball c (R / 2), ∀ b ∈ ball c (R / 2), ‖F a - F b‖ ≤ L * ‖a - b‖ := by
    intro a ha b hb'
    have hdiff : ∀ x ∈ ball c (R / 2), DifferentiableAt ℂ F x := fun x hx =>
      hF.differentiableAt (isOpen_ball.mem_nhds (ball_subset_ball (by linarith) hx))
    exact (convex_ball c (R / 2)).norm_image_sub_le_of_norm_fderiv_le hdiff hder hb' ha
  refine ⟨M, L, min (R / 4 / (M + 1)) (1 / (2 * (L + 1))), R / 4, by positivity, by positivity,
    ⟨hF.mono (ball_subset_ball (by linarith)),
      fun z hz => hb z (ball_subset_ball (by linarith) hz), hlip, hM0, hL0, by positivity,
      by positivity, ?_, ?_⟩⟩
  · have h1 : min (R / 4 / (M + 1)) (1 / (2 * (L + 1))) ≤ R / 4 / (M + 1) := min_le_left _ _
    have h2 : M * (R / 4 / (M + 1)) ≤ R / 4 := by
      rw [← mul_div_assoc, div_le_iff₀ (by positivity)]; nlinarith
    nlinarith [mul_le_mul_of_nonneg_left h1 hM0]
  · have h1 : min (R / 4 / (M + 1)) (1 / (2 * (L + 1))) ≤ 1 / (2 * (L + 1)) := min_le_right _ _
    have h2 : L * (1 / (2 * (L + 1))) ≤ 1 / 2 := by
      rw [← mul_div_assoc, mul_one, div_le_iff₀ (by positivity)]; nlinarith
    nlinarith [mul_le_mul_of_nonneg_left h1 hL0]

end KAM.Planetary
