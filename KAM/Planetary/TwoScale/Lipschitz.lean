/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Strip.Cauchy
public import KAM.Strip.Analytic
public import KAM.Frozen.Defs.ActionNbhd

/-!
# Two-scale KAM: Lipschitz bound from a supremum bound

`bpP:p3:lip-sup` with `stepP:p3:ls-close`, `stepP:p3:ls-far`. A holomorphic map bounded by `A` on
the complex `r`-neighbourhood of a real set `S` is `4 N A / r`-Lipschitz on `S` (max norms). Near
pairs (`‖x - y‖ < r / 2`) use the Cauchy estimate on the ball and the convex mean-value bound;
far pairs use the triangle inequality. The zero-dimensional case is a subsingleton domain.
-/

public section

open Metric Set

namespace KAM.Planetary

private theorem isOpen_actionNbhd_aux {N : ℕ} (S : Set (Fin N → ℝ)) (r : ℝ) :
    IsOpen (KAM.actionNbhd S r) := by
  have : KAM.actionNbhd S r = ⋃ J ∈ S, ball (KAM.realInclusion N J) r := by
    ext I
    simp [KAM.actionNbhd, dist_eq_norm]
    rfl
  rw [this]
  exact isOpen_biUnion fun _ _ => isOpen_ball

theorem lip_sup {N m : ℕ} {S : Set (Fin N → ℝ)} {r A : ℝ} (hr : 0 < r) (hA : 0 ≤ A)
    {Δ : (Fin N → ℂ) → (Fin m → ℂ)}
    (hΔ : DifferentiableOn ℂ Δ (KAM.actionNbhd S r))
    (hbound : ∀ z ∈ KAM.actionNbhd S r, ‖Δ z‖ ≤ A) :
    ∀ x ∈ S, ∀ y ∈ S,
      ‖Δ (KAM.realInclusion N x) - Δ (KAM.realInclusion N y)‖ ≤ 4 * N * A / r * ‖x - y‖ := by
  intro x hx y hy
  have hxU : ∀ w ∈ ball (KAM.realInclusion N x) r, w ∈ KAM.actionNbhd S r := fun w hw =>
    ⟨x, hx, by rw [mem_ball, dist_eq_norm] at hw; exact hw⟩
  have hxm : KAM.realInclusion N x ∈ KAM.actionNbhd S r :=
    hxU _ (mem_ball_self hr)
  have hym : KAM.realInclusion N y ∈ KAM.actionNbhd S r :=
    ⟨y, hy, by
      have : KAM.realInclusion N y - (fun i => (y i : ℂ)) = 0 := by ext i; simp
      rw [this, norm_zero]; exact hr⟩
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    have : x = y := Subsingleton.elim _ _
    subst this
    simp
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hc : 0 ≤ A / r := div_nonneg hA hr.le
  have hxy : 0 ≤ ‖x - y‖ := norm_nonneg _
  by_cases hnear : ‖x - y‖ < r / 2
  · -- near pair
    have hU := isOpen_actionNbhd_aux S r
    have hder : ∀ z ∈ ball (KAM.realInclusion N x) (r / 2),
        ‖fderiv ℂ Δ z‖ ≤ 2 * A / r := by
      intro z hz
      have hsub : closedBall z (r / 2) ⊆ KAM.actionNbhd S r := by
        intro w hw
        apply hxU
        rw [mem_ball, dist_eq_norm] at hz ⊢
        rw [mem_closedBall, dist_eq_norm] at hw
        calc ‖w - KAM.realInclusion N x‖ = ‖(w - z) + (z - KAM.realInclusion N x)‖ := by
              congr 1; abel
          _ ≤ ‖w - z‖ + ‖z - KAM.realInclusion N x‖ := norm_add_le _ _
          _ < r := by linarith
      have h := KAM.norm_fderiv_le_of_closedBall hU hΔ (by positivity : 0 < r / 2) hsub hbound
      calc ‖fderiv ℂ Δ z‖ ≤ A / (r / 2) := h
        _ = 2 * A / r := by field_simp
    have hdiff : ∀ z ∈ ball (KAM.realInclusion N x) (r / 2),
        HasFDerivWithinAt Δ (fderiv ℂ Δ z) (ball (KAM.realInclusion N x) (r / 2)) z := by
      intro z hz
      have hzU : z ∈ KAM.actionNbhd S r := hxU z (ball_subset_ball (by linarith) hz)
      exact ((hΔ.differentiableAt (hU.mem_nhds hzU)).hasFDerivAt).hasFDerivWithinAt
    have hyb : KAM.realInclusion N y ∈ ball (KAM.realInclusion N x) (r / 2) := by
      rw [mem_ball, dist_eq_norm, ← map_sub, KAM.norm_realInclusion, norm_sub_rev]
      exact hnear
    have hcv := convex_ball (KAM.realInclusion N x) (r / 2)
    have hmv := hcv.norm_image_sub_le_of_norm_hasFDerivWithin_le
      hdiff hder (mem_ball_self (by positivity)) hyb
    rw [← map_sub, KAM.norm_realInclusion] at hmv
    rw [norm_sub_rev] at hmv
    calc _ ≤ 2 * A / r * ‖x - y‖ := by
          rw [norm_sub_rev]; simpa [norm_sub_rev] using hmv
      _ ≤ 4 * N * A / r * ‖x - y‖ := by
          apply mul_le_mul_of_nonneg_right _ hxy
          rw [div_le_div_iff_of_pos_right hr]
          nlinarith
  · -- far pair
    rw [not_lt] at hnear
    calc ‖Δ (KAM.realInclusion N x) - Δ (KAM.realInclusion N y)‖
        ≤ ‖Δ (KAM.realInclusion N x)‖ + ‖Δ (KAM.realInclusion N y)‖ := norm_sub_le _ _
      _ ≤ 2 * A := by linarith [hbound _ hxm, hbound _ hym]
      _ ≤ 4 * N * A / r * ‖x - y‖ := by
          rw [div_mul_eq_mul_div, le_div_iff₀ hr]
          nlinarith [mul_nonneg hA hxy, mul_nonneg hA (sub_nonneg.2 hN1)]

end KAM.Planetary
