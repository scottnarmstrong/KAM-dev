/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Kepler.Basic

/-!
# Secular form: orthogonal `2 × 2` matrices

Every orthogonal real `2 × 2` matrix is a rotation `rot θ` or a rotation composed with the
reflection `(v₀, v₁) ↦ (v₀, -v₁)`.
-/

@[expose] public noncomputable section
open Set Filter Real Function
namespace KAM.Planetary
open KAM KAM.Kepler

namespace SecularForm

theorem exists_angle {a c : ℝ} (h : a ^ 2 + c ^ 2 = 1) :
    ∃ θ : ℝ, Real.cos θ = a ∧ Real.sin θ = c := by
  set z : ℂ := ⟨a, c⟩ with hz
  have hn : ‖z‖ = 1 := by
    have h1 : ‖z‖ ^ 2 = 1 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp only [hz]; nlinarith
    nlinarith [norm_nonneg z]
  have hz0 : z ≠ 0 := fun h0 => by rw [h0] at hn; simp at hn
  refine ⟨Complex.arg z, ?_, ?_⟩
  · rw [Complex.cos_arg hz0, hn]; simp [hz]
  · rw [Complex.sin_arg, hn]; simp [hz]

theorem orth_cases (R : Matrix (Fin 2) (Fin 2) ℝ) (hR : R.transpose * R = 1) :
    ∃ θ : ℝ, (∀ v : Fin 2 → ℝ, R.mulVec v = rot θ v) ∨
      (∀ v : Fin 2 → ℝ, R.mulVec v = rot θ ![v 0, -v 1]) := by
  have h00 := congrFun (congrFun hR 0) 0
  have h11 := congrFun (congrFun hR 1) 1
  have h01 := congrFun (congrFun hR 0) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h00 h11 h01
  set a := R 0 0 with ha
  set b := R 0 1 with hb
  set c := R 1 0 with hc
  set d := R 1 1 with hd
  have hdet : (a * d - b * c - 1) * (a * d - b * c + 1) = 0 := by
    have : (a * d - b * c) ^ 2 = (a ^ 2 + c ^ 2) * (b ^ 2 + d ^ 2) - (a * b + c * d) ^ 2 := by ring
    nlinarith [h00, h11, h01]
  rcases mul_eq_zero.1 hdet with h | h
  · have hs : (d - a) ^ 2 + (b + c) ^ 2 = 0 := by nlinarith [h00, h11]
    have hda : d = a := by nlinarith [sq_nonneg (d - a), sq_nonneg (b + c)]
    have hbc : b = -c := by nlinarith [sq_nonneg (d - a), sq_nonneg (b + c)]
    obtain ⟨θ, hθ1, hθ2⟩ := exists_angle (a := a) (c := c) (by linarith [h00])
    refine ⟨θ, Or.inl fun v => ?_⟩
    ext k
    fin_cases k <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, rot, hθ1, hθ2] <;>
      simp only [← ha, ← hb, ← hc, ← hd, hda, hbc] <;> ring
  · have hs : (d + a) ^ 2 + (b - c) ^ 2 = 0 := by nlinarith [h00, h11]
    have hda : d = -a := by nlinarith [sq_nonneg (d + a), sq_nonneg (b - c)]
    have hbc : b = c := by nlinarith [sq_nonneg (d + a), sq_nonneg (b - c)]
    obtain ⟨θ, hθ1, hθ2⟩ := exists_angle (a := a) (c := c) (by linarith [h00])
    refine ⟨θ, Or.inr fun v => ?_⟩
    ext k
    fin_cases k <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, rot, hθ1, hθ2] <;>
      simp only [← ha, ← hb, ← hc, ← hd, hda, hbc] <;> ring

end SecularForm
end KAM.Planetary
end
