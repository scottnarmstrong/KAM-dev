/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Sharp.Frame

/-!
# Geometry controlled by the normal error

Blueprint `bp:p2s2:sec-geo`.

* `norm_invarianceError_le_eta` (`bp:p2s2:recovery`, FH24 Lemma 3.3): the invariance error `E` is
  recovered from its tangent and normal parts `ηᴸ`, `ηᴺ`. Writing `E = L ξᴸ + N ξᴺ`, the identities
  `Lᵀ Ω₀ N = -I`, `Nᵀ Ω₀ L = I` give `ηᴺ = Ω_K ξᴸ - ξᴺ` and `ηᴸ = -ξᴸ - Ω_N ξᴺ`; with
  `|Ω_K|, |Ω_N| ≤ q < 1` this solves for `ξ` (`frame_surj`) and bounds it.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator
open Matrix

namespace KAM.Sharp2

open KAM KAM.Torus KAM.Apost

section Recovery

variable {n : ℕ} {h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
  {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {θ : Fin n → ℂ}

/-- `P (x, y) = L x + N y`, and the two projections of `Lᵀ Ω₀ ·` and `Nᵀ Ω₀ ·` of it. -/
theorem frame_proj (hG : IsUnit (gramMatrix K θ).det) (x y : Fin n → ℂ) :
    ((tangentMat K θ)ᵀ * omegaZeroMatrix n) *ᵥ (frameMat K θ *ᵥ Sum.elim x y) =
        lagrangeMat K θ *ᵥ x - y ∧
      ((normalMat K θ)ᵀ * omegaZeroMatrix n) *ᵥ (frameMat K θ *ᵥ Sum.elim x y) =
        x + ((normalMat K θ)ᵀ * omegaZeroMatrix n * normalMat K θ) *ᵥ y := by
  have h1 := Identities.fi_LtON K hG
  have h2 := Identities.fi_NtOL K hG
  rw [frameMat, Matrix.fromCols_mulVec_sumElim]
  constructor
  · rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h1, lagrangeMat,
      Matrix.neg_mulVec, Matrix.one_mulVec, sub_eq_add_neg]
  · rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h2, Matrix.one_mulVec]

/-- Under `|Ω_K|, |Ω_N| ≤ q < 1` the frame `P = (L N)` is onto. -/
theorem frame_surj (hG : IsUnit (gramMatrix K θ).det) {q : ℝ} (hq : q < 1)
    (hΩK : ‖lagrangeMat K θ‖ ≤ q) (hΩN : ‖(normalMat K θ)ᵀ * omegaZeroMatrix n * normalMat K θ‖ ≤ q)
    (e : Fin n ⊕ Fin n → ℂ) : ∃ x y : Fin n → ℂ, frameMat K θ *ᵥ Sum.elim x y = e := by
  have hq0 : 0 ≤ q := (norm_nonneg _).trans hΩK
  have key : ∀ x y : Fin n → ℂ, frameMat K θ *ᵥ Sum.elim x y = 0 → x = 0 ∧ y = 0 := by
    intro x y hxy
    obtain ⟨p1, p2⟩ := frame_proj hG x y
    rw [hxy, Matrix.mulVec_zero] at p1 p2
    have hy : y = lagrangeMat K θ *ᵥ x := (sub_eq_zero.mp p1.symm).symm
    have hx : x = -(((normalMat K θ)ᵀ * omegaZeroMatrix n * normalMat K θ) *ᵥ y) :=
      eq_neg_of_add_eq_zero_left p2.symm
    have e1 : ‖y‖ ≤ q * ‖x‖ := by
      rw [hy]
      exact (Matrix.linfty_opNorm_mulVec _ _).trans (mul_le_mul_of_nonneg_right hΩK (norm_nonneg _))
    have e2 : ‖x‖ ≤ q * ‖y‖ := by
      rw [hx, norm_neg]
      exact (Matrix.linfty_opNorm_mulVec _ _).trans (mul_le_mul_of_nonneg_right hΩN (norm_nonneg _))
    have hy0 : ‖y‖ = 0 := by
      have : ‖y‖ ≤ q ^ 2 * ‖y‖ := by
        calc ‖y‖ ≤ q * ‖x‖ := e1
          _ ≤ q * (q * ‖y‖) := mul_le_mul_of_nonneg_left e2 hq0
          _ = q ^ 2 * ‖y‖ := by ring
      have hq2 : q ^ 2 < 1 := by nlinarith
      nlinarith [norm_nonneg y]
    have hy' : y = 0 := norm_eq_zero.mp hy0
    refine ⟨?_, hy'⟩
    rw [hx, hy', Matrix.mulVec_zero, neg_zero]
  have hU : IsUnit (frameMat K θ) := by
    rw [← Matrix.mulVec_injective_iff_isUnit]
    intro a b hab
    have hz : frameMat K θ *ᵥ (a - b) = 0 := by rw [Matrix.mulVec_sub, hab, sub_self]
    have hab' : a - b = Sum.elim ((a - b) ∘ Sum.inl) ((a - b) ∘ Sum.inr) := by
      ext i; cases i <;> rfl
    rw [hab'] at hz
    obtain ⟨hx, hy⟩ := key _ _ hz
    have : a - b = 0 := by
      rw [hab', hx, hy]; ext i; cases i <;> rfl
    exact sub_eq_zero.mp this
  obtain ⟨v, hv⟩ := (Matrix.mulVec_surjective_iff_isUnit.mpr hU) e
  refine ⟨v ∘ Sum.inl, v ∘ Sum.inr, ?_⟩
  rw [Sum.elim_comp_inl_inr]
  exact hv

end Recovery

/-- Blueprint `bp:p2s2:recovery`: the invariance error from its tangent and normal parts (FH24 Lemma 3.3). -/
theorem norm_invarianceError_le_eta {n : ℕ} {σK σN q εL εN r : ℝ} {ω : Fin n → ℝ}
    {h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} (hq : q < 1)
    (hL : ∀ θ ∈ complexStrip n r, ‖tangentMat K θ‖ ≤ σK) (hN : ∀ θ ∈ complexStrip n r, ‖normalMat K θ‖ ≤ σN)
    (hG : ∀ θ ∈ complexStrip n r, IsUnit (gramMatrix K θ).det)
    (hΩK : ∀ θ ∈ complexStrip n r, ‖lagrangeMat K θ‖ ≤ q)
    (hΩN : ∀ θ ∈ complexStrip n r, ‖(normalMat K θ)ᵀ * omegaZeroMatrix n * normalMat K θ‖ ≤ q)
    (hηL : ∀ θ ∈ complexStrip n r, ‖etaL h K ω θ‖ ≤ εL) (hηN : ∀ θ ∈ complexStrip n r, ‖etaN h K ω θ‖ ≤ εN) :
    ∀ θ ∈ complexStrip n r, ‖invarianceError h K ω θ‖ ≤
      (σK + σN * q) / (1 - q ^ 2) * εL + (σN + σK * q) / (1 - q ^ 2) * εN := by
  intro θ hθ
  have hq0 : 0 ≤ q := (norm_nonneg _).trans (hΩK θ hθ)
  have hσK : 0 ≤ σK := (norm_nonneg _).trans (hL θ hθ)
  have hσN : 0 ≤ σN := (norm_nonneg _).trans (hN θ hθ)
  have hεL : 0 ≤ εL := (norm_nonneg _).trans (hηL θ hθ)
  have hεN : 0 ≤ εN := (norm_nonneg _).trans (hηN θ hθ)
  have hd : 0 < 1 - q ^ 2 := by nlinarith
  obtain ⟨x, y, hxy⟩ := frame_surj (hG θ hθ) hq (hΩK θ hθ) (hΩN θ hθ)
    (sumVec n (invarianceError h K ω θ))
  obtain ⟨p1, p2⟩ := frame_proj (hG θ hθ) x y
  rw [hxy] at p1 p2
  have hN' : etaN h K ω θ = lagrangeMat K θ *ᵥ x - y := p1
  have hL' : etaL h K ω θ = -(x + ((normalMat K θ)ᵀ * omegaZeroMatrix n * normalMat K θ) *ᵥ y) := by
    rw [etaL, p2]
  have e1 : ‖y‖ ≤ q * ‖x‖ + εN := by
    have : y = lagrangeMat K θ *ᵥ x - etaN h K ω θ := by rw [hN']; abel
    rw [this]
    refine (norm_sub_le _ _).trans (add_le_add ?_ (hηN θ hθ))
    exact (Matrix.linfty_opNorm_mulVec _ _).trans (mul_le_mul_of_nonneg_right (hΩK θ hθ) (norm_nonneg _))
  have e2 : ‖x‖ ≤ εL + q * ‖y‖ := by
    have : x = -etaL h K ω θ - ((normalMat K θ)ᵀ * omegaZeroMatrix n * normalMat K θ) *ᵥ y := by
      rw [hL']; abel
    rw [this]
    refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_neg]; exact hηL θ hθ
    · exact (Matrix.linfty_opNorm_mulVec _ _).trans (mul_le_mul_of_nonneg_right (hΩN θ hθ) (norm_nonneg _))
  have hx : ‖x‖ ≤ (εL + q * εN) / (1 - q ^ 2) := by
    rw [le_div_iff₀ hd]
    nlinarith [norm_nonneg x, norm_nonneg y]
  have hy : ‖y‖ ≤ (εN + q * εL) / (1 - q ^ 2) := by
    rw [le_div_iff₀ hd]
    nlinarith [norm_nonneg x, norm_nonneg y]
  have hE : ‖invarianceError h K ω θ‖ ≤ σK * ‖x‖ + σN * ‖y‖ := by
    rw [← norm_sumVec, ← hxy, frameMat, Matrix.fromCols_mulVec_sumElim]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · exact (Matrix.linfty_opNorm_mulVec _ _).trans (mul_le_mul_of_nonneg_right (hL θ hθ) (norm_nonneg _))
    · exact (Matrix.linfty_opNorm_mulVec _ _).trans (mul_le_mul_of_nonneg_right (hN θ hθ) (norm_nonneg _))
  calc _ ≤ σK * ‖x‖ + σN * ‖y‖ := hE
    _ ≤ σK * ((εL + q * εN) / (1 - q ^ 2)) + σN * ((εN + q * εL) / (1 - q ^ 2)) :=
        add_le_add (mul_le_mul_of_nonneg_left hx hσK) (mul_le_mul_of_nonneg_left hy hσN)
    _ = _ := by field_simp; ring

end KAM.Sharp2

end
