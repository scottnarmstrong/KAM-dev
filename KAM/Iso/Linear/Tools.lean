/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Iso.Linear.Defs
public import KAM.Matrix.Neumann
public import KAM.Matrix.Inverse

/-!
# Part 1 (isoenergetic linear step): small tools

Blueprint nodes `bpI:p1:ray` and `bpI:p1:ext-neumann`, and the finite-index versions of the
Kolmogorov matrix Neumann/realness lemmas
(`KAM.Apost` states them for `Fin n` only; the bordered matrices of Part 1 live on `Fin n ⊕ Unit`).

* `isDiophantine_smul` (`bpI:p1:ray`): `s ω*` is `(γ, τ)`-Diophantine for `s ≥ 1`.
* `isUnit_det_one_sub` (`bpI:p1:ext-neumann`): `1 - X` has a unit determinant if `‖X‖ < 1`.
* `neumann_fintype`: `KAM.matrix_neumann_uniform` for any finite index type.
* `inv_im_eq_zero`: `bp:p1:real-inverse` for any finite index type.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator
open scoped Ring
open Matrix

namespace KAM.Iso.Linear

open KAM

variable {n : ℕ}

/-- `bpI:p1:ray`: `sω*` is `(γ, τ)`-Diophantine for `s ≥ 1`. -/
theorem isDiophantine_smul {γ τ s : ℝ} {ωstar : Fin n → ℝ} (hdio : IsDiophantine γ τ ωstar)
    (hs : 1 ≤ s) : IsDiophantine γ τ (s • ωstar) := by
  intro k hk
  have hsum : ∑ i, (k i : ℝ) * (s • ωstar) i = s * ∑ i, (k i : ℝ) * ωstar i := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [hsum, abs_mul, abs_of_nonneg (by linarith : 0 ≤ s)]
  exact (hdio k hk).trans (le_mul_of_one_le_left (abs_nonneg _) hs)

/-- `bpI:p1:ext-neumann` (radius one), any finite index type. -/
theorem isUnit_det_one_sub {ι : Type*} [Fintype ι] [DecidableEq ι] {X : Matrix ι ι ℂ}
    (hX : ‖X‖ < 1) : IsUnit (1 - X).det :=
  (Matrix.isUnit_iff_isUnit_det _).1 (isUnit_one_sub_of_norm_lt_one hX)

/-- `KAM.matrix_neumann_uniform` (`bp:p1:neumann`) for any finite index type (`Fin n ⊕ Unit`). -/
theorem neumann_fintype {ι : Type*} [Fintype ι] [DecidableEq ι] {A Δ : Matrix ι ι ℂ} {σ : ℝ}
    (hA : IsUnit A.det) (hσ : ‖A⁻¹‖ ≤ σ) (hs : σ * ‖Δ‖ ≤ 1 / 2) :
    IsUnit (A + Δ).det ∧ ‖(A + Δ)⁻¹‖ ≤ 2 * σ ∧ ‖(A + Δ)⁻¹ - A⁻¹‖ ≤ 2 * σ ^ 2 * ‖Δ‖ := by
  have hAu : IsUnit A := (Matrix.isUnit_iff_isUnit_det _).2 hA
  have hlocal : ‖A⁻¹‖ * ‖Δ‖ ≤ 1 / 2 :=
    (mul_le_mul_of_nonneg_right hσ (norm_nonneg _)).trans hs
  have hσ0 : 0 ≤ σ := (norm_nonneg _).trans hσ
  have hsmall : ‖A⁻¹ʳ‖ * ‖Δ‖ ≤ 1 / 2 := by
    rwa [← Matrix.nonsing_inv_eq_ringInverse]
  have hB : IsUnit (A + Δ) := isUnit_add_of_inverse_norm_mul_le_half hAu hsmall
  refine ⟨(Matrix.isUnit_iff_isUnit_det _).1 hB, ?_, ?_⟩
  · have h1 : ‖(A + Δ)⁻¹ʳ‖ ≤ 2 * ‖A⁻¹ʳ‖ := norm_inverse_add_le hAu hsmall
    simp only [Matrix.nonsing_inv_eq_ringInverse] at hσ ⊢
    linarith
  · have h2 : ‖(A + Δ)⁻¹ʳ - A⁻¹ʳ‖ ≤ 2 * ‖A⁻¹ʳ‖ ^ 2 * ‖Δ‖ :=
      norm_inverse_add_sub_inverse_le hAu hsmall
    simp only [Matrix.nonsing_inv_eq_ringInverse] at hσ ⊢
    refine h2.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hσ 2) (by norm_num)

/-- `bp:p1:real-inverse` for any finite index type. -/
theorem inv_im_eq_zero {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℂ}
    (hA : ∀ i j, (A i j).im = 0) (i j : ι) : (A⁻¹ i j).im = 0 := by
  let B : Matrix ι ι ℝ := Matrix.of fun a b => (A a b).re
  have hAB : A = B.map Complex.ofReal := by
    ext a b
    exact (Complex.ext (by simp [B]) (by simp [B, hA a b]))
  have hdet : A.det = (B.det : ℂ) := by
    have h := RingHom.map_det Complex.ofRealHom B
    rw [RingHom.mapMatrix_apply] at h
    rw [hAB]
    exact h.symm
  have hadj : A.adjugate = B.adjugate.map Complex.ofReal := by
    have h := RingHom.map_adjugate Complex.ofRealHom B
    rw [RingHom.mapMatrix_apply, RingHom.mapMatrix_apply] at h
    rw [hAB]
    exact h.symm
  rw [Matrix.inv_def, Ring.inverse_eq_inv', hdet, hadj]
  simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
  rw [← Complex.ofReal_inv, ← Complex.ofReal_mul]
  exact Complex.ofReal_im _

end KAM.Iso.Linear

end
