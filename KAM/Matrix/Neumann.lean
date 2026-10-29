/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.Linarith

/-!
# Quantitative stability of matrix inverses

The Neumann series proves invertibility under a perturbation of relative norm at most
one half. The resolvent identity then gives the inverse and inverse-difference bounds
from blueprint Part 1. Matrices use the maximum row-sum operator norm throughout.
The ring lemmas do not require a norm-one hypothesis, so empty matrices are covered too.
-/

public noncomputable section

open scoped Ring NNReal

namespace KAM

section Ring

variable {R : Type*} [NormedRing R] [CompleteSpace R]

/-- The Neumann criterion for a perturbation with relative norm at most one half. -/
theorem isUnit_add_of_inverse_norm_mul_le_half {A Δ : R} (hA : IsUnit A)
    (hsmall : ‖A⁻¹ʳ‖ * ‖Δ‖ ≤ 1 / 2) : IsUnit (A + Δ) := by
  have hnorm : ‖-(A⁻¹ʳ * Δ)‖ < 1 := by
    rw [norm_neg]
    exact (norm_mul_le _ _).trans_lt (hsmall.trans_lt (by norm_num))
  have hunit : IsUnit (1 + A⁻¹ʳ * Δ) := by
    simpa using isUnit_one_sub_of_norm_lt_one hnorm
  convert hA.mul hunit using 1
  rw [mul_add, mul_one, ← mul_assoc, Ring.mul_inverse_cancel _ hA, one_mul]

omit [CompleteSpace R] in
/-- The resolvent identity in the order needed for the quantitative estimates. -/
theorem inverse_sub_inverse_add {A Δ : R} (hA : IsUnit A) (hB : IsUnit (A + Δ)) :
    A⁻¹ʳ - (A + Δ)⁻¹ʳ = A⁻¹ʳ * Δ * (A + Δ)⁻¹ʳ := by
  simpa only [add_sub_cancel_left] using
    Ring.inverse_sub_inverse (a := A) (b := A + Δ) ⟨fun _ => hB, fun _ => hA⟩

/-- A perturbation of relative norm at most one half doubles the inverse bound at most. -/
theorem norm_inverse_add_le {A Δ : R} (hA : IsUnit A)
    (hsmall : ‖A⁻¹ʳ‖ * ‖Δ‖ ≤ 1 / 2) : ‖(A + Δ)⁻¹ʳ‖ ≤ 2 * ‖A⁻¹ʳ‖ := by
  have hB := isUnit_add_of_inverse_norm_mul_le_half hA hsmall
  have hid := inverse_sub_inverse_add hA hB
  have heq : (A + Δ)⁻¹ʳ = A⁻¹ʳ - A⁻¹ʳ * Δ * (A + Δ)⁻¹ʳ := by
    rw [← hid, sub_sub_cancel]
  have hbound : ‖(A + Δ)⁻¹ʳ‖ ≤ ‖A⁻¹ʳ‖ + (‖A⁻¹ʳ‖ * ‖Δ‖) * ‖(A + Δ)⁻¹ʳ‖ := by
    calc
      _ = ‖A⁻¹ʳ - A⁻¹ʳ * Δ * (A + Δ)⁻¹ʳ‖ := congrArg norm heq
      _ ≤ ‖A⁻¹ʳ‖ + ‖A⁻¹ʳ * Δ * (A + Δ)⁻¹ʳ‖ := norm_sub_le _ _
      _ ≤ _ := add_le_add le_rfl ((norm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)))
  have hhalf := mul_le_mul_of_nonneg_right hsmall (norm_nonneg (A + Δ)⁻¹ʳ)
  linarith

/-- The inverse changes by at most twice the squared inverse bound times the perturbation. -/
theorem norm_inverse_add_sub_inverse_le {A Δ : R} (hA : IsUnit A)
    (hsmall : ‖A⁻¹ʳ‖ * ‖Δ‖ ≤ 1 / 2) :
    ‖(A + Δ)⁻¹ʳ - A⁻¹ʳ‖ ≤ 2 * ‖A⁻¹ʳ‖ ^ 2 * ‖Δ‖ := by
  rw [norm_sub_rev, inverse_sub_inverse_add hA
    (isUnit_add_of_inverse_norm_mul_le_half hA hsmall)]
  calc
    _ ≤ (‖A⁻¹ʳ‖ * ‖Δ‖) * ‖(A + Δ)⁻¹ʳ‖ := (norm_mul_le _ _).trans
      (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ (‖A⁻¹ʳ‖ * ‖Δ‖) * (2 * ‖A⁻¹ʳ‖) := mul_le_mul_of_nonneg_left
      (norm_inverse_add_le hA hsmall) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = _ := by ring

end Ring

open scoped Matrix.Norms.Operator

section Matrix

variable {n : ℕ} {A Δ : Matrix (Fin n) (Fin n) ℂ}

/-- Row-sum bounds are exactly bounds for the selected matrix operator norm.
The explicit nonnegativity also covers a matrix with no rows. -/
theorem matrix_opNorm_le_iff_rows {m : ℕ} {M : Matrix (Fin m) (Fin n) ℂ}
    {B : ℝ} (hB : 0 ≤ B) : ‖M‖ ≤ B ↔ ∀ i, ∑ j, ‖M i j‖ ≤ B := by
  rw [Matrix.linfty_opNorm_def]
  change ((Finset.univ.sup fun i => ∑ j, ‖M i j‖₊ : ℝ≥0) : ℝ) ≤
    ((⟨B, hB⟩ : ℝ≥0) : ℝ) ↔ _
  erw [NNReal.coe_le_coe, Finset.sup_le_iff]
  simp only [Finset.mem_univ, true_implies]
  constructor
  · intro h i
    simpa only [NNReal.coe_sum, coe_nnnorm] using! (NNReal.coe_le_coe.mpr (h i))
  · intro h i
    apply NNReal.coe_le_coe.mp
    simpa only [NNReal.coe_sum, coe_nnnorm] using! h i

/-- The matrix Neumann criterion, using the usual matrix inverse and row-sum norm. -/
theorem matrix_isUnit_add_of_inv_norm_mul_le_half (hA : IsUnit A)
    (hsmall : ‖A⁻¹‖ * ‖Δ‖ ≤ 1 / 2) : IsUnit (A + Δ) := by
  rw [Matrix.nonsing_inv_eq_ringInverse] at hsmall
  exact isUnit_add_of_inverse_norm_mul_le_half hA hsmall

/-- The matrix inverse bound in the maximum row-sum operator norm. -/
theorem matrix_norm_inv_add_le (hA : IsUnit A)
    (hsmall : ‖A⁻¹‖ * ‖Δ‖ ≤ 1 / 2) : ‖(A + Δ)⁻¹‖ ≤ 2 * ‖A⁻¹‖ := by
  simp only [Matrix.nonsing_inv_eq_ringInverse] at hsmall ⊢
  exact norm_inverse_add_le hA hsmall

/-- The matrix inverse-difference bound in the maximum row-sum operator norm. -/
theorem matrix_norm_inv_add_sub_inv_le (hA : IsUnit A)
    (hsmall : ‖A⁻¹‖ * ‖Δ‖ ≤ 1 / 2) :
    ‖(A + Δ)⁻¹ - A⁻¹‖ ≤ 2 * ‖A⁻¹‖ ^ 2 * ‖Δ‖ := by
  simp only [Matrix.nonsing_inv_eq_ringInverse] at hsmall ⊢
  exact norm_inverse_add_sub_inverse_le hA hsmall

/-- Uniform inverse and inverse-difference bounds for a matrix-valued function on any set.
In particular the set can be a complex strip; no analyticity is needed for these bounds. -/
theorem matrix_neumann_uniform {X : Type*} {s : Set X}
    {A Δ : X → Matrix (Fin n) (Fin n) ℂ} {B ε : ℝ}
    (hB : 0 ≤ B) (hsmall : B * ε ≤ 1 / 2)
    (hA : ∀ x ∈ s, IsUnit (A x))
    (hbound : ∀ x ∈ s, ‖(A x)⁻¹‖ ≤ B) (hΔ : ∀ x ∈ s, ‖Δ x‖ ≤ ε) :
    ∀ x ∈ s, IsUnit (A x + Δ x) ∧ ‖(A x + Δ x)⁻¹‖ ≤ 2 * B ∧
      ‖(A x + Δ x)⁻¹ - (A x)⁻¹‖ ≤ 2 * B ^ 2 * ε := by
  intro x hx
  have hlocal : ‖(A x)⁻¹‖ * ‖Δ x‖ ≤ 1 / 2 :=
    (mul_le_mul (hbound x hx) (hΔ x hx) (norm_nonneg _) hB).trans hsmall
  refine ⟨matrix_isUnit_add_of_inv_norm_mul_le_half (hA x hx) hlocal,
    (matrix_norm_inv_add_le (hA x hx) hlocal).trans (by nlinarith [hbound x hx]), ?_⟩
  apply (matrix_norm_inv_add_sub_inv_le (hA x hx) hlocal).trans
  have hsquare : ‖(A x)⁻¹‖ ^ 2 ≤ B ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (hbound x hx) 2
  exact mul_le_mul (by linarith) (hΔ x hx) (norm_nonneg _) (by positivity)

end Matrix

end KAM

end
