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
# Approximate-inverse (Neumann defect) certificates for matrices

* `matrix_inv_of_approx_inverse`: if `B` is an approximate left inverse of `A` with row-sum
  defect `‖1 - B A‖ ≤ δ < 1` and `‖B‖ ≤ β`, then `A` is invertible, `‖A⁻¹‖ ≤ β / (1 - δ)` and
  `‖A⁻¹ - B‖ ≤ δ β / (1 - δ)`. No symmetry is used; the norm is the maximum row sum.
* `ModelMatrix.HasShape k M`: `M` is a list matrix with exactly `k` rows, each of length `k`
  (audit 2 F7); it is stated for lists of any type, so the matrix of models is a special case.
-/

public section

open scoped Matrix.Norms.Operator

/-- Exact shape of a list matrix: `k` rows, each of length `k` (audit 2 F7). With
`ModelMatrix.Encloses n (torsionIdx n)` and `k = n + 1`, the checked list matrix is then the
whole denoted bordered matrix, not a larger matrix containing it as a leading block. -/
@[expose] def ModelMatrix.HasShape {β : Type} (k : ℕ) (M : List (List β)) : Prop :=
  M.length = k ∧ ∀ r ∈ M, r.length = k

/-- Pointwise approximate-inverse certificate: `‖I - B A‖ ≤ δ < 1` gives `A` invertible and
`‖A⁻¹‖ ≤ ‖B‖/(1-δ)`, `‖A⁻¹ - B‖ ≤ δ‖B‖/(1-δ)` (row-sum norm; no symmetry used). -/
theorem matrix_inv_of_approx_inverse {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {A B : Matrix ι ι ℂ} {δ β : ℝ} (hδ : ‖1 - B * A‖ ≤ δ) (hδ1 : δ < 1) (hB : ‖B‖ ≤ β) :
    IsUnit A.det ∧ ‖A⁻¹‖ ≤ β / (1 - δ) ∧ ‖A⁻¹ - B‖ ≤ δ * β / (1 - δ) := by
  set E : Matrix ι ι ℂ := 1 - B * A with hE
  have hU : IsUnit (B * A) := by
    have := isUnit_one_sub_of_norm_lt_one (x := E) (hδ.trans_lt hδ1)
    simpa [hE] using this
  have hdet : IsUnit (B * A).det := (Matrix.isUnit_iff_isUnit_det _).mp hU
  have hAu : IsUnit A.det := by
    rw [Matrix.det_mul, IsUnit.mul_iff] at hdet
    exact hdet.2
  have hδ0 : 0 ≤ δ := (norm_nonneg _).trans hδ
  have hβ0 : 0 ≤ β := (norm_nonneg _).trans hB
  have h1δ : 0 < 1 - δ := by linarith
  set X : Matrix ι ι ℂ := (B * A)⁻¹ with hX
  have hXl : X * (B * A) = 1 := Matrix.nonsing_inv_mul _ hdet
  have hAinv : A⁻¹ = X * B := by
    exact Matrix.inv_eq_left_inv (by rw [mul_assoc]; exact hXl)
  have hXE : X = 1 + X * E := by
    rw [hE, mul_sub, mul_one, hXl]; abel
  have h1 : ‖(1 : Matrix ι ι ℂ)‖ ≤ 1 := by
    exact norm_one.le
  have hXn : ‖X‖ ≤ 1 / (1 - δ) := by
    have h2 : ‖X‖ ≤ 1 + ‖X‖ * δ :=
      calc ‖X‖ = ‖1 + X * E‖ := congrArg norm hXE
        _ ≤ ‖(1 : Matrix ι ι ℂ)‖ + ‖X * E‖ := norm_add_le _ _
        _ ≤ 1 + ‖X‖ * δ := add_le_add h1
          ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left hδ (norm_nonneg _)))
    rw [le_div_iff₀ h1δ]; nlinarith
  refine ⟨hAu, ?_, ?_⟩
  · rw [hAinv]
    calc ‖X * B‖ ≤ ‖X‖ * ‖B‖ := norm_mul_le _ _
      _ ≤ 1 / (1 - δ) * β := mul_le_mul hXn hB (norm_nonneg _) (by positivity)
      _ = β / (1 - δ) := by ring
  · have hX1 : X - 1 = X * E := sub_eq_iff_eq_add'.mpr hXE
    have : A⁻¹ - B = X * E * B := by
      rw [hAinv, ← hX1, sub_mul, one_mul]
    rw [this]
    calc ‖X * E * B‖ ≤ ‖X * E‖ * ‖B‖ := norm_mul_le _ _
      _ ≤ (‖X‖ * δ) * β := mul_le_mul
          ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left hδ (norm_nonneg _))) hB
          (norm_nonneg _) (by positivity)
      _ ≤ (1 / (1 - δ) * δ) * β := by gcongr
      _ = δ * β / (1 - δ) := by ring
