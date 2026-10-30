/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Matrix.Bridges
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Matrix tools for the sharp a-posteriori theorems

* `KAM.Sharp.neumann_ratio` (blueprint `bp:p2s:neumann`): the Neumann lemma with a general ratio
  `q < 1`, `KAM.neumann` being `q = 1/2`.
* `KAM.Sharp.norm_mul_sub_mul_le` (blueprint `bp:p2s:telescope`): the two-factor telescoping step.
-/

public noncomputable section

open scoped Matrix.Norms.Operator Ring

namespace KAM.Sharp

/-- Ring form of `neumann_ratio`. -/
private theorem ring_neumann_ratio {R : Type*} [NormedRing R] [CompleteSpace R] {A Δ : R}
    (hA : IsUnit A) {q : ℝ} (hq : q < 1) (hsmall : ‖A⁻¹ʳ‖ * ‖Δ‖ ≤ q) :
    IsUnit (A + Δ) ∧ ‖(A + Δ)⁻¹ʳ‖ ≤ ‖A⁻¹ʳ‖ / (1 - q) ∧
      ‖(A + Δ)⁻¹ʳ - A⁻¹ʳ‖ ≤ ‖A⁻¹ʳ‖ ^ 2 * ‖Δ‖ / (1 - q) := by
  have hq' : 0 < 1 - q := by linarith
  have hB : IsUnit (A + Δ) := by
    have hnorm : ‖-(A⁻¹ʳ * Δ)‖ < 1 := by
      rw [norm_neg]
      exact (norm_mul_le _ _).trans_lt (hsmall.trans_lt hq)
    have hunit : IsUnit (1 + A⁻¹ʳ * Δ) := by
      simpa using isUnit_one_sub_of_norm_lt_one hnorm
    convert hA.mul hunit using 1
    rw [mul_add, mul_one, ← mul_assoc, Ring.mul_inverse_cancel _ hA, one_mul]
  have hid := inverse_sub_inverse_add hA hB
  have hbound : ‖(A + Δ)⁻¹ʳ‖ ≤ ‖A⁻¹ʳ‖ + (‖A⁻¹ʳ‖ * ‖Δ‖) * ‖(A + Δ)⁻¹ʳ‖ := by
    have heq : (A + Δ)⁻¹ʳ = A⁻¹ʳ - A⁻¹ʳ * Δ * (A + Δ)⁻¹ʳ := by
      rw [← hid, sub_sub_cancel]
    calc
      _ = ‖A⁻¹ʳ - A⁻¹ʳ * Δ * (A + Δ)⁻¹ʳ‖ := congrArg norm heq
      _ ≤ ‖A⁻¹ʳ‖ + ‖A⁻¹ʳ * Δ * (A + Δ)⁻¹ʳ‖ := norm_sub_le _ _
      _ ≤ _ := add_le_add le_rfl ((norm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)))
  have hq1 := mul_le_mul_of_nonneg_right hsmall (norm_nonneg (A + Δ)⁻¹ʳ)
  have hinv : ‖(A + Δ)⁻¹ʳ‖ ≤ ‖A⁻¹ʳ‖ / (1 - q) := by
    rw [le_div_iff₀ hq']
    nlinarith
  refine ⟨hB, hinv, ?_⟩
  rw [norm_sub_rev, hid]
  calc
    _ ≤ (‖A⁻¹ʳ‖ * ‖Δ‖) * ‖(A + Δ)⁻¹ʳ‖ := (norm_mul_le _ _).trans
      (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ (‖A⁻¹ʳ‖ * ‖Δ‖) * (‖A⁻¹ʳ‖ / (1 - q)) :=
      mul_le_mul_of_nonneg_left hinv (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = _ := by ring

/-- Blueprint `bp:p2s:neumann` (ratio `q`). -/
theorem neumann_ratio {ι : Type*} [Fintype ι] [DecidableEq ι] {A Δ : Matrix ι ι ℂ} (hA : IsUnit A)
    {q : ℝ} (hq : q < 1) (hsmall : ‖A⁻¹‖ * ‖Δ‖ ≤ q) :
    IsUnit (A + Δ) ∧ ‖(A + Δ)⁻¹‖ ≤ ‖A⁻¹‖ / (1 - q) ∧
      ‖(A + Δ)⁻¹ - A⁻¹‖ ≤ ‖A⁻¹‖ ^ 2 * ‖Δ‖ / (1 - q) := by
  simp only [Matrix.nonsing_inv_eq_ringInverse] at hsmall ⊢
  exact ring_neumann_ratio hA hq hsmall

/-- The two-factor step of `bp:p2s:telescope`. -/
theorem norm_mul_sub_mul_le {ι κ' μ' : Type*} [Fintype ι] [Fintype κ'] [Fintype μ']
    (X X' : Matrix ι κ' ℂ) (Y Y' : Matrix κ' μ' ℂ) :
    ‖X' * Y' - X * Y‖ ≤ ‖X'‖ * ‖Y' - Y‖ + ‖X' - X‖ * ‖Y‖ := by
  have h : X' * Y' - X * Y = X' * (Y' - Y) + (X' - X) * Y := by
    rw [Matrix.mul_sub, Matrix.sub_mul]; abel
  rw [h]
  exact (norm_add_le _ _).trans (add_le_add (Matrix.linfty_opNorm_mul _ _)
    (Matrix.linfty_opNorm_mul _ _))

end KAM.Sharp

end
