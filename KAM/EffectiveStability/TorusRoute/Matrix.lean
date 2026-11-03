/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.Analysis.Complex.Basic

/-!
# Complex matrices close to the identity (track B, package B5-ROUTE)

* `differentiableOn_matrix_inv_entry`: entries of the inverse of a holomorphic matrix family
  with nonvanishing determinant are holomorphic.
* `transpose_det_ne_of_entry_bound`, `norm_transpose_inv_mulVec_le`: if every entry of `A - 1`
  has modulus `≤ κ` with `n κ < 1`, then `Aᵀ` is invertible and
  `‖(Aᵀ)⁻¹ J‖ ≤ ‖J‖ / (1 - n κ)` in the sup norm.
-/

@[expose] public noncomputable section

namespace KAM.EffectiveStability

open Matrix

section Holo

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem differentiableOn_finset_prod_cx {ι : Type*} {s : Set E} (u : Finset ι) {g : ι → E → ℂ}
    (h : ∀ i ∈ u, DifferentiableOn ℂ (g i) s) : DifferentiableOn ℂ (fun x => ∏ i ∈ u, g i x) s := by
  classical
  induction u using Finset.induction_on with
  | empty => simp
  | insert a u ha ih =>
    simp only [Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).mul
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem differentiableOn_matrix_det {s : Set E} {f : E → Matrix (Fin n) (Fin n) ℂ}
    (hf : ∀ i j, DifferentiableOn ℂ (fun x => f x i j) s) :
    DifferentiableOn ℂ (fun x => (f x).det) s := by
  simp only [Matrix.det_apply']
  refine DifferentiableOn.fun_sum fun σ _ => ?_
  refine DifferentiableOn.const_mul ?_ _
  exact differentiableOn_finset_prod_cx _ fun i _ => hf _ _

/-- Entries of the inverse of a holomorphic matrix family are holomorphic where `det ≠ 0`. -/
theorem differentiableOn_matrix_inv_entry {s : Set E} {f : E → Matrix (Fin n) (Fin n) ℂ}
    (hf : ∀ i j, DifferentiableOn ℂ (fun x => f x i j) s) (hd : ∀ x ∈ s, (f x).det ≠ 0)
    (i j : Fin n) : DifferentiableOn ℂ (fun x => (f x)⁻¹ i j) s := by
  simp only [Matrix.inv_def, Matrix.smul_apply, Ring.inverse_eq_inv', smul_eq_mul,
    Matrix.adjugate_apply]
  refine ((differentiableOn_matrix_det hf).inv hd).mul ?_
  refine differentiableOn_matrix_det fun a b => ?_
  simp only [Matrix.updateRow_apply]
  by_cases hab : a = j
  · simp only [hab, ite_true]
    exact differentiableOn_const _
  · simp only [hab, ite_false]
    exact hf a b

end Holo

section Bound

variable {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} {κ : ℝ}

/-- `‖x‖ ≤ ‖Aᵀ x‖ + n κ ‖x‖` when the entries of `A - 1` are bounded by `κ ≥ 0`. -/
theorem norm_le_transpose_mulVec_add (hκ : 0 ≤ κ)
    (hA : ∀ i j, ‖A i j - (1 : Matrix (Fin n) (Fin n) ℂ) i j‖ ≤ κ) (x : Fin n → ℂ) :
    ‖x‖ ≤ ‖Aᵀ *ᵥ x‖ + n * κ * ‖x‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
  have e : x j = (Aᵀ *ᵥ x) j - ∑ i, (A i j - (1 : Matrix (Fin n) (Fin n) ℂ) i j) * x i := by
    simp [Matrix.mulVec, dotProduct, sub_mul, Finset.sum_sub_distrib, Matrix.one_apply]
  have h1 : ‖∑ i, (A i j - (1 : Matrix (Fin n) (Fin n) ℂ) i j) * x i‖ ≤ n * κ * ‖x‖ := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ i, ‖(A i j - (1 : Matrix (Fin n) (Fin n) ℂ) i j) * x i‖ ≤ ∑ _i : Fin n, κ * ‖x‖ := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [norm_mul]
          exact mul_le_mul (hA i j) (norm_le_pi_norm x i) (norm_nonneg _) hκ
      _ = n * κ * ‖x‖ := by simp [mul_assoc]
  calc ‖x j‖ = ‖(Aᵀ *ᵥ x) j - ∑ i, (A i j - (1 : Matrix (Fin n) (Fin n) ℂ) i j) * x i‖ := by
        rw [← e]
    _ ≤ ‖(Aᵀ *ᵥ x) j‖ + ‖∑ i, (A i j - (1 : Matrix (Fin n) (Fin n) ℂ) i j) * x i‖ :=
        norm_sub_le _ _
    _ ≤ _ := add_le_add (norm_le_pi_norm (Aᵀ *ᵥ x) j) h1

theorem transpose_det_ne_of_entry_bound (hκ : 0 ≤ κ) (hn : (n : ℝ) * κ < 1)
    (hA : ∀ i j, ‖A i j - (1 : Matrix (Fin n) (Fin n) ℂ) i j‖ ≤ κ) : Aᵀ.det ≠ 0 := by
  intro hd
  obtain ⟨x, hx, hx0⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hd
  have h := norm_le_transpose_mulVec_add hκ hA x
  rw [hx0, norm_zero, zero_add] at h
  have h1 : 0 < 1 - n * κ := by linarith
  exact hx (norm_le_zero_iff.mp (by nlinarith [norm_nonneg x]))

theorem norm_transpose_inv_mulVec_le (hκ : 0 ≤ κ) (hn : (n : ℝ) * κ < 1)
    (hA : ∀ i j, ‖A i j - (1 : Matrix (Fin n) (Fin n) ℂ) i j‖ ≤ κ) (J : Fin n → ℂ) :
    ‖Aᵀ⁻¹ *ᵥ J‖ ≤ ‖J‖ / (1 - n * κ) := by
  have h1 : 0 < 1 - n * κ := by linarith
  have hdet := transpose_det_ne_of_entry_bound hκ hn hA
  have hy : Aᵀ *ᵥ (Aᵀ⁻¹ *ᵥ J) = J := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet),
      Matrix.one_mulVec]
  have h := norm_le_transpose_mulVec_add hκ hA (Aᵀ⁻¹ *ᵥ J)
  rw [hy] at h
  rw [le_div_iff₀ h1]
  nlinarith

end Bound

end KAM.EffectiveStability

end
