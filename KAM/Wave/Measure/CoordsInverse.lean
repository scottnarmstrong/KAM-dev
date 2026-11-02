/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Measure.Coords
public import Mathlib.Analysis.Matrix.Normed

/-!
# W7: the inverse of the frequency map (blueprint `bpW:w7:freqcoords` (i)–(iii))

Lemma `bpW:w7:freqcoords`, the parts not in `KAM.Wave.Measure.Coords`:
(i) `A⁻¹ = (8π/21) [[-3λ₁², 4λ₁λ₂], [4λ₁λ₂, -3λ₂²]]` and `A⁻¹ b = (8π/21) λ_J` with
`b = (λ₁⁻¹, λ₂⁻¹)`; (ii) the `ℓ^∞` operator norms (maximal absolute row sums,
`open scoped Matrix.Norms.Operator`) `‖A‖_∞ = N_A` and `‖A⁻¹‖_∞ = L_A`; (iii) `ω⁰` is an affine
bijection of `ℝ²` with inverse `ζ ↦ A⁻¹ (ζ - λ_J)`.
-/

@[expose] public noncomputable section

open Real

namespace KAM.Wave

variable (m : ℝ) (hm : 0 < m)

/-- `b = (λ₁⁻¹, λ₂⁻¹)` (blueprint `bpW:w7:unpert`). -/
def measBvec : Fin 2 → ℝ := fun i => (lamTan m hm i)⁻¹

/-- The displayed matrix `(8π/21) [[-3λ₁², 4λ₁λ₂], [4λ₁λ₂, -3λ₂²]]`
(blueprint `bpW:w7:freqcoords` (i)). -/
def measAinvMat : Matrix (Fin 2) (Fin 2) ℝ :=
  !![8 * π / 21 * (-3 * lamTan m hm 0 ^ 2), 8 * π / 21 * (4 * lamTan m hm 0 * lamTan m hm 1);
    8 * π / 21 * (4 * lamTan m hm 0 * lamTan m hm 1), 8 * π / 21 * (-3 * lamTan m hm 1 ^ 2)]

theorem actionAMat_mul_measAinvMat : actionAMat m hm * measAinvMat m hm = 1 := by
  have h0 := (lamTan_pos m hm 0).ne'
  have h1 := (lamTan_pos m hm 1).ne'
  have hpi : π ≠ 0 := Real.pi_ne_zero
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, actionAMat, actionA, measAinvMat] <;>
    field_simp <;> ring

theorem measAinvMat_mul_actionAMat : measAinvMat m hm * actionAMat m hm = 1 := by
  have h0 := (lamTan_pos m hm 0).ne'
  have h1 := (lamTan_pos m hm 1).ne'
  have hpi : π ≠ 0 := Real.pi_ne_zero
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, actionAMat, actionA, measAinvMat] <;>
    field_simp <;> ring

/-- `A⁻¹ = (8π/21) [[-3λ₁², 4λ₁λ₂], [4λ₁λ₂, -3λ₂²]]` (blueprint `bpW:w7:freqcoords` (i)). -/
theorem actionAMat_inv : (actionAMat m hm)⁻¹ = measAinvMat m hm :=
  Matrix.inv_eq_right_inv (actionAMat_mul_measAinvMat m hm)

/-- `|det A| = D_A` (blueprint `bpW:w7:freqcoords` (i)). -/
theorem abs_det_actionAMat : |(actionAMat m hm).det| = measDA m hm :=
  (measDA_eq_abs_det m hm).symm

/-- `A⁻¹ b = (8π/21) λ_J` (blueprint `bpW:w7:freqcoords` (i)). -/
theorem actionAMat_inv_mulVec_measBvec :
    ((actionAMat m hm)⁻¹).mulVec (measBvec m hm) = (8 * π / 21) • fun i => lamTan m hm i := by
  have h0 := (lamTan_pos m hm 0).ne'
  have h1 := (lamTan_pos m hm 1).ne'
  rw [actionAMat_inv]
  ext i
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, measAinvMat, measBvec] <;>
    field_simp <;> ring

section norms

open scoped Matrix.Norms.Operator

/-- `‖A‖_∞ = N_A`, the `ℓ^∞` operator norm (maximal absolute row sum)
(blueprint `bpW:w7:freqcoords` (ii)). -/
theorem actionAMat_linfty_opNorm : ‖actionAMat m hm‖ = measNA m hm := by
  obtain ⟨g0, g01, g1⟩ := measLam_facts m hm
  have hl0 := lamTan_pos m hm 0
  have hl1 := lamTan_pos m hm 1
  have hpi := Real.pi_pos
  have hNA := measNA_pos m hm
  -- the two absolute row sums
  have r0 : ∑ j, |actionA m hm 0 j| = measNA m hm := by
    simp only [Fin.sum_univ_two, actionA, measNA]
    simp
    rw [abs_of_pos (by positivity), abs_of_pos (by positivity)]
    field_simp; ring
  have r1 : ∑ j, |actionA m hm 1 j| ≤ measNA m hm := by
    simp only [Fin.sum_univ_two, actionA, measNA]
    simp
    rw [abs_of_pos (by positivity), abs_of_pos (by positivity)]
    have h3 : 3 / lamTan m hm 1 ^ 2 ≤ 3 / lamTan m hm 0 ^ 2 := by
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      nlinarith
    have h4 : 3 / (2 * π * lamTan m hm 1 * lamTan m hm 0) =
        3 / (8 * π) * (4 / (lamTan m hm 0 * lamTan m hm 1)) := by
      field_simp; ring
    have h5 : 9 / (8 * π * lamTan m hm 1 ^ 2) = 3 / (8 * π) * (3 / lamTan m hm 1 ^ 2) := by
      field_simp; ring
    rw [h4, h5, ← mul_add]
    apply mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hrow : ∀ i, ((∑ j, ‖actionAMat m hm i j‖₊ : NNReal) : ℝ) = ∑ j, |actionA m hm i j| := by
    intro i
    simp [actionAMat, Real.norm_eq_abs]
  rw [Matrix.linfty_opNorm_def]
  apply le_antisymm
  · have : (Finset.univ.sup fun i => ∑ j, ‖actionAMat m hm i j‖₊) ≤ (measNA m hm).toNNReal := by
      refine Finset.sup_le fun i _ => ?_
      rw [← NNReal.coe_le_coe, hrow, Real.coe_toNNReal _ hNA.le]
      fin_cases i
      · exact r0.le
      · exact r1
    have := NNReal.coe_le_coe.2 this
    rwa [Real.coe_toNNReal _ hNA.le] at this
  · have := Finset.le_sup (f := fun i => ∑ j, ‖actionAMat m hm i j‖₊) (Finset.mem_univ 0)
    have := NNReal.coe_le_coe.2 this
    rw [hrow, r0] at this
    exact this

/-- `‖A⁻¹‖_∞ = L_A`, the `ℓ^∞` operator norm (maximal absolute row sum)
(blueprint `bpW:w7:freqcoords` (ii)). -/
theorem actionAMat_inv_linfty_opNorm : ‖(actionAMat m hm)⁻¹‖ = measLA m hm := by
  obtain ⟨g0, g01, g1⟩ := measLam_facts m hm
  have hl0 := lamTan_pos m hm 0
  have hl1 := lamTan_pos m hm 1
  have hpi := Real.pi_pos
  have hLA := measLA_pos m hm
  have r1 : ∑ j, |measAinvMat m hm 1 j| = measLA m hm := by
    have a : |8 * π / 21 * (4 * lamTan m hm 0 * lamTan m hm 1)| =
        8 * π / 21 * (4 * lamTan m hm 0 * lamTan m hm 1) := abs_of_pos (by positivity)
    have b : |8 * π / 21 * (-3 * lamTan m hm 1 ^ 2)| = 8 * π / 21 * (3 * lamTan m hm 1 ^ 2) := by
      rw [abs_of_neg (by nlinarith [sq_pos_of_pos hl1])]; ring
    simp only [Fin.sum_univ_two, measAinvMat, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
    rw [a, b, measLA]; ring
  have r0 : ∑ j, |measAinvMat m hm 0 j| ≤ measLA m hm := by
    have a : |8 * π / 21 * (4 * lamTan m hm 0 * lamTan m hm 1)| =
        8 * π / 21 * (4 * lamTan m hm 0 * lamTan m hm 1) := abs_of_pos (by positivity)
    have b : |8 * π / 21 * (-3 * lamTan m hm 0 ^ 2)| = 8 * π / 21 * (3 * lamTan m hm 0 ^ 2) := by
      rw [abs_of_neg (by nlinarith [sq_pos_of_pos hl0])]; ring
    simp only [Fin.sum_univ_two, measAinvMat, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
    rw [a, b, measLA]
    have : 3 * lamTan m hm 0 ^ 2 + 4 * lamTan m hm 0 * lamTan m hm 1 ≤
        lamTan m hm 1 * (4 * lamTan m hm 0 + 3 * lamTan m hm 1) := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ 8 * π / 21)]
  have hrow : ∀ i, ((∑ j, ‖measAinvMat m hm i j‖₊ : NNReal) : ℝ) = ∑ j, |measAinvMat m hm i j| := by
    intro i
    simp [Real.norm_eq_abs]
  rw [actionAMat_inv, Matrix.linfty_opNorm_def]
  apply le_antisymm
  · have : (Finset.univ.sup fun i => ∑ j, ‖measAinvMat m hm i j‖₊) ≤ (measLA m hm).toNNReal := by
      refine Finset.sup_le fun i _ => ?_
      rw [← NNReal.coe_le_coe, hrow, Real.coe_toNNReal _ hLA.le]
      fin_cases i
      · exact r0
      · exact r1.le
    have := NNReal.coe_le_coe.2 this
    rwa [Real.coe_toNNReal _ hLA.le] at this
  · have := Finset.le_sup (f := fun i => ∑ j, ‖measAinvMat m hm i j‖₊) (Finset.mem_univ 1)
    have := NNReal.coe_le_coe.2 this
    rw [hrow, r1] at this
    exact this

end norms

/-- The inverse frequency map `ζ ↦ A⁻¹ (ζ - λ_J)` (blueprint `bpW:w7:freqcoords` (iii)). -/
def omegaTanInv (ζ : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ((actionAMat m hm)⁻¹).mulVec (ζ - fun i => lamTan m hm i)

theorem measAlin_eq_mulVec (ξ : Fin 2 → ℝ) : measAlin m hm ξ = (actionAMat m hm).mulVec ξ := by
  simp [measAlin, Matrix.toLin'_apply]

/-- `ω⁰ (A⁻¹ (ζ - λ_J)) = ζ` (blueprint `bpW:w7:freqcoords` (iii)). -/
theorem omegaTan_omegaTanInv (ζ : Fin 2 → ℝ) : omegaTan m hm (omegaTanInv m hm ζ) = ζ := by
  rw [omegaTan_eq, measAlin_eq_mulVec, omegaTanInv, Matrix.mulVec_mulVec, actionAMat_inv,
    actionAMat_mul_measAinvMat, Matrix.one_mulVec]
  abel

/-- `A⁻¹ (ω⁰ ξ - λ_J) = ξ` (blueprint `bpW:w7:freqcoords` (iii)). -/
theorem omegaTanInv_omegaTan (ξ : Fin 2 → ℝ) : omegaTanInv m hm (omegaTan m hm ξ) = ξ := by
  rw [omegaTanInv, omegaTan_eq, measAlin_eq_mulVec, add_sub_cancel_left, Matrix.mulVec_mulVec,
    actionAMat_inv, measAinvMat_mul_actionAMat, Matrix.one_mulVec]

/-- `ω⁰` is a bijection of `ℝ²` (blueprint `bpW:w7:freqcoords` (iii)). -/
theorem omegaTan_bijective : Function.Bijective (omegaTan m hm) :=
  Function.bijective_iff_has_inverse.2
    ⟨omegaTanInv m hm, omegaTanInv_omegaTan m hm, omegaTan_omegaTanInv m hm⟩

/-- `ω⁰` as an equivalence of `ℝ²` with the displayed inverse
(blueprint `bpW:w7:freqcoords` (iii)). -/
def omegaTanEquiv : (Fin 2 → ℝ) ≃ (Fin 2 → ℝ) where
  toFun := omegaTan m hm
  invFun := omegaTanInv m hm
  left_inv := omegaTanInv_omegaTan m hm
  right_inv := omegaTan_omegaTanInv m hm

/-- `ω⁰` is affine: `ω⁰ ξ = λ_J + A ξ` with the linear part `A`
(blueprint `bpW:w7:freqcoords` (iii)). -/
theorem omegaTan_eq_add_mulVec (ξ : Fin 2 → ℝ) :
    omegaTan m hm ξ = (fun i => lamTan m hm i) + (actionAMat m hm).mulVec ξ := by
  rw [omegaTan_eq, measAlin_eq_mulVec]

end KAM.Wave

end
