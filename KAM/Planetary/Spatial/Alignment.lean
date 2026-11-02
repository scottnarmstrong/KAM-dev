/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Spatial.Rotation
public import KAM.Planetary.Spatial.Momentum

/-!
# Aligning the angular momentum with the third axis

Source: rotation invariance for the alignment in `LP:MAIN L18` (`d = 3`); track LP,
non-frozen.

`exists_rotation_unit_eq_e3`: for every unit vector `u` there is a rotation `R` (`Rᵀ R = 1`,
`det R = 1`) with `R u = e₃`.  `exists_rotation_align_angularMomentum3`: for every `z` with
`L ≠ 0` there is a rotation `R` with `spatialUnit (L (R z)) = e₃`.
-/

@[expose] public noncomputable section

namespace KAM.Planetary.Spatial

open KAM.Planetary Matrix

/-- The third basis vector. -/
def spaceE3 : Fin 3 → ℝ := ![0, 0, 1]

private theorem rot_case_one {u : Fin 3 → ℝ} (hu : spaceSq u = 1) (h : u 2 = -1) :
    ∃ R : Matrix (Fin 3) (Fin 3) ℝ, Rᵀ * R = 1 ∧ R.det = 1 ∧ R *ᵥ u = spaceE3 := by
  rw [spaceSq_def] at hu
  have h0 : u 0 = 0 := by nlinarith [sq_nonneg (u 0), sq_nonneg (u 1)]
  have h1 : u 1 = 0 := by nlinarith [sq_nonneg (u 0), sq_nonneg (u 1)]
  refine ⟨!![1, 0, 0; 0, -1, 0; 0, 0, -1], ?_, ?_, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply]
  · simp [Matrix.det_fin_three]
  · ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, spaceE3, h0, h1, h]

private theorem rot_case_two {u : Fin 3 → ℝ} (hu : spaceSq u = 1) (h : u 2 ≠ -1) :
    ∃ R : Matrix (Fin 3) (Fin 3) ℝ, Rᵀ * R = 1 ∧ R.det = 1 ∧ R *ᵥ u = spaceE3 := by
  rw [spaceSq_def] at hu
  have hge : -1 ≤ u 2 := by nlinarith [sq_nonneg (u 0), sq_nonneg (u 1)]
  have hpos : 0 < 1 + u 2 := by
    rcases lt_or_eq_of_le hge with h' | h'
    · linarith
    · exact absurd h'.symm h
  set w : ℝ := (1 + u 2)⁻¹ with hwdef
  have hw : w * (1 + u 2) = 1 := inv_mul_cancel₀ hpos.ne'
  refine ⟨!![1 - w * u 0 ^ 2, -(w * u 0 * u 1), -u 0; -(w * u 0 * u 1), 1 - w * u 1 ^ 2, -u 1;
    u 0, u 1, u 2], ?_, ?_, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply]
    · linear_combination (u 0 ^ 2 * w ^ 2 - u 2 ^ 2 * w ^ 2 + w ^ 2 - 2 * w + 1) * hu +
        ((u 1 ^ 2 + u 2 ^ 2 - 1) * (u 2 * w - w + 1)) * hw
    · linear_combination (u 0 * u 1 * w ^ 2) * hu + (-(u 0 * u 1) * (u 2 * w - w + 1)) * hw
    · linear_combination (u 0 * w) * hu + (-(u 0) * (u 2 - 1)) * hw
    · linear_combination (u 0 * u 1 * w ^ 2) * hu + (-(u 0 * u 1) * (u 2 * w - w + 1)) * hw
    · linear_combination (u 1 ^ 2 * w ^ 2) * hu + (-(u 1 ^ 2) * (u 2 * w - w + 1)) * hw
    · linear_combination (u 1 * w) * hu + (-(u 1) * (u 2 - 1)) * hw
    · linear_combination (u 0 * w) * hu + (-(u 0) * (u 2 - 1)) * hw
    · linear_combination (u 1 * w) * hu + (-(u 1) * (u 2 - 1)) * hw
    · linear_combination hu
  · simp only [Matrix.det_fin_three, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.empty_val',
      Matrix.cons_val_fin_one, Matrix.tail_cons, Matrix.head_fin_const]
    linear_combination (1 - u 2 * w) * hu + (u 2 * (u 2 - 1)) * hw
  · ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, spaceE3]
    · linear_combination (-(u 0) * w) * hu + (u 0 * (u 2 - 1)) * hw
    · linear_combination (-(u 1) * w) * hu + (u 1 * (u 2 - 1)) * hw
    · linear_combination hu

/-- For every unit vector `u` there is a rotation `R` with `R u = e₃`. -/
theorem exists_rotation_unit_eq_e3 {u : Fin 3 → ℝ} (hu : spaceSq u = 1) :
    ∃ R : Matrix (Fin 3) (Fin 3) ℝ, Rᵀ * R = 1 ∧ R.det = 1 ∧ R *ᵥ u = spaceE3 := by
  by_cases h : u 2 = -1
  · exact rot_case_one hu h
  · exact rot_case_two hu h

theorem spatialUnit_mulVec {R : Matrix (Fin 3) (Fin 3) ℝ} (hR : Rᵀ * R = 1) (L : Fin 3 → ℝ) :
    spatialUnit (R *ᵥ L) = R *ᵥ spatialUnit L := by
  simp only [spatialUnit, spaceLength_mulVec hR, Matrix.mulVec_smul]

/-- For every nonzero `L` there is a rotation `R` with `R (L/|L|) = e₃`. -/
theorem exists_rotation_align {L : Fin 3 → ℝ} (hL : L ≠ 0) :
    ∃ R : Matrix (Fin 3) (Fin 3) ℝ, Rᵀ * R = 1 ∧ R.det = 1 ∧ R *ᵥ spatialUnit L = spaceE3 := by
  have h1 : spaceSq (spatialUnit L) = 1 := by
    rw [← spaceLength_sq, spaceLength_spatialUnit hL]; norm_num
  exact exists_rotation_unit_eq_e3 h1

/-- Rotating the phase point aligns the total angular momentum with the third axis: for `L ≠ 0`
there is a rotation `R` such that `L (R z) / |L (R z)| = e₃`. -/
theorem exists_rotation_align_angularMomentum3 {n : ℕ} {z : Phase (n * 3)}
    (hL : angularMomentum3 z ≠ 0) :
    ∃ R : Matrix (Fin 3) (Fin 3) ℝ, Rᵀ * R = 1 ∧ R.det = 1 ∧
      spatialUnit (angularMomentum3 (spatialRotatePhase R z)) = spaceE3 := by
  obtain ⟨R, hR, hdet, hRu⟩ := exists_rotation_align hL
  exact ⟨R, hR, hdet, by rw [angularMomentum3_rotate hR hdet, spatialUnit_mulVec hR, hRu]⟩

end KAM.Planetary.Spatial

end
