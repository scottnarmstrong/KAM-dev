/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib

/-!
# P Part 5: block inversion (`stepP:p5:fi-inv`)

`schur_inverse_blocks`: the inverse of a complex block matrix whose top-left block and Schur
complement are invertible, in the four-block form used for the row-wise bounds of `freq_inj`.
Design `docs/tracks/P/design/P45-LEAN-DESIGN.md`, package P5-FI.
-/

@[expose] public noncomputable section

namespace KAM.Planetary

variable {a b : ℕ}

/-- Identifies the missing row-wise operator bounds after Schur complement inversion. -/
theorem schur_inverse_blocks {A : Matrix (Fin a) (Fin a) ℂ}
    {B : Matrix (Fin a) (Fin b) ℂ} {C : Matrix (Fin b) (Fin a) ℂ}
    {D : Matrix (Fin b) (Fin b) ℂ} (hA : IsUnit A.det) (hS : IsUnit (D-C*A⁻¹*B).det) :
    (Matrix.fromBlocks A B C D)⁻¹ =
      Matrix.fromBlocks (A⁻¹+A⁻¹*B*(D-C*A⁻¹*B)⁻¹*C*A⁻¹)
        (-A⁻¹*B*(D-C*A⁻¹*B)⁻¹) (-(D-C*A⁻¹*B)⁻¹*C*A⁻¹) ((D-C*A⁻¹*B)⁻¹) := by
  let _ : Invertible A := Matrix.invertibleOfIsUnitDet A hA
  have hS' : IsUnit (D - C * ⅟A * B).det := by rwa [Matrix.invOf_eq_nonsing_inv]
  let _ : Invertible (D - C * ⅟A * B) := Matrix.invertibleOfIsUnitDet _ hS'
  let _ := Matrix.fromBlocks₁₁Invertible A B C D
  have h := Matrix.invOf_fromBlocks₁₁_eq A B C D
  simp only [Matrix.invOf_eq_nonsing_inv] at h
  rw [h]
  simp only [Matrix.neg_mul]

end KAM.Planetary

end
