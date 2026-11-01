/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Spatial.Vector

/-!
# Rotations of `Fin 3 → ℝ`: dot, length and cross product equivariance

Package LP-SP-MODEL, rotation invariance for `LP:MAIN L18` alignment (support for
`LP:MAIN §1 (9–93)`, `d = 3`); track LP, non-frozen; the statement surface is proposed in
docs/tracks/LP/FREEZE-PROPOSAL.md.

A rotation is a `Matrix (Fin 3) (Fin 3) ℝ` with `Rᵀ * R = 1` and `R.det = 1`, acting by `mulVec`
(Mathlib's standard 3-vector API: `dotProduct`, `crossProduct`, `mulVec`).  Dot product and length
are preserved by orthogonal `R`; the cross product is equivariant, `R (a × b) = R a × R b`, for
`det R = 1`.
-/

@[expose] public noncomputable section

namespace KAM.Planetary.Spatial

open Matrix

theorem spaceDot_sub_left (a b w : Fin 3 → ℝ) :
    spaceDot (a - b) w = spaceDot a w - spaceDot b w := by
  simp only [spaceDot_def, Pi.sub_apply]; ring

variable {R : Matrix (Fin 3) (Fin 3) ℝ}

theorem mul_transpose_eq_one (hR : Rᵀ * R = 1) : R * Rᵀ = 1 := mul_eq_one_comm.mp hR

/-- Orthogonal matrices preserve the Euclidean dot product. -/
theorem spaceDot_mulVec (hR : Rᵀ * R = 1) (v w : Fin 3 → ℝ) :
    spaceDot (R *ᵥ v) (R *ᵥ w) = spaceDot v w := by
  rw [spaceDot_eq_dotProduct, spaceDot_eq_dotProduct, Matrix.dotProduct_mulVec,
    ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec, hR, Matrix.one_mulVec]

theorem spaceSq_mulVec (hR : Rᵀ * R = 1) (v : Fin 3 → ℝ) : spaceSq (R *ᵥ v) = spaceSq v := by
  rw [spaceSq_eq_spaceDot, spaceSq_eq_spaceDot, spaceDot_mulVec hR]

theorem spaceLength_mulVec (hR : Rᵀ * R = 1) (v : Fin 3 → ℝ) :
    spaceLength (R *ᵥ v) = spaceLength v := by
  unfold spaceLength
  rw [spaceSq_mulVec hR]

/-- The triple product as a determinant. -/
theorem spaceDot_cross_eq_det (a b c : Fin 3 → ℝ) :
    spaceDot (spaceCross a b) c = Matrix.det !![a 0, a 1, a 2; b 0, b 1, b 2; c 0, c 1, c 2] := by
  rw [spaceCross_eq_crossProduct, spaceDot_eq_dotProduct, dotProduct_comm,
    triple_product_permutation, triple_product_eq_det]
  congr 1
  ext i j; fin_cases i <;> fin_cases j <;> simp

/-- The matrix with rows `R a, R b, R c` is `![a,b,c] * Rᵀ`. -/
theorem rows_mulVec (R : Matrix (Fin 3) (Fin 3) ℝ) (a b c : Fin 3 → ℝ) :
    !![(R *ᵥ a) 0, (R *ᵥ a) 1, (R *ᵥ a) 2; (R *ᵥ b) 0, (R *ᵥ b) 1, (R *ᵥ b) 2;
        (R *ᵥ c) 0, (R *ᵥ c) 1, (R *ᵥ c) 2] =
      !![a 0, a 1, a 2; b 0, b 1, b 2; c 0, c 1, c 2] * Rᵀ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> ring

/-- Rotations (`Rᵀ R = 1`, `det R = 1`) commute with the cross product: `R (a × b) = R a × R b`. -/
theorem mulVec_spaceCross (hR : Rᵀ * R = 1) (hdet : R.det = 1) (a b : Fin 3 → ℝ) :
    R *ᵥ spaceCross a b = spaceCross (R *ᵥ a) (R *ᵥ b) := by
  have hkey : ∀ c, spaceDot (spaceCross (R *ᵥ a) (R *ᵥ b)) (R *ᵥ c) =
      spaceDot (R *ᵥ spaceCross a b) (R *ᵥ c) := by
    intro c
    rw [spaceDot_mulVec hR, spaceDot_cross_eq_det, spaceDot_cross_eq_det, rows_mulVec,
      Matrix.det_mul, Matrix.det_transpose, hdet, mul_one]
  set d := spaceCross (R *ᵥ a) (R *ᵥ b) - R *ᵥ spaceCross a b with hd
  have hRRt := mul_transpose_eq_one hR
  have h0 : spaceDot d d = 0 := by
    have := hkey (Rᵀ *ᵥ d)
    rw [Matrix.mulVec_mulVec, hRRt, Matrix.one_mulVec] at this
    have h2 : spaceDot d d = spaceDot (spaceCross (R *ᵥ a) (R *ᵥ b)) d -
        spaceDot (R *ᵥ spaceCross a b) d := by
      rw [← spaceDot_sub_left]
    rw [h2, this, sub_self]
  have : d = 0 := spaceSq_eq_zero_iff.mp (by rw [spaceSq_eq_spaceDot]; exact h0)
  exact (sub_eq_zero.mp this).symm

end KAM.Planetary.Spatial

end
