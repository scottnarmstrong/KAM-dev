/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib

/-!
# The rotation algebra of the spatial Poincare chart, formula (46)

Package LP-SP-ROT, `LP:MAIN L17 (533–578)`, track LP, non-frozen. Pure `3 × 3` matrix algebra on
`Fin 3 → ℝ` with Mathlib's `crossProduct` (`⨯₃`).

* `skewMatrix t` is the matrix of `w ↦ t ⨯₃ w`; `skewMatrix_mul_skewMatrix` is
  `[t]ₓ² = t tᵀ − |t|² Id`.
* `tiltRotation t c = (1 − 2|t|²) Id + 2 t tᵀ + 2c [t]ₓ` for `c² = 1 − |t|²` is orthogonal of
  determinant one and preserves the cross product.
* `incTilt`, `incCos`, `incRotation` are the objects `t`, `c`, `R` of (46).
-/

@[expose] public noncomputable section

open Matrix

namespace KAM.Planetary.Spatial

/-- The matrix of `w ↦ t ⨯₃ w`. -/
def skewMatrix (t : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, -t 2, t 1; t 2, 0, -t 0; -t 1, t 0, 0]

/-- The rotation `(1 − 2|t|²) Id + 2 t tᵀ + 2c [t]ₓ` with an abstract cosine `c`. -/
def tiltRotation (t : Fin 3 → ℝ) (c : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  (1 - 2 * (t ⬝ᵥ t)) • (1 : Matrix (Fin 3) (Fin 3) ℝ) + (2 : ℝ) • vecMulVec t t
    + (2 * c) • skewMatrix t

/-- The tilt vector `t = (u, −v, 0) / (2 √G)` of (46). -/
def incTilt (u v G : ℝ) : Fin 3 → ℝ := (1 / (2 * Real.sqrt G)) • ![u, -v, 0]

/-- The cosine `c = √(1 − |t|²)` of (46). -/
def incCos (u v G : ℝ) : ℝ := Real.sqrt (1 - incTilt u v G ⬝ᵥ incTilt u v G)

/-- The rotation `R` of (46). -/
def incRotation (u v G : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  (1 - 2 * (incTilt u v G ⬝ᵥ incTilt u v G)) • (1 : Matrix (Fin 3) (Fin 3) ℝ)
    + (2 : ℝ) • vecMulVec (incTilt u v G) (incTilt u v G)
    + (2 * incCos u v G) • skewMatrix (incTilt u v G)

lemma incRotation_eq_tiltRotation (u v G : ℝ) :
    incRotation u v G = tiltRotation (incTilt u v G) (incCos u v G) := rfl

/-- The unit vector `e₃`. -/
def e₃ : Fin 3 → ℝ := ![0, 0, 1]

/-- Embedding of a planar vector in the first two coordinates. -/
def planarEmbed (Q : Fin 2 → ℝ) : Fin 3 → ℝ := ![Q 0, Q 1, 0]

lemma skewMatrix_mulVec (t w : Fin 3 → ℝ) : skewMatrix t *ᵥ w = t ⨯₃ w := by
  ext i
  fin_cases i <;>
    simp [skewMatrix, cross_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> ring

/-- `[t]ₓ² = t tᵀ − |t|² Id`. -/
theorem skewMatrix_mul_skewMatrix (t : Fin 3 → ℝ) :
    skewMatrix t * skewMatrix t = vecMulVec t t - (t ⬝ᵥ t) • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [skewMatrix, Matrix.mul_apply, Fin.sum_univ_three, vecMulVec_apply, dotProduct] <;> ring

section Generic

variable (t : Fin 3 → ℝ) (c : ℝ)

/-- Explicit entries of `tiltRotation`. -/
lemma tiltRotation_eq :
    tiltRotation t c = !![1 - 2 * (t 1 ^ 2 + t 2 ^ 2) + 0, 2 * t 0 * t 1 - 2 * c * t 2,
        2 * t 0 * t 2 + 2 * c * t 1;
      2 * t 0 * t 1 + 2 * c * t 2, 1 - 2 * (t 0 ^ 2 + t 2 ^ 2) + 0, 2 * t 1 * t 2 - 2 * c * t 0;
      2 * t 0 * t 2 - 2 * c * t 1, 2 * t 1 * t 2 + 2 * c * t 0,
        1 - 2 * (t 0 ^ 2 + t 1 ^ 2) + 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [tiltRotation, skewMatrix, vecMulVec_apply, dotProduct, Fin.sum_univ_three] <;> ring

lemma tiltRotation_transpose_mul (hc : c ^ 2 = 1 - t ⬝ᵥ t) :
    (tiltRotation t c)ᵀ * tiltRotation t c = 1 := by
  simp only [dotProduct, Fin.sum_univ_three] at hc
  rw [tiltRotation_eq]
  ext i j
  fin_cases i <;> fin_cases j
  · simp [Matrix.mul_apply, Fin.sum_univ_three]; linear_combination (4*(t 1^2 + t 2^2)) * hc
  · simp [Matrix.mul_apply, Fin.sum_univ_three]; linear_combination (-4*t 0*t 1) * hc
  · simp [Matrix.mul_apply, Fin.sum_univ_three]; linear_combination (-4*t 0*t 2) * hc
  · simp [Matrix.mul_apply, Fin.sum_univ_three]; linear_combination (-4*t 0*t 1) * hc
  · simp [Matrix.mul_apply, Fin.sum_univ_three]; linear_combination (4*(t 0^2 + t 2^2)) * hc
  · simp [Matrix.mul_apply, Fin.sum_univ_three]; linear_combination (-4*t 1*t 2) * hc
  · simp [Matrix.mul_apply, Fin.sum_univ_three]; linear_combination (-4*t 0*t 2) * hc
  · simp [Matrix.mul_apply, Fin.sum_univ_three]; linear_combination (-4*t 1*t 2) * hc
  · simp [Matrix.mul_apply, Fin.sum_univ_three]; linear_combination (4*(t 0^2 + t 1^2)) * hc

lemma tiltRotation_det (hc : c ^ 2 = 1 - t ⬝ᵥ t) : (tiltRotation t c).det = 1 := by
  simp only [dotProduct, Fin.sum_univ_three] at hc
  rw [tiltRotation_eq]
  simp [Matrix.det_fin_three]
  linear_combination (4 * (t 0 ^ 2 + t 1 ^ 2 + t 2 ^ 2)) * hc

end Generic

/-- A proper orthogonal matrix commutes with the cross product. -/
theorem mulVec_cross_mulVec (M : Matrix (Fin 3) (Fin 3) ℝ) (h1 : Mᵀ * M = 1) (h2 : M.det = 1)
    (v w : Fin 3 → ℝ) : (M *ᵥ v) ⨯₃ (M *ᵥ w) = M *ᵥ (v ⨯₃ w) := by
  have key : ∀ x : Fin 3 → ℝ, x ⬝ᵥ ((M *ᵥ v) ⨯₃ (M *ᵥ w)) = x ⬝ᵥ (M *ᵥ (v ⨯₃ w)) := by
    intro x
    have hN : Matrix.of ![x, M *ᵥ v, M *ᵥ w] * M = Matrix.of ![Mᵀ *ᵥ x, v, w] := by
      ext a b
      change (![x, M *ᵥ v, M *ᵥ w] a ᵥ* M) b = ![Mᵀ *ᵥ x, v, w] a b
      fin_cases a
      · simp [Matrix.mulVec_transpose]
      · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
        rw [← Matrix.mulVec_transpose, Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
      · simp only [Fin.reduceFinMk, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
        rw [← Matrix.mulVec_transpose, Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
    have hd := congrArg Matrix.det hN
    rw [Matrix.det_mul, h2, mul_one] at hd
    rw [triple_product_eq_det, dotProduct_mulVec, ← Matrix.mulVec_transpose,
      triple_product_eq_det]
    exact hd
  funext i
  simpa [dotProduct_single] using key (Pi.single i 1)



end KAM.Planetary.Spatial
