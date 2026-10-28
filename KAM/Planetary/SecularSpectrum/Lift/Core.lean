/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.SecularSpectrum.Lift.Basic

/-!
# Secular spectrum: the algebraic core of the lift's symplecticity

Blueprint P, Part 9 (`stepP:p9:lift-form`, `stepP:p9:lift-mc`): the matrix identity that remains
after the derivative of the lift is written out.  Here `R` is orthogonal, `Ru, Rv` are
derivatives of `R` along two directions (so `R Ruᵀ = -(Ru Rᵀ)`), and the identity is the
slow-block part of the symplectic form against the angle-shift part, whose second-derivative
terms cancel by the symmetry of `H`.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter Real Function
open scoped BigOperators Topology Matrix.Norms.Elementwise
namespace KAM.Planetary
open KAM KAM.Kepler

namespace SecularSpectrum
open SecularForm
variable {n : ℕ}

section Core

lemma dot_mulVec_swap (a b : Vec n) (M : Mat n) :
    a ⬝ᵥ (M.mulVec b) = b ⬝ᵥ (M.transpose.mulVec a) := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, dotProduct_comm]

lemma dot_transpose_mulVec (M : Mat n) (a y : Vec n) :
    (M.transpose.mulVec a) ⬝ᵥ y = a ⬝ᵥ (M.mulVec y) := by
  rw [dot_mulVec_swap a y M, dotProduct_comm]

lemma dot_transpose_transpose (M N : Mat n) (a b : Vec n) :
    (M.transpose.mulVec a) ⬝ᵥ (N.transpose.mulVec b) = a ⬝ᵥ ((M * N.transpose).mulVec b) := by
  rw [dot_transpose_mulVec, Matrix.mulVec_mulVec]

lemma core_identity (R Ru Rv H : Mat n) (hRR : R * R.transpose = 1)
    (hu : R * Ru.transpose = -(Ru * R.transpose)) (hv : R * Rv.transpose = -(Rv * R.transpose))
    (p q dpu dpv dqu dqv : Vec n) :
    ((R.transpose.mulVec dpu + Ru.transpose.mulVec p) ⬝ᵥ
        (R.transpose.mulVec dqv + Rv.transpose.mulVec q) -
      (R.transpose.mulVec dqu + Ru.transpose.mulVec q) ⬝ᵥ
        (R.transpose.mulVec dpv + Rv.transpose.mulVec p)) - (dpu ⬝ᵥ dqv - dqu ⬝ᵥ dpv) =
    (p ⬝ᵥ (((H * R.transpose + Ru * Rv.transpose).mulVec q) +
        (Ru * R.transpose).mulVec dqv) + dpv ⬝ᵥ ((Ru * R.transpose).mulVec q)) -
    (p ⬝ᵥ (((H * R.transpose + Rv * Ru.transpose).mulVec q) +
        (Rv * R.transpose).mulVec dqu) + dpu ⬝ᵥ ((Rv * R.transpose).mulVec q)) := by
  have hAu : (Ru * R.transpose).transpose = -(Ru * R.transpose) := by
    rw [Matrix.transpose_mul, Matrix.transpose_transpose, hu]
  have hAv : (Rv * R.transpose).transpose = -(Rv * R.transpose) := by
    rw [Matrix.transpose_mul, Matrix.transpose_transpose, hv]
  have hB : (Ru * Rv.transpose).transpose = Rv * Ru.transpose := by
    rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  have e1 : (R.transpose.mulVec dpu) ⬝ᵥ (R.transpose.mulVec dqv) = dpu ⬝ᵥ dqv := by
    rw [dot_transpose_transpose, hRR, Matrix.one_mulVec]
  have e2 : (R.transpose.mulVec dpu) ⬝ᵥ (Rv.transpose.mulVec q) =
      -(dpu ⬝ᵥ ((Rv * R.transpose).mulVec q)) := by
    rw [dot_transpose_transpose, hv, Matrix.neg_mulVec, dotProduct_neg]
  have e3 : (Ru.transpose.mulVec p) ⬝ᵥ (R.transpose.mulVec dqv) =
      p ⬝ᵥ ((Ru * R.transpose).mulVec dqv) := dot_transpose_transpose _ _ _ _
  have e4 : (Ru.transpose.mulVec p) ⬝ᵥ (Rv.transpose.mulVec q) =
      p ⬝ᵥ ((Ru * Rv.transpose).mulVec q) := dot_transpose_transpose _ _ _ _
  have f1 : (R.transpose.mulVec dqu) ⬝ᵥ (R.transpose.mulVec dpv) = dqu ⬝ᵥ dpv := by
    rw [dot_transpose_transpose, hRR, Matrix.one_mulVec]
  have f2 : (R.transpose.mulVec dqu) ⬝ᵥ (Rv.transpose.mulVec p) =
      -(dqu ⬝ᵥ ((Rv * R.transpose).mulVec p)) := by
    rw [dot_transpose_transpose, hv, Matrix.neg_mulVec, dotProduct_neg]
  have f3 : (Ru.transpose.mulVec q) ⬝ᵥ (R.transpose.mulVec dpv) =
      q ⬝ᵥ ((Ru * R.transpose).mulVec dpv) := dot_transpose_transpose _ _ _ _
  have f4 : (Ru.transpose.mulVec q) ⬝ᵥ (Rv.transpose.mulVec p) =
      q ⬝ᵥ ((Ru * Rv.transpose).mulVec p) := dot_transpose_transpose _ _ _ _
  have g2 : dqu ⬝ᵥ ((Rv * R.transpose).mulVec p) = -(p ⬝ᵥ ((Rv * R.transpose).mulVec dqu)) := by
    rw [dot_mulVec_swap, hAv, Matrix.neg_mulVec, dotProduct_neg]
  have g3 : q ⬝ᵥ ((Ru * R.transpose).mulVec dpv) = -(dpv ⬝ᵥ ((Ru * R.transpose).mulVec q)) := by
    rw [dot_mulVec_swap, hAu, Matrix.neg_mulVec, dotProduct_neg]
  have g4 : q ⬝ᵥ ((Ru * Rv.transpose).mulVec p) = p ⬝ᵥ ((Rv * Ru.transpose).mulVec q) := by
    rw [dot_mulVec_swap, hB]
  simp only [Matrix.add_mulVec, dotProduct_add, add_dotProduct, e1, e2, e3, e4, f1, f2, f3, f4,
    g2, g3, g4]
  ring

end Core

end SecularSpectrum

end KAM.Planetary

end
