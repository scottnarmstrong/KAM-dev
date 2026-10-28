/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.SecularSpectrum.LocalAnalytic.Projection

/-!
# Secular spectrum: the orthonormal eigenframe from the eigenprojections

Blueprint P, Part 9 (`stepP:p9:la-vec`).  With a column index `k j` at which the diagonal entry of
the eigenprojection `Π_j` is positive, the vector `Π_j e_{k j} / √(Π_j)_{k j,k j}` is a unit
eigenvector for `σ j`; these vectors are orthonormal, so the matrix `eigFrame` they form is
orthogonal and diagonalises `M`.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter Real Function Polynomial
open scoped BigOperators Topology Matrix.Norms.Elementwise
namespace KAM.Planetary
open KAM KAM.Kepler

namespace SecularSpectrum
open SecularForm
variable {n : ℕ}

/-- The frame whose `j`-th column is `Π_j e_{k j} / √(Π_j)_{k j, k j}`. -/
def eigFrame (M : Mat n) (σ : Vec n) (k : Fin n → Fin n) : Mat n :=
  Matrix.of fun i j => eigProj M σ j i (k j) / √(eigProj M σ j (k j) (k j))

variable {M : Mat n} {σ : Vec n} {k : Fin n → Fin n}

section Frame
variable (hM : M.transpose = M) (hσ : Function.Injective σ)
  (hch : M.charpoly = ∏ k, (Polynomial.X - Polynomial.C (σ k)))
  (hpos : ∀ j, 0 < eigProj M σ j (k j) (k j))
include hM hσ hch hpos

lemma eigFrame_transpose_mul : (eigFrame M σ k).transpose * eigFrame M σ k = 1 := by
  ext a b
  have hLt := eigProj_transpose (σ := σ) hM
  have key : ∑ i, eigProj M σ a i (k a) * eigProj M σ b i (k b) =
      (if a = b then eigProj M σ a (k a) (k b) else 0) := by
    have h := congrFun (congrFun (eigProj_mul hσ hch a b) (k a)) (k b)
    rw [Matrix.mul_apply] at h
    have hsym : ∀ i, eigProj M σ a i (k a) = eigProj M σ a (k a) i := fun i => by
      have := congrFun (congrFun (hLt a) (k a)) i
      simpa [Matrix.transpose_apply] using this
    simp_rw [hsym]
    rw [h]
    split_ifs <;> simp
  have hsa := Real.sqrt_pos.2 (hpos a)
  have hsb := Real.sqrt_pos.2 (hpos b)
  simp only [Matrix.mul_apply, Matrix.transpose_apply, eigFrame, Matrix.of_apply]
  have : ∑ i, eigProj M σ a i (k a) / √(eigProj M σ a (k a) (k a)) *
      (eigProj M σ b i (k b) / √(eigProj M σ b (k b) (k b))) =
      (∑ i, eigProj M σ a i (k a) * eigProj M σ b i (k b)) /
        (√(eigProj M σ a (k a) (k a)) * √(eigProj M σ b (k b) (k b))) := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ => by field_simp
  rw [this, key]
  by_cases hab : a = b
  · subst hab
    simp only [ite_true, Matrix.one_apply_eq]
    rw [← Real.sqrt_mul (hpos a).le, Real.sqrt_mul_self (hpos a).le]
    exact div_self (hpos a).ne'
  · simp [hab, Matrix.one_apply_ne hab]

lemma eigFrame_mul_transpose : eigFrame M σ k * (eigFrame M σ k).transpose = 1 :=
  mul_eq_one_comm.1 (eigFrame_transpose_mul hM hσ hch hpos)

omit hM hpos in
lemma mul_eigFrame : M * eigFrame M σ k = eigFrame M σ k * Matrix.diagonal σ := by
  ext i j
  have h := congrFun (congrFun (mul_eigProj hσ hch j) i) (k j)
  simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul] at h
  rw [Matrix.mul_diagonal]
  simp only [eigFrame, Matrix.of_apply, Matrix.mul_apply]
  have : ∑ l, M i l * (eigProj M σ j l (k j) / √(eigProj M σ j (k j) (k j))) =
      (∑ l, M i l * eigProj M σ j l (k j)) / √(eigProj M σ j (k j) (k j)) := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun l _ => by ring
  rw [this, h]
  ring

lemma eigFrame_diagonalises :
    M = eigFrame M σ k * Matrix.diagonal σ * (eigFrame M σ k).transpose := by
  rw [← mul_eigFrame hσ hch, Matrix.mul_assoc, eigFrame_mul_transpose hM hσ hch hpos,
    Matrix.mul_one]

end Frame

end SecularSpectrum

end KAM.Planetary
