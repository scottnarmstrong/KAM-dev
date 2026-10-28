/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.SecularSpectrum.LocalAnalytic.Existence

/-!
# Secular spectrum: uniqueness of the local analytic spectral decomposition

Blueprint P, Part 9 (`bpP:p9:local-analytic`, `stepP:p9:la-so`): on a connected open set the
increasing eigenvalue branches are unique and two analytic `SO(n)` eigenframes differ by a
constant diagonal sign matrix of determinant one.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter Real Function Polynomial
open scoped BigOperators Topology Matrix.Norms.Elementwise
namespace KAM.Planetary
open KAM KAM.Kepler

namespace SecularSpectrum
open SecularForm
variable {n d : ℕ}

section Pointwise
variable {R S : Mat n} {s t : Vec n}

/-- Two strictly increasing spectra of the same orthogonally diagonalised matrix agree. -/
lemma eq_of_conj_diagonal (hR : R.transpose * R = 1) (hS : S.transpose * S = 1)
    (hs : StrictMono s) (ht : StrictMono t)
    (h : R * Matrix.diagonal s * R.transpose = S * Matrix.diagonal t * S.transpose) : s = t := by
  have hcp : ∀ (R : Mat n) (s : Vec n), R.transpose * R = 1 →
      (R * Matrix.diagonal s * R.transpose).charpoly = ∏ i, (X - C (s i)) := by
    intro R s hR
    rw [Matrix.mul_assoc, Matrix.charpoly_mul_comm, Matrix.mul_assoc, hR, Matrix.mul_one,
      Matrix.charpoly_diagonal]
  have hc : ∏ i, (X - C (s i)) = (∏ i, (X - C (t i)) : ℝ[X]) := by
    rw [← hcp R s hR, ← hcp S t hS, h]
  have hsub : ∀ {s t : Vec n}, (∏ i, (X - C (s i)) : ℝ[X]) = ∏ i, (X - C (t i)) →
      Set.range s ⊆ Set.range t := by
    intro s t hc x ⟨j, hj⟩
    have : ((∏ i, (X - C (t i)) : ℝ[X])).eval x = 0 := by
      rw [← hc, eval_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hj])
    rw [eval_prod] at this
    obtain ⟨i, -, hi⟩ := Finset.prod_eq_zero_iff.1 this
    exact ⟨i, by simpa [sub_eq_zero] using (sub_eq_zero.1 (by simpa using hi)).symm⟩
  exact Set.range_injOn_strictMono_of_wellFoundedLT hs ht (Set.Subset.antisymm (hsub hc) (hsub hc.symm))

/-- Two orthogonal eigenframes of a simple spectrum differ by a diagonal sign matrix. -/
lemma frame_eq_signs (hR : isSO R) (hS : isSO S) (hs : Function.Injective s)
    (h : R * Matrix.diagonal s * R.transpose = S * Matrix.diagonal s * S.transpose) :
    ∃ q : Vec n, R.transpose * S = Matrix.diagonal q ∧ (∀ i, q i = 1 ∨ q i = -1) ∧
      ∏ i, q i = 1 ∧ S = R * Matrix.diagonal q := by
  have hRR : R * R.transpose = 1 := mul_eq_one_comm.1 hR.1
  set Q := R.transpose * S with hQ
  have hcomm : Matrix.diagonal s * Q = Q * Matrix.diagonal s := by
    have h1 := congrArg (fun A => R.transpose * A * S) h
    have e1 : R.transpose * (R * Matrix.diagonal s * R.transpose) * S = Matrix.diagonal s * Q := by
      simp only [hQ, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc R.transpose R, hR.1, Matrix.one_mul]
    have e2 : R.transpose * (S * Matrix.diagonal s * S.transpose) * S = Q * Matrix.diagonal s := by
      simp only [hQ, Matrix.mul_assoc]
      rw [hS.1, Matrix.mul_one]
    rw [← e1, ← e2, h1]
  have hdiag : Q = Matrix.diagonal (fun i => Q i i) := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp
    · have := congrFun (congrFun hcomm i) j
      simp only [Matrix.diagonal_mul, Matrix.mul_diagonal] at this
      have h0 : Q i j = 0 := by
        have : Q i j * (s i - s j) = 0 := by linarith
        rcases mul_eq_zero.1 this with h | h
        · exact h
        · exact absurd (hs (sub_eq_zero.1 h)) hij
      simp [h0, Matrix.diagonal_apply_ne _ hij]
  set q : Vec n := fun i => Q i i with hq
  have hQo : Q.transpose * Q = 1 := by
    simp only [hQ, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc R R.transpose, hRR, Matrix.one_mul, hS.1]
  refine ⟨q, hdiag, fun i => ?_, ?_, ?_⟩
  · have := congrFun (congrFun hQo i) i
    rw [hdiag, Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal] at this
    simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq] at this
    exact mul_self_eq_one_iff.1 this
  · have := congrArg Matrix.det hdiag
    rw [Matrix.det_diagonal, hQ, Matrix.det_mul, Matrix.det_transpose, hR.2, hS.2] at this
    simpa using this.symm
  · rw [← hdiag, hQ, ← Matrix.mul_assoc, hRR, Matrix.one_mul]

end Pointwise

end SecularSpectrum

end KAM.Planetary
