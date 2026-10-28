/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PGMeasure.Setting
public import KAM.Planetary.PGMeasure.AffineSlab
public import KAM.Planetary.PGMeasure.LatticeTail

/-!
# P Part 4: slow resonances (`bpP:p4:beta-inverse`)

`beta_inverse`: a quantitative inverse bound for the transpose of a matrix with entries
bounded by `M` and determinant at least `B` in absolute value, by the adjugate formula
(no symmetry is used). Design `docs/tracks/P/design/P45-LEAN-DESIGN.md`, package P4-R0.
-/

public section

open Finset

namespace KAM.Planetary

variable {a b n : ℕ}

/-- Hadamard-free determinant bound: `|det A| ≤ n! M^n` for entries bounded by `M`. -/
theorem abs_det_le_factorial_mul_pow {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} {M : ℝ} (hA : ∀ i j, |A i j| ≤ M) :
    |A.det| ≤ (Nat.factorial (Fintype.card ι) : ℝ) * M ^ Fintype.card ι := by
  rw [Matrix.det_apply]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have h : ∀ σ : Equiv.Perm ι, |(Equiv.Perm.sign σ : ℤ) • ∏ i, A (σ i) i| ≤ M ^ Fintype.card ι := by
    intro σ
    have hp : |∏ i, A (σ i) i| ≤ M ^ Fintype.card ι := by
      rw [abs_prod]
      calc ∏ i, |A (σ i) i| ≤ ∏ _i : ι, M :=
            by gcongr with i; exact hA _ _
        _ = M ^ Fintype.card ι := by simp
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simpa [h] using hp
  refine (Finset.sum_le_sum fun σ _ => h σ).trans ?_
  simp [Fintype.card_perm]

/-- Adjugate entries are bounded by `(b-1)! M^(b-1)`. -/
theorem abs_adjugate_le {m : ℕ} {A : Matrix (Fin (m+1)) (Fin (m+1)) ℝ} {M : ℝ}
    (hA : ∀ i j, |A i j| ≤ M) (i j : Fin (m+1)) :
    |A.adjugate i j| ≤ (Nat.factorial m : ℝ) * M ^ m := by
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix, abs_mul, abs_pow, abs_neg, abs_one, one_pow,
    one_mul]
  have := abs_det_le_factorial_mul_pow (A := A.submatrix j.succAbove i.succAbove)
    (fun p q => hA _ _)
  simpa using this

theorem beta_inverse (hb : 0 < b) {T : Matrix (Fin b) (Fin b) ℝ} {B M : ℝ}
    (hB : 0 < B) (hM : 0 ≤ M) (hdet : B ≤ |T.det|) (hentries : ∀ i j, |T i j| ≤ M) :
    ∀ v : Fin b → ℝ, ‖v‖ ≤ ((Nat.factorial b : ℝ)*M^(b-1)/B)*‖T.transpose.mulVec v‖ := by
  intro v
  obtain ⟨m, rfl⟩ : ∃ m, b = m + 1 := ⟨b - 1, by omega⟩
  set w := T.transpose.mulVec v with hw
  have hdetT : |T.transpose.det| = |T.det| := by rw [Matrix.det_transpose]
  have hv : ∀ i, T.det * v i = (T.transpose.adjugate.mulVec w) i := by
    intro i
    have : T.transpose.adjugate.mulVec w = T.transpose.det • v := by
      rw [hw, Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
    rw [this]; simp [Matrix.det_transpose]
  have hentT : ∀ i j, |T.transpose i j| ≤ M := fun i j => hentries j i
  have hw0 : 0 ≤ ‖w‖ := norm_nonneg _
  have hcoef : 0 ≤ (Nat.factorial (m+1) : ℝ) * M ^ (m+1-1) / B := by positivity
  have hdetpos : 0 < |T.det| := lt_of_lt_of_le hB hdet
  have key : ∀ i, |T.det| * |v i| ≤ (Nat.factorial (m+1) : ℝ) * M ^ (m+1-1) * ‖w‖ := by
    intro i
    rw [← abs_mul, hv i, Matrix.mulVec, dotProduct]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ j, |T.transpose.adjugate i j * w j|
        ≤ ∑ _j : Fin (m+1), (Nat.factorial m : ℝ) * M ^ m * ‖w‖ := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [abs_mul]
          exact mul_le_mul (abs_adjugate_le hentT i j) (by simpa using norm_le_pi_norm w j)
            (abs_nonneg _) (by positivity)
      _ = (Nat.factorial (m+1) : ℝ) * M ^ (m+1-1) * ‖w‖ := by
          simp [Nat.factorial_succ]; ring
  rw [div_mul_eq_mul_div]
  refine (pi_norm_le_iff_of_nonneg (r := (Nat.factorial (m+1) : ℝ) * M ^ (m+1-1) * ‖w‖ / B)
    (by positivity)).2 fun i => ?_
  rw [Real.norm_eq_abs, le_div_iff₀ hB]
  have h1 : B * |v i| ≤ |T.det| * |v i| := mul_le_mul_of_nonneg_right hdet (abs_nonneg _)
  nlinarith [key i]

end KAM.Planetary
