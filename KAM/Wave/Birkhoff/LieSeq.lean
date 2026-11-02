/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Birkhoff.LieNumeric
public import Mathlib.Analysis.Normed.Module.Multilinear.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-!
# The Lie coefficients, diagonal form (blueprint-W `bpW:w3:lie-coeff`)

Package W3-FLOW, blueprint label `bpW:w3:lie-coeff`.

For a continuous trilinear map `T` on a complex Banach space `E` (in the application `T = ι ∘ S`),
`lieSeq T w k = φ_k(w)` is defined by `φ_0 = id`, `(k+1) φ_{k+1} = Σ_{a+b+c=k} T(φ_a, φ_b, φ_c)`
(the diagonal of the Lie coefficients `Φ_k`, by Leibniz identity (iv) of `bpW:w3:leibniz`).
`norm_lieSeq_le`: `‖φ_k(w)‖ ≤ m_k C^k ‖w‖^{2k+1} ≤ (2C)^k ‖w‖^{2k+1}` for `‖T‖ ≤ C`.
-/

@[expose] public noncomputable section

open Finset

namespace KAM.Wave

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (T : ContinuousMultilinearMap ℂ
  (fun _ : Fin 3 => E) E)

/-- `φ_k(w)`: `φ_0 = w`, `(k+1) φ_{k+1} = Σ_{a+b+c=k} T(φ_a, φ_b, φ_c)`. -/
def lieSeq (w : E) : ℕ → E
  | 0 => w
  | k + 1 => ((1 : ℂ) / ((k : ℂ) + 1)) •
      ∑ x ∈ (Finset.Nat.antidiagonalTuple 3 k).attach,
        T ![lieSeq w (x.1 0), lieSeq w (x.1 1), lieSeq w (x.1 2)]
decreasing_by
  all_goals
    have h := Finset.Nat.mem_antidiagonalTuple.1 x.2
    simp only [Fin.sum_univ_three] at h
    omega

theorem lieSeq_succ (w : E) (k : ℕ) :
    lieSeq T w (k + 1) = ((1 : ℂ) / ((k : ℂ) + 1)) •
      ∑ x ∈ Finset.Nat.antidiagonalTuple 3 k,
        T ![lieSeq T w (x 0), lieSeq T w (x 1), lieSeq T w (x 2)] := by
  rw [lieSeq]
  congr 1
  exact sum_attach (Finset.Nat.antidiagonalTuple 3 k)
    (fun x => T ![lieSeq T w (x 0), lieSeq T w (x 1), lieSeq T w (x 2)])

@[simp] theorem lieSeq_zero (w : E) : lieSeq T w 0 = w := by rw [lieSeq]

/-- `‖φ_k(w)‖ ≤ m_k C^k ‖w‖^{2k+1}`. -/
theorem norm_lieSeq_le {C : ℝ} (hC : 0 ≤ C) (hT : ∀ v : Fin 3 → E, ‖T v‖ ≤ C * ∏ i, ‖v i‖)
    (w : E) (k : ℕ) : ‖lieSeq T w k‖ ≤ birkLieM k * C ^ k * ‖w‖ ^ (2 * k + 1) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    cases k with
    | zero => simp [birkLieM]
    | succ k =>
      rw [lieSeq_succ, norm_smul]
      have hk : ‖((1 : ℂ) / ((k : ℂ) + 1))‖ = 1 / ((k : ℝ) + 1) := by
        rw [norm_div, norm_one]
        congr 1
        have : ((k : ℂ) + 1) = (((k : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
        rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
      rw [hk]
      have hsum : ‖∑ x ∈ Finset.Nat.antidiagonalTuple 3 k,
          T ![lieSeq T w (x 0), lieSeq T w (x 1), lieSeq T w (x 2)]‖ ≤
          ∑ x ∈ Finset.Nat.antidiagonalTuple 3 k,
            C * ((birkLieM (x 0) * C ^ x 0 * ‖w‖ ^ (2 * x 0 + 1)) *
              (birkLieM (x 1) * C ^ x 1 * ‖w‖ ^ (2 * x 1 + 1)) *
              (birkLieM (x 2) * C ^ x 2 * ‖w‖ ^ (2 * x 2 + 1))) := by
        refine (norm_sum_le _ _).trans (sum_le_sum fun x hx => ?_)
        have hx' := Finset.Nat.mem_antidiagonalTuple.1 hx
        simp only [Fin.sum_univ_three] at hx'
        refine (hT _).trans ?_
        simp only [Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_two, Matrix.cons_val_three]
        refine mul_le_mul_of_nonneg_left ?_ hC
        refine mul_le_mul (mul_le_mul (ih _ (by omega)) (ih _ (by omega)) (norm_nonneg _)
          (by have := birkLieM_nonneg (x 0); positivity)) (ih _ (by omega)) (norm_nonneg _)
          (by have := birkLieM_nonneg (x 0); have := birkLieM_nonneg (x 1); positivity)
      refine (mul_le_mul_of_nonneg_left hsum (by positivity)).trans ?_
      have e : ∀ x ∈ Finset.Nat.antidiagonalTuple 3 k,
          C * ((birkLieM (x 0) * C ^ x 0 * ‖w‖ ^ (2 * x 0 + 1)) *
              (birkLieM (x 1) * C ^ x 1 * ‖w‖ ^ (2 * x 1 + 1)) *
              (birkLieM (x 2) * C ^ x 2 * ‖w‖ ^ (2 * x 2 + 1))) =
          C ^ (k + 1) * ‖w‖ ^ (2 * k + 3) *
            (birkLieM (x 0) * birkLieM (x 1) * birkLieM (x 2)) := by
        intro x hx
        have hx' := Finset.Nat.mem_antidiagonalTuple.1 hx
        simp only [Fin.sum_univ_three] at hx'
        have : C ^ (k + 1) = C * (C ^ x 0 * C ^ x 1 * C ^ x 2) := by
          rw [← pow_add, ← pow_add, pow_succ']; congr 2; omega
        have h2 : ‖w‖ ^ (2 * k + 3) = ‖w‖ ^ (2 * x 0 + 1) * ‖w‖ ^ (2 * x 1 + 1) *
            ‖w‖ ^ (2 * x 2 + 1) := by
          rw [← pow_add, ← pow_add]; congr 1; omega
        rw [this, h2]; ring
      rw [sum_congr rfl e, ← mul_sum, ← birkLieM_succ' k]
      rw [show 2 * (k + 1) + 1 = 2 * k + 3 by ring]
      have : (1 : ℝ) / ((k : ℝ) + 1) * (C ^ (k + 1) * ‖w‖ ^ (2 * k + 3) *
          (((k : ℝ) + 1) * birkLieM (k + 1))) = birkLieM (k + 1) * C ^ (k + 1) *
            ‖w‖ ^ (2 * k + 3) := by
        field_simp
      exact this.le

end KAM.Wave

end
