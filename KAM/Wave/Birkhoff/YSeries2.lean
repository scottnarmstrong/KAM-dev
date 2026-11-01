/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Birkhoff.YSeries
public import KAM.Wave.Birkhoff.YSeriesNum

/-!
# Norm bound for the coefficients `V_n` (blueprint-W `bpW:w3:Yseries`, majorant calculus)

Package W3-MAIN, blueprint label `bpW:w3:Yseries`.

`norm_lieV_le`: `‖V_n‖ ρ^{2n} ≤ 4 ‖N‖ (10 q)^n` with `q = 2Cρ²`, hence (`q < 1/10`)
`Σ_n ‖V_n‖ ρ^{2n+3} < ∞` (`summable_norm_lieV`).
-/

@[expose] public noncomputable section

open Finset

namespace KAM.Wave

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  (ι : F →L[ℂ] E) (S N : ContinuousMultilinearMap ℂ (fun _ : Fin 3 => E) F)
  {C : ℝ} (hC : 0 ≤ C) (hι : ‖ι‖ ≤ 1) (hS : ‖S‖ ≤ C)

include hC hι hS in
theorem norm_lieT_le' : ‖lieT ι S‖ ≤ C := by
  refine ContinuousMultilinearMap.opNorm_le_bound hC fun v => ?_
  rw [lieT_apply]
  have hSv : ‖S v‖ ≤ C * ∏ i, ‖v i‖ :=
    (S.le_opNorm v).trans (mul_le_mul_of_nonneg_right hS (by positivity))
  calc ‖ι (S v)‖ ≤ ‖ι‖ * ‖S v‖ := ι.le_opNorm _
    _ ≤ 1 * ‖S v‖ := mul_le_mul_of_nonneg_right hι (norm_nonneg _)
    _ ≤ C * ∏ i, ‖v i‖ := by rw [one_mul]; exact hSv

omit [CompleteSpace E] [CompleteSpace F] in
theorem norm_lieBlockT_le (R : ContinuousMultilinearMap ℂ (fun _ : Fin 3 => E) F) (f : Fin 3 → ℕ)
    (P : (j : Fin 3) → ContinuousMultilinearMap ℂ (fun _ : Fin (2 * f j + 1) => E) E) (n : ℕ) :
    ‖lieBlockT R f P n‖ ≤ ‖R‖ * ∏ j, ‖P j‖ := by
  unfold lieBlockT
  by_cases h : ∑ j, (2 * f j + 1) = n
  · simp only [h, dite_true]
    exact norm_lieBlock_le R f P n h
  · simp only [h, dite_false, norm_zero]
    positivity

include hC hι hS in
theorem norm_lieNsum_le (n : ℕ) :
    ‖lieNsum ι S N n‖ ≤ ‖N‖ * (C ^ n * (((n : ℝ) + 1) * birkLieM (n + 1))) := by
  have hT := norm_lieT_le' ι S hC hι hS
  unfold lieNsum
  refine (norm_sum_le _ _).trans ?_
  have hx : ∀ x ∈ Finset.Nat.antidiagonalTuple 3 n,
      ‖lieBlockT N x (fun j => lieMulti (lieT ι S) (x j)) (2 * n + 3)‖ ≤
        ‖N‖ * (C ^ n * (birkLieM (x 0) * birkLieM (x 1) * birkLieM (x 2))) := fun x hx => by
    have hx' := Finset.Nat.mem_antidiagonalTuple.1 hx
    simp only [Fin.sum_univ_three] at hx'
    refine (norm_lieBlockT_le N x _ _).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    simp only [Fin.prod_univ_three]
    have u0 := norm_lieMulti_le (lieT ι S) hC hT (x 0)
    have u1 := norm_lieMulti_le (lieT ι S) hC hT (x 1)
    have u2 := norm_lieMulti_le (lieT ι S) hC hT (x 2)
    have m0 := birkLieM_nonneg (x 0)
    have m1 := birkLieM_nonneg (x 1)
    refine (mul_le_mul (mul_le_mul u0 u1 (norm_nonneg _) (by positivity)) u2 (norm_nonneg _)
      (by positivity)).trans (le_of_eq ?_)
    have : C ^ n = C ^ x 0 * C ^ x 1 * C ^ x 2 := by
      rw [← pow_add, ← pow_add]; congr 1; omega
    rw [this]; ring
  refine (Finset.sum_le_sum hx).trans (le_of_eq ?_)
  rw [← Finset.mul_sum, ← Finset.mul_sum, ← birkLieM_succ' n]

include hC hι hS in
theorem norm_lieV_term_le (j m n' : ℕ) (h : (2 * m + 3) + 2 * (j + 1) = n') :
    ‖((2 * (j : ℂ) + 3)) • slotMap (lieSymF ι S j)
        (ι.compContinuousMultilinearMap (lieV ι S N m)) n' h‖ ≤
      (2 * (j : ℝ) + 3) * (2 * C) ^ (j + 1) * ‖lieV ι S N m‖ := by
  rw [norm_smul]
  have hn : ‖(2 * (j : ℂ) + 3)‖ = 2 * (j : ℝ) + 3 := by
    have : (2 * (j : ℂ) + 3) = ((2 * (j : ℝ) + 3 : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [hn, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity : (0 : ℝ) ≤ 2 * (j : ℝ) + 3)
  refine (norm_slotMap_le _ _ _ _).trans ?_
  have h1 : ‖lieSymF ι S j‖ ≤ (2 * C) ^ (j + 1) := by
    refine (norm_symmMulti_le _).trans ?_
    refine (norm_lieMultiF_le ι S hC hι hS j).trans ?_
    have hm := birkLieM_le_pow (j + 1)
    calc birkLieM (j + 1) * C ^ (j + 1) ≤ 2 ^ (j + 1) * C ^ (j + 1) := by gcongr
      _ = (2 * C) ^ (j + 1) := by rw [mul_pow]
  have h2 : ‖ι.compContinuousMultilinearMap (lieV ι S N m)‖ ≤ ‖lieV ι S N m‖ := by
    refine (ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _).trans ?_
    calc ‖ι‖ * ‖lieV ι S N m‖ ≤ 1 * ‖lieV ι S N m‖ :=
          mul_le_mul_of_nonneg_right hι (norm_nonneg _)
      _ = _ := one_mul _
  exact mul_le_mul h1 h2 (norm_nonneg _) (by positivity)

include hC hι hS in
theorem norm_lieV_le (ρ : ℝ) (hρ : 0 < ρ) (n : ℕ) :
    ‖lieV ι S N n‖ * ρ ^ (2 * n) ≤ 4 * ‖N‖ * (10 * (2 * C * ρ ^ 2)) ^ n := by
  have hq0 : 0 ≤ 2 * C * ρ ^ 2 := by positivity
  have hrec : ∀ n, ‖lieV ι S N n‖ * ρ ^ (2 * n) ≤
      2 * ‖N‖ * ((n : ℝ) + 1) * (2 * C * ρ ^ 2) ^ n +
        ∑ j ∈ Finset.range n, (2 * (j : ℝ) + 3) * (2 * C * ρ ^ 2) ^ (j + 1) *
          (‖lieV ι S N (n - 1 - j)‖ * ρ ^ (2 * (n - 1 - j))) := fun n => by
    have hρn : 0 ≤ ρ ^ (2 * n) := by positivity
    have h1 : ‖lieV ι S N n‖ ≤ ‖lieNsum ι S N n‖ + ∑ j ∈ Finset.range n,
        (2 * (j : ℝ) + 3) * (2 * C) ^ (j + 1) * ‖lieV ι S N (n - 1 - j)‖ := by
      rw [lieV_eq]
      refine (norm_sub_le _ _).trans (add_le_add le_rfl ?_)
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j hj => ?_)
      have hjn : j < n := Finset.mem_range.1 hj
      simp only [hjn, dite_true]
      exact norm_lieV_term_le ι S N hC hι hS j (n - 1 - j) (2 * n + 3) (by omega)
    have h2 := norm_lieNsum_le ι S N hC hι hS n
    have hm : birkLieM (n + 1) ≤ 2 ^ (n + 1) := birkLieM_le_pow (n + 1)
    have h3 : ‖lieNsum ι S N n‖ ≤ ‖N‖ * (C ^ n * (((n : ℝ) + 1) * 2 ^ (n + 1))) :=
      h2.trans (by gcongr)
    calc ‖lieV ι S N n‖ * ρ ^ (2 * n)
        ≤ (‖lieNsum ι S N n‖ + ∑ j ∈ Finset.range n,
            (2 * (j : ℝ) + 3) * (2 * C) ^ (j + 1) * ‖lieV ι S N (n - 1 - j)‖) * ρ ^ (2 * n) :=
          mul_le_mul_of_nonneg_right h1 hρn
      _ = ‖lieNsum ι S N n‖ * ρ ^ (2 * n) + ∑ j ∈ Finset.range n,
            (2 * (j : ℝ) + 3) * (2 * C) ^ (j + 1) * ‖lieV ι S N (n - 1 - j)‖ * ρ ^ (2 * n) := by
          rw [add_mul, Finset.sum_mul]
      _ ≤ _ := by
          refine add_le_add ?_ (Finset.sum_le_sum fun j hj => le_of_eq ?_)
          · calc ‖lieNsum ι S N n‖ * ρ ^ (2 * n)
                ≤ (‖N‖ * (C ^ n * (((n : ℝ) + 1) * 2 ^ (n + 1)))) * ρ ^ (2 * n) :=
                  mul_le_mul_of_nonneg_right h3 hρn
              _ = 2 * ‖N‖ * ((n : ℝ) + 1) * (2 * C * ρ ^ 2) ^ n := by
                  rw [mul_pow, mul_pow, ← pow_mul]; ring
          · have hjn : j + 1 ≤ n := Finset.mem_range.1 hj
            have hρp : ρ ^ (2 * n) = (ρ ^ 2) ^ (j + 1) * ρ ^ (2 * (n - 1 - j)) := by
              rw [← pow_mul, ← pow_add]; congr 1; omega
            rw [hρp, mul_pow, mul_pow]
            ring
  have key := seq_bound (fun n => ‖lieV ι S N n‖ * ρ ^ (2 * n))
    (fun n => 2 * ‖N‖ * ((n : ℝ) + 1) * (2 * C * ρ ^ 2) ^ n) (2 * C * ρ ^ 2) (4 * ‖N‖) hq0
    (by positivity) (fun n => by
      have hn1 : ((n : ℝ) + 1) ≤ 10 ^ n := by
        have : n < 10 ^ n := Nat.lt_pow_self (by norm_num)
        have h2 : n + 1 ≤ 10 ^ n := this
        exact_mod_cast h2
      calc 2 * ‖N‖ * ((n : ℝ) + 1) * (2 * C * ρ ^ 2) ^ n ≤
          2 * ‖N‖ * (10 ^ n) * (2 * C * ρ ^ 2) ^ n := by gcongr
        _ = 4 * ‖N‖ / 2 * (10 * (2 * C * ρ ^ 2)) ^ n := by
            rw [mul_pow (10 : ℝ) (2 * C * ρ ^ 2) n]; ring)
    hrec n
  exact key

end KAM.Wave

end
