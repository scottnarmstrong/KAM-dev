/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Birkhoff.LiePlusNum

/-!
# A numerical recursion bound (blueprint-W `bpW:w3:Yseries`, majorant)

Package W3-MAIN, blueprint label `bpW:w3:Yseries`.

`seq_bound`: if `b_n ≤ ν_n + Σ_{j<n} (2j+3) q^{j+1} b_{n-1-j}` with `ν_n ≤ (K/2)(10q)^n`,
`0 ≤ b_n`, then `b_n ≤ K (10 q)^n`.
-/

@[expose] public noncomputable section

open Finset

namespace KAM.Wave

theorem summable_odd_geom (q : ℝ) (h0 : 0 ≤ q) (h1 : q < 1) :
    Summable fun k : ℕ => (2 * ((k + 1 : ℕ) : ℝ) + 1) * q ^ (k + 1) := by
  have hs : Summable fun k : ℕ => ((k : ℝ)) * q ^ k := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one 1 (r := q)
      (by rw [Real.norm_eq_abs, abs_of_nonneg h0]; exact h1)
  have hg : Summable fun k : ℕ => q ^ k := summable_geometric_of_lt_one h0 h1
  have h' := (summable_nat_add_iff 1).2 ((hs.mul_left 2).add hg)
  refine h'.congr fun k => ?_
  push_cast; ring

theorem odd_geom_partial_le (n : ℕ) :
    ∑ j ∈ Finset.range n, (2 * (j : ℝ) + 3) * (1 / 10 : ℝ) ^ (j + 1) ≤ 1 / 2 := by
  have h0 : (0 : ℝ) ≤ 1 / 10 := by norm_num
  have hsum := summable_odd_geom (1 / 10) h0 (by norm_num)
  have hle := (geom_sums (1 / 10) h0 le_rfl).2.2
  calc ∑ j ∈ Finset.range n, (2 * (j : ℝ) + 3) * (1 / 10 : ℝ) ^ (j + 1)
      = ∑ j ∈ Finset.range n, (2 * ((j + 1 : ℕ) : ℝ) + 1) * (1 / 10 : ℝ) ^ (j + 1) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        push_cast; ring
    _ ≤ ∑' k : ℕ, (2 * ((k + 1 : ℕ) : ℝ) + 1) * (1 / 10 : ℝ) ^ (k + 1) :=
        hsum.sum_le_tsum _ fun _ _ => by positivity
    _ ≤ 5 * (1 / 10) := hle
    _ = 1 / 2 := by norm_num

theorem seq_bound (b ν : ℕ → ℝ) (q K : ℝ) (hq0 : 0 ≤ q) (hK : 0 ≤ K)
    (hν : ∀ n, ν n ≤ K / 2 * (10 * q) ^ n)
    (hrec : ∀ n, b n ≤ ν n +
      ∑ j ∈ Finset.range n, (2 * (j : ℝ) + 3) * q ^ (j + 1) * b (n - 1 - j)) :
    ∀ n, b n ≤ K * (10 * q) ^ n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have hterm : ∀ j ∈ Finset.range n, (2 * (j : ℝ) + 3) * q ^ (j + 1) * b (n - 1 - j) ≤
        K * (10 * q) ^ n * ((2 * (j : ℝ) + 3) * (1 / 10 : ℝ) ^ (j + 1)) := fun j hj => by
      have hjn : j + 1 ≤ n := Finset.mem_range.1 hj
      have h1 := ih (n - 1 - j) (by omega)
      have hpow : (10 * q) ^ n = (10 * q) ^ (j + 1) * (10 * q) ^ (n - 1 - j) := by
        rw [← pow_add]; congr 1; omega
      have hpos : 0 ≤ (2 * (j : ℝ) + 3) * q ^ (j + 1) := by positivity
      calc (2 * (j : ℝ) + 3) * q ^ (j + 1) * b (n - 1 - j)
          ≤ (2 * (j : ℝ) + 3) * q ^ (j + 1) * (K * (10 * q) ^ (n - 1 - j)) :=
            mul_le_mul_of_nonneg_left h1 hpos
        _ = K * (10 * q) ^ n * ((2 * (j : ℝ) + 3) * (1 / 10 : ℝ) ^ (j + 1)) := by
            rw [hpow, mul_pow (10 : ℝ) q (j + 1), one_div, inv_pow]
            field_simp
    have hsum : ∑ j ∈ Finset.range n, (2 * (j : ℝ) + 3) * q ^ (j + 1) * b (n - 1 - j) ≤
        K * (10 * q) ^ n * (1 / 2) := by
      refine (Finset.sum_le_sum hterm).trans ?_
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (odd_geom_partial_le n) (by positivity)
    have := hrec n
    have := hν n
    nlinarith [hsum]

end KAM.Wave

end
