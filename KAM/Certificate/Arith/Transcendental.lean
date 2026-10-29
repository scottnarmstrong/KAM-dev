/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Data.Rat.Cast.CharZero

/-!
# Backend-independent rational transcendental bounds

`ratExpUp q s N` is a kernel-computable upper bound of `Real.exp q` for `q ≥ 0`: the argument is
halved `s` times, `exp (q / 2 ^ s)` is bounded by a Taylor sum of order `N` plus the
`Real.exp_bound` remainder, and the result is squared `s` times, all in `ℚ`. When the halved
argument exceeds `1` or `N = 0` the (valid but coarse) fallback `3 ^ ⌈q⌉` is used, so that the
bound holds for all parameters.
-/

@[expose] public section

namespace KAM.Certificate

/-- A kernel-computable upper bound for `exp q` (`q ≥ 0`): argument halving `s` times, Taylor
order `N`, Lagrange remainder, then `s` squarings, all in `ℚ`. -/
def ratExpUp (q : ℚ) (s N : ℕ) : ℚ :=
  if q / 2 ^ s ≤ 1 ∧ 0 < N then
    (fun r : ℚ => r * r)^[s] ((∑ m ∈ Finset.range N, (q / 2 ^ s) ^ m / (m.factorial : ℚ)) +
      (q / 2 ^ s) ^ N * (((N : ℚ) + 1) / ((N.factorial : ℚ) * N)))
  else 3 ^ ⌈q⌉₊

theorem sqIter_cast (s : ℕ) (y : ℚ) :
    (((fun r : ℚ => r * r)^[s] y : ℚ) : ℝ) = (y : ℝ) ^ 2 ^ s := by
  induction s with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    simp only [Rat.cast_mul, ih]
    rw [pow_succ 2 n, pow_mul, sq]

theorem exp_le_ratExpUp {q : ℚ} (hq : 0 ≤ q) (s N : ℕ) : Real.exp q ≤ ratExpUp q s N := by
  unfold ratExpUp
  split_ifs with h
  · obtain ⟨h1, hN⟩ := h
    set x : ℚ := q / 2 ^ s with hx
    have hx0 : 0 ≤ x := by positivity
    have hx1 : (x : ℝ) ≤ 1 := by exact_mod_cast h1
    have hb := Real.exp_bound (x := (x : ℝ))
      (by rw [abs_of_nonneg (by exact_mod_cast hx0)]; exact hx1) hN
    have hxq : (q : ℝ) = (2 ^ s : ℕ) * (x : ℝ) := by
      rw [hx]; push_cast; field_simp
    rw [sqIter_cast, hxq, Real.exp_nat_mul]
    apply pow_le_pow_left₀ (Real.exp_pos _).le
    have := (abs_le.mp hb).2
    rw [abs_of_nonneg (by exact_mod_cast hx0)] at this
    push_cast
    simp only [Nat.succ_eq_add_one] at this
    push_cast at this
    linarith
  · have h1 : Real.exp (q : ℝ) ≤ Real.exp (⌈q⌉₊ : ℝ) := by
      apply Real.exp_le_exp.mpr
      exact_mod_cast Nat.le_ceil q
    have h2 : Real.exp (⌈q⌉₊ : ℝ) = Real.exp 1 ^ ⌈q⌉₊ := by
      rw [← Real.exp_nat_mul, mul_one]
    have h3 : Real.exp 1 ≤ 3 := by linarith [Real.exp_one_lt_d9]
    have h4 : Real.exp 1 ^ ⌈q⌉₊ ≤ 3 ^ ⌈q⌉₊ := pow_le_pow_left₀ (Real.exp_pos _).le h3 _
    push_cast
    linarith

end KAM.Certificate
