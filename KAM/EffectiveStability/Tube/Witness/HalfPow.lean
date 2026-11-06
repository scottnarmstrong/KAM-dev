/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.Tube.Witness.Binomial
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Half-integer powers and rational binomial coefficients (T2-CONF, N4)

Arithmetic glue between the real statements of `Witness/Binomial.lean` and the checker's exact data.

* `rpow_half_int`: for `x > 0` and `k : ℤ`, `x ^ (k / 2) = (√x) ^ k`. The Taylor coefficients
  `B^{s - m}` with `s = n/2` are therefore integer powers of `√B` (models `W`, `Y = 1/√B`,
  `Witness/Sqrt.lean`, `Witness/InvSqrt.lean`).
* `gbinom_eq_prod`: `binom(s, m) = Π_{i < m} (s - i) / m!`;
  `gbinom_ratCast`: for rational `s` it is the cast of the same rational expression, which the
  checker evaluates exactly.
-/

@[expose] public section

namespace KAM.EffectiveStability.Tube

open Finset

/-- Half-integer powers as integer powers of the square root. -/
theorem rpow_half_int {x : ℝ} (hx : 0 < x) (k : ℤ) : x ^ ((k : ℝ) / 2) = √x ^ k := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_intCast, ← Real.rpow_mul hx.le]
  ring_nf

/-- Half-integer powers, natural-number form: `x ^ (n / 2 - m) = (√x) ^ (n - 2 m)`. -/
theorem rpow_half_sub {x : ℝ} (hx : 0 < x) (n m : ℕ) :
    x ^ ((n : ℝ) / 2 - m) = √x ^ ((n : ℤ) - 2 * m) := by
  rw [← rpow_half_int hx]
  congr 1
  push_cast
  ring

/-- The falling factorial as a product. -/
theorem descPochhammer_eval_eq_prod (s : ℝ) (m : ℕ) :
    (descPochhammer ℝ m).eval s = ∏ i ∈ range m, (s - i) := by
  induction m with
  | zero => simp
  | succ m ih => rw [descPochhammer_succ_eval, ih, prod_range_succ]

/-- `binom(s, m) = Π_{i < m} (s - i) / m!`. -/
theorem gbinom_eq_prod (s : ℝ) (m : ℕ) : gbinom s m = (∏ i ∈ range m, (s - i)) / m.factorial := by
  rw [gbinom, descPochhammer_eval_eq_prod]

/-- For rational `s`, `binom(s, m)` is the cast of a rational number. -/
theorem gbinom_ratCast (q : ℚ) (m : ℕ) :
    gbinom (q : ℝ) m = (((∏ i ∈ range m, (q - i)) / m.factorial : ℚ) : ℝ) := by
  rw [gbinom_eq_prod]
  push_cast
  rfl

end KAM.EffectiveStability.Tube

end
