/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Sharp2.SmallDiv.Defs
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Rational bounds of the classical constant at `n = 2`, `τ = 1`

For `n = 2`, `τ = 1`, `c♮(δ) = √(Z (1 + 8πδ/e²))/π²` with `Z = ζ(2) - 1 = π²/6 - 1`:

* `shellConst_one`: `A₁ = 8 Z`, from `hasSum_zeta_two`;
* `cohConstC_two_one_le`: a rational test for an upper bound of `c♮(δ)`, with `3.1415 < π < 3.1416`
  and `e > 2.7182`.
-/

@[expose] public section

namespace KAM.Sharp2.Examples

open KAM.Sharp2

theorem tsum_shift_two :
    ∑' j : ℕ, (((2 : ℝ) ^ (1 : ℝ) + j)⁻¹) ^ 2 = Real.pi ^ 2 / 6 - 1 := by
  have h := (hasSum_nat_add_iff' 2).mpr hasSum_zeta_two
  have e : (fun j : ℕ => ((2 : ℝ) ^ (1 : ℝ) + j)⁻¹ ^ 2) =
      fun j : ℕ => 1 / (((j + 2 : ℕ) : ℝ)) ^ 2 := by
    funext j
    rw [Real.rpow_one, inv_pow, one_div]
    push_cast
    rw [add_comm]
  rw [e, h.tsum_eq]
  simp [Finset.sum_range_succ]

theorem shellConst_one : shellConst 1 = 8 * (Real.pi ^ 2 / 6 - 1) := by
  unfold shellConst
  rw [tsum_shift_two, show (2 * (1 : ℝ) + 1) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  norm_num

theorem gamma_three : Real.Gamma (2 * 1 + 1) = 2 := by
  rw [show (2 * (1 : ℝ) + 1) = ((2 : ℕ) : ℝ) + 1 by norm_num, Real.Gamma_nat_eq_factorial]
  norm_num

theorem sdEps_one (x : ℝ) : sdEps 1 x = 2 * x / Real.exp 1 ^ 2 := by
  unfold sdEps
  rw [gamma_three, show (2 * (1 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have := Real.exp_pos 1
  field_simp
  norm_num

/-- A rational test for an upper bound of `c♮(2, 1, δ)`. -/
theorem cohConstC_two_one_le {δ C : ℝ} (hδ : 0 ≤ δ) (hC : 0 ≤ C)
    (h : 64495 / 100000 * (1 + 8 * (31416 / 10000) * δ / (738 / 100)) ≤ (9869 / 1000 * C) ^ 2) :
    cohConstC 2 1 δ ≤ C := by
  have hpi1 := Real.pi_gt_d4
  have hpi2 := Real.pi_lt_d4
  have hpi0 : 0 < Real.pi := Real.pi_pos
  have he : (738 / 100 : ℝ) ≤ Real.exp 1 ^ 2 := by
    have := Real.exp_one_gt_d9
    nlinarith
  have hep : 0 < Real.exp 1 ^ 2 := by positivity
  set Z : ℝ := Real.pi ^ 2 / 6 - 1 with hZ
  set E : ℝ := 8 * Real.pi * δ / Real.exp 1 ^ 2 with hE
  have hZ0 : 0 ≤ Z := by rw [hZ]; nlinarith
  have hE0 : 0 ≤ E := by rw [hE]; positivity
  have hZle : Z ≤ 64495 / 100000 := by rw [hZ]; nlinarith
  have hEle : E ≤ 8 * (31416 / 10000) * δ / (738 / 100) := by
    rw [hE]
    apply div_le_div₀ (by positivity) (by nlinarith) (by norm_num) he
  have hp2 : (9869 / 1000 : ℝ) ≤ Real.pi ^ 2 := by nlinarith
  have hkey : Z * (1 + E) ≤ (Real.pi ^ 2 * C) ^ 2 := by
    have h1 : Z * (1 + E) ≤ 64495 / 100000 * (1 + 8 * (31416 / 10000) * δ / (738 / 100)) :=
      mul_le_mul hZle (by linarith) (by linarith) (by norm_num)
    have h2 : (9869 / 1000 * C) ^ 2 ≤ (Real.pi ^ 2 * C) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right hp2 hC) 2
    linarith
  have hroot : Real.sqrt (Z * (1 + E)) ≤ Real.pi ^ 2 * C :=
    Real.sqrt_le_iff.mpr ⟨by positivity, hkey⟩
  have e1 : (2 : ℝ) ^ 2 *
      (shellConst 1 * Real.Gamma (2 * 1 + 1) * (1 + sdEps 1 (4 * Real.pi * δ))) =
      8 ^ 2 * (Z * (1 + E)) := by
    rw [shellConst_one, gamma_three, sdEps_one, hE]
    ring
  unfold cohConstC
  rw [e1, Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num), Real.rpow_neg_one]
  have e2 : (2 * Real.pi)⁻¹ * (8 * Real.sqrt (Z * (1 + E))) * (4 * Real.pi)⁻¹ =
      Real.sqrt (Z * (1 + E)) / Real.pi ^ 2 := by
    field_simp
    ring
  rw [e2, div_le_iff₀ (by positivity)]
  linarith

end KAM.Sharp2.Examples

end
