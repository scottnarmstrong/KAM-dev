/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Fourier.Derivative
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Polynomial growth absorbed by a Fourier radius loss

The sharp scalar bound is `x ^ τ * exp (-δ * x) ≤ (τ / (exp 1 * δ)) ^ τ`,
for `x ≥ 0`, `τ ≥ 0`, and `δ > 0`. Real powers make the estimate applicable to
arbitrary Diophantine exponents. At `τ = 0`, the right side is `1`.
-/

public section

namespace KAM.Fourier

/-- The sharp bound for a real power times exponential decay, including exponent zero. -/
theorem rpow_mul_exp_neg_le {x τ δ : ℝ} (hx : 0 ≤ x) (hτ : 0 ≤ τ) (hδ : 0 < δ) :
    x ^ τ * Real.exp (-δ * x) ≤ (τ / (Real.exp 1 * δ)) ^ τ := by
  rcases eq_or_lt_of_le hτ with hτ | hτ
  · subst τ
    simp only [Real.rpow_zero, one_mul]
    exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hδ.le) hx)
  · have h := mul_exp_radius_sub_le 0 x (div_pos hδ hτ)
    simp only [zero_sub, zero_mul, Real.exp_zero, mul_one] at h
    have hp := Real.rpow_le_rpow (mul_nonneg hx (Real.exp_nonneg _)) h hτ.le
    rw [Real.mul_rpow hx (Real.exp_nonneg _), ← Real.exp_mul] at hp
    have he : (-(δ / τ) * x) * τ = -δ * x := by
      field_simp
    have hc : Real.exp (-1) / (δ / τ) = τ / (Real.exp 1 * δ) := by
      rw [Real.exp_neg]
      field_simp
    rwa [he, hc] at hp

/-- Shrinking the coefficient radius absorbs a multiplier of real polynomial growth. -/
theorem rpow_mul_exp_radius_sub_le (s : ℝ) {x τ δ : ℝ}
    (hx : 0 ≤ x) (hτ : 0 ≤ τ) (hδ : 0 < δ) :
    x ^ τ * Real.exp ((s - δ) * x) ≤
      (τ / (Real.exp 1 * δ)) ^ τ * Real.exp (s * x) := by
  calc
    x ^ τ * Real.exp ((s - δ) * x) =
        (x ^ τ * Real.exp (-δ * x)) * Real.exp (s * x) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring
    _ ≤ (τ / (Real.exp 1 * δ)) ^ τ * Real.exp (s * x) :=
      mul_le_mul_of_nonneg_right (rpow_mul_exp_neg_le hx hτ hδ) (Real.exp_nonneg _)

end KAM.Fourier
