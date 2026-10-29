/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Differentiating weighted Fourier coefficients

For period-one Fourier series, differentiation in coordinate `j` multiplies coefficient `k`
by `2 * π * I * k j`. We prove that this multiplier takes summable coefficients with weight
`exp (s * |k|₁)` to summable coefficients at radius `s - δ`, with bound `2 * π / (exp 1 * δ)`.

The radius `s` is a coefficient radius, corresponding to geometric strip width `s / (2 * π)`.
These are coefficient estimates; identifying the resulting series with derivatives of an
analytic function belongs to the separate Fourier-to-function bridge.
-/

@[expose] public section

noncomputable section

namespace KAM.Fourier

variable {n : ℕ}

/-- The ℓ¹ size of an integer Fourier index, as a real number. -/
def modeSize (k : Fin n → ℤ) : ℝ := ∑ j, |(k j : ℝ)|

theorem modeSize_nonneg (k : Fin n → ℤ) : 0 ≤ modeSize k := by
  exact Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem abs_coord_le_modeSize (k : Fin n → ℤ) (j : Fin n) :
    |(k j : ℝ)| ≤ modeSize k := by
  exact Finset.single_le_sum (f := fun i : Fin n => |(k i : ℝ)|)
    (fun _ _ => abs_nonneg _) (Finset.mem_univ j)

/-- Absolute summability with the exponential Fourier weight. -/
def SummableWeighted (s : ℝ) (a : (Fin n → ℤ) → ℂ) : Prop :=
  Summable fun k => ‖a k‖ * Real.exp (s * modeSize k)

/-- The weighted coefficient sum, used as a norm on `SummableWeighted` families. -/
def weightedNorm (s : ℝ) (a : (Fin n → ℤ) → ℂ) : ℝ :=
  ∑' k, ‖a k‖ * Real.exp (s * modeSize k)

/-- The period-one Fourier multiplier for differentiation in coordinate `j`. -/
def partialCoeff (j : Fin n) (a : (Fin n → ℤ) → ℂ) (k : Fin n → ℤ) : ℂ :=
  (2 * (Real.pi : ℂ) * Complex.I * (k j : ℂ)) * a k

theorem norm_partialCoeff (j : Fin n) (a : (Fin n → ℤ) → ℂ) (k : Fin n → ℤ) :
    ‖partialCoeff j a k‖ = 2 * Real.pi * |(k j : ℝ)| * ‖a k‖ := by
  simp [partialCoeff, abs_of_pos Real.pi_pos]

/-- Exponential decay absorbs the linear growth of a derivative multiplier. -/
theorem mul_exp_radius_sub_le (s x : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    x * Real.exp ((s - δ) * x) ≤
      (Real.exp (-1) / δ) * Real.exp (s * x) := by
  have h : x * Real.exp (-(δ * x)) ≤ Real.exp (-1) / δ := by
    apply (le_div_iff₀ hδ).2
    nlinarith [Real.mul_exp_neg_le_exp_neg_one (δ * x)]
  calc
    x * Real.exp ((s - δ) * x) =
        (x * Real.exp (-(δ * x))) * Real.exp (s * x) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring
    _ ≤ (Real.exp (-1) / δ) * Real.exp (s * x) :=
      mul_le_mul_of_nonneg_right h (Real.exp_nonneg _)

/-- The weighted derivative bound for a single Fourier coefficient. -/
theorem partialCoeff_weight_le (j : Fin n) (a : (Fin n → ℤ) → ℂ)
    (s : ℝ) {δ : ℝ} (hδ : 0 < δ) (k : Fin n → ℤ) :
    ‖partialCoeff j a k‖ * Real.exp ((s - δ) * modeSize k) ≤
      (2 * Real.pi / (Real.exp 1 * δ)) * (‖a k‖ * Real.exp (s * modeSize k)) := by
  rw [norm_partialCoeff]
  calc
    2 * Real.pi * |(k j : ℝ)| * ‖a k‖ * Real.exp ((s - δ) * modeSize k) ≤
        2 * Real.pi * modeSize k * ‖a k‖ * Real.exp ((s - δ) * modeSize k) := by
      gcongr
      exact abs_coord_le_modeSize k j
    _ = (2 * Real.pi * ‖a k‖) *
        (modeSize k * Real.exp ((s - δ) * modeSize k)) := by ring
    _ ≤ (2 * Real.pi * ‖a k‖) *
        ((Real.exp (-1) / δ) * Real.exp (s * modeSize k)) := by
      exact mul_le_mul_of_nonneg_left (mul_exp_radius_sub_le s (modeSize k) hδ)
        (by positivity)
    _ = (2 * Real.pi / (Real.exp 1 * δ)) *
        (‖a k‖ * Real.exp (s * modeSize k)) := by
      rw [Real.exp_neg]
      ring

/-- Differentiation preserves weighted summability after any positive radius loss. -/
theorem SummableWeighted.partialCoeff {s δ : ℝ} {a : (Fin n → ℤ) → ℂ}
    (ha : SummableWeighted s a) (hδ : 0 < δ) (j : Fin n) :
    SummableWeighted (s - δ) (partialCoeff j a) := by
  exact Summable.of_nonneg_of_le (fun _ => by positivity)
    (partialCoeff_weight_le j a s hδ) (ha.mul_left (2 * Real.pi / (Real.exp 1 * δ)))

/-- Cauchy's derivative estimate in the period-one weighted ℓ¹ coefficient norm. -/
theorem weightedNorm_partialCoeff_le {s δ : ℝ} {a : (Fin n → ℤ) → ℂ}
    (ha : SummableWeighted s a) (hδ : 0 < δ) (j : Fin n) :
    weightedNorm (s - δ) (partialCoeff j a) ≤
      (2 * Real.pi / (Real.exp 1 * δ)) * weightedNorm s a := by
  calc
    weightedNorm (s - δ) (partialCoeff j a) ≤
        ∑' k, (2 * Real.pi / (Real.exp 1 * δ)) *
          (‖a k‖ * Real.exp (s * modeSize k)) :=
      Summable.tsum_le_tsum (partialCoeff_weight_le j a s hδ)
        (ha.partialCoeff hδ j) (ha.mul_left _)
    _ = (2 * Real.pi / (Real.exp 1 * δ)) * weightedNorm s a := tsum_mul_left

end KAM.Fourier
