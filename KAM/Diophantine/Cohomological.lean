/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Diophantine.Basic
public import KAM.Fourier.ExponentialDecay
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The Fourier cohomological equation

For nonresonant `ω`, division by `2π i (k · ω)` solves the coefficient equation
`ω · ∂u = g - average g`, uniquely after setting the zero coefficient to zero.
Under the Diophantine condition, the solution preserves weighted summability
after any positive radius loss, with bound `(τ / (eδ)) ^ τ / (2πγ)`.

These are coefficient-space results. The analytic-function bridge is separate.
Our operator has the opposite sign to `L_ω` in HL19 §4.1, equations (4.1)-(4.2).
-/

@[expose] public section

noncomputable section

namespace KAM.Diophantine

open Fourier

variable {n : ℕ}

/-- The period-one Fourier symbol of the directional derivative `ω · ∂`. -/
def flowMultiplier (ω : Fin n → ℝ) (k : Fin n → ℤ) : ℂ :=
  2 * (Real.pi : ℂ) * Complex.I * (frequencyDot ω k : ℂ)

/-- Directional differentiation of Fourier coefficients. -/
def directionalCoeff (ω : Fin n → ℝ) (a : (Fin n → ℤ) → ℂ) (k : Fin n → ℤ) : ℂ :=
  flowMultiplier ω k * a k

/-- Remove the average (the zero Fourier coefficient). -/
def removeAverage (a : (Fin n → ℤ) → ℂ) (k : Fin n → ℤ) : ℂ :=
  if k = 0 then 0 else a k

/-- The zero-average coefficient solution of the cohomological equation. -/
def solve (ω : Fin n → ℝ) (a : (Fin n → ℤ) → ℂ) (k : Fin n → ℤ) : ℂ :=
  if k = 0 then 0 else a k / flowMultiplier ω k

@[simp] theorem flowMultiplier_zero (ω : Fin n → ℝ) : flowMultiplier ω 0 = 0 := by
  simp [flowMultiplier]

theorem norm_flowMultiplier (ω : Fin n → ℝ) (k : Fin n → ℤ) :
    ‖flowMultiplier ω k‖ = 2 * Real.pi * |frequencyDot ω k| := by
  simp [flowMultiplier, abs_of_pos Real.pi_pos]

theorem Nonresonant.flowMultiplier_ne_zero {ω : Fin n → ℝ} (hω : Nonresonant ω)
    {k : Fin n → ℤ} (hk : k ≠ 0) : flowMultiplier ω k ≠ 0 := by
  apply norm_pos_iff.mp
  rw [norm_flowMultiplier]
  exact mul_pos (by positivity) (abs_pos.mpr (hω k hk))

/-- The multiplier agrees with the sum of the coordinate derivatives. -/
theorem directionalCoeff_eq_sum (ω : Fin n → ℝ) (a : (Fin n → ℤ) → ℂ)
    (k : Fin n → ℤ) :
    directionalCoeff ω a k = ∑ j, (ω j : ℂ) * partialCoeff j a k := by
  simp only [directionalCoeff, flowMultiplier, frequencyDot, Complex.ofReal_sum,
    Complex.ofReal_mul, partialCoeff, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  push_cast
  ring

@[simp] theorem solve_zero_mode (ω : Fin n → ℝ) (a : (Fin n → ℤ) → ℂ) :
    solve ω a 0 = 0 := by
  simp [solve]

/-- The constructed coefficients solve the cohomological equation exactly. -/
theorem directionalCoeff_solve {ω : Fin n → ℝ} (hω : Nonresonant ω)
    (a : (Fin n → ℤ) → ℂ) : directionalCoeff ω (solve ω a) = removeAverage a := by
  funext k
  by_cases hk : k = 0
  · simp [directionalCoeff, removeAverage, hk]
  · simp [directionalCoeff, solve, removeAverage, hk,
      mul_div_cancel₀ _ (hω.flowMultiplier_ne_zero hk)]

/-- Nonresonance gives uniqueness once the zero coefficient is fixed. -/
theorem solve_unique {ω : Fin n → ℝ} (hω : Nonresonant ω)
    {a u : (Fin n → ℤ) → ℂ} (hu0 : u 0 = 0)
    (hu : directionalCoeff ω u = removeAverage a) : u = solve ω a := by
  funext k
  by_cases hk : k = 0
  · simpa [hk] using hu0
  · have he := congrFun hu k
    simp only [directionalCoeff, removeAverage, ite_eq_right hk] at he
    rw [solve, ite_eq_right hk]
    apply (eq_div_iff (hω.flowMultiplier_ne_zero hk)).2
    simpa only [mul_comm] using he

/-- The inverse small-divisor estimate for one nonzero coefficient. -/
theorem norm_solve_le {ω : Fin n → ℝ} {γ τ : ℝ}
    (hω : Condition ω γ τ) (hγ : 0 < γ)
    (a : (Fin n → ℤ) → ℂ) {k : Fin n → ℤ} (hk : k ≠ 0) :
    ‖solve ω a k‖ ≤ (1 / (2 * Real.pi * γ)) * (‖a k‖ * modeSize k ^ τ) := by
  rw [solve, ite_eq_right hk, norm_div, norm_flowMultiplier]
  have hp : 0 < modeSize k ^ τ := Real.rpow_pos_of_pos (modeSize_pos hk) τ
  have hd : 0 < 2 * Real.pi * (γ / modeSize k ^ τ) := by positivity
  calc
    ‖a k‖ / (2 * Real.pi * |frequencyDot ω k|) ≤
        ‖a k‖ / (2 * Real.pi * (γ / modeSize k ^ τ)) := by
      apply div_le_div_of_nonneg_left (norm_nonneg _) hd
      exact mul_le_mul_of_nonneg_left (hω k hk) (by positivity)
    _ = (1 / (2 * Real.pi * γ)) * (‖a k‖ * modeSize k ^ τ) := by
      field_simp

/-- The explicit cohomological estimate constant; exponent zero gives `1 / (2πγ)`. -/
def solveBound (γ τ δ : ℝ) : ℝ :=
  (1 / (2 * Real.pi * γ)) * (τ / (Real.exp 1 * δ)) ^ τ

theorem solveBound_nonneg {γ τ δ : ℝ} (hγ : 0 < γ) (hτ : 0 ≤ τ) (hδ : 0 < δ) :
    0 ≤ solveBound γ τ δ := by
  unfold solveBound
  positivity

@[simp] theorem solveBound_zero_exponent (γ δ : ℝ) :
    solveBound γ 0 δ = 1 / (2 * Real.pi * γ) := by
  simp [solveBound]

/-- Radius loss absorbs the polynomial growth of the inverse small divisors. -/
theorem solve_weight_le {ω : Fin n → ℝ} {γ τ δ : ℝ}
    (hω : Condition ω γ τ) (hγ : 0 < γ) (hτ : 0 ≤ τ) (hδ : 0 < δ)
    (a : (Fin n → ℤ) → ℂ) (s : ℝ) (k : Fin n → ℤ) :
    ‖solve ω a k‖ * Real.exp ((s - δ) * modeSize k) ≤
      solveBound γ τ δ * (‖a k‖ * Real.exp (s * modeSize k)) := by
  by_cases hk : k = 0
  · subst k
    simp only [solve_zero_mode, norm_zero, zero_mul]
    exact mul_nonneg (solveBound_nonneg hγ hτ hδ) (by positivity)
  · calc
      ‖solve ω a k‖ * Real.exp ((s - δ) * modeSize k) ≤
          ((1 / (2 * Real.pi * γ)) * (‖a k‖ * modeSize k ^ τ)) *
            Real.exp ((s - δ) * modeSize k) :=
        mul_le_mul_of_nonneg_right (norm_solve_le hω hγ a hk) (Real.exp_nonneg _)
      _ = ((1 / (2 * Real.pi * γ)) * ‖a k‖) *
          (modeSize k ^ τ * Real.exp ((s - δ) * modeSize k)) := by ring
      _ ≤ ((1 / (2 * Real.pi * γ)) * ‖a k‖) *
          ((τ / (Real.exp 1 * δ)) ^ τ * Real.exp (s * modeSize k)) := by
        apply mul_le_mul_of_nonneg_left
          (rpow_mul_exp_radius_sub_le s (modeSize_nonneg k) hτ hδ)
        positivity
      _ = solveBound γ τ δ * (‖a k‖ * Real.exp (s * modeSize k)) := by
        unfold solveBound
        ring

/-- The zero-average solution is summable at every strictly smaller coefficient radius. -/
theorem summableWeighted_solve {ω : Fin n → ℝ} {γ τ s δ : ℝ}
    (hω : Condition ω γ τ) (hγ : 0 < γ) (hτ : 0 ≤ τ) (hδ : 0 < δ)
    {a : (Fin n → ℤ) → ℂ} (ha : SummableWeighted s a) :
    SummableWeighted (s - δ) (solve ω a) := by
  exact Summable.of_nonneg_of_le (fun _ => by positivity)
    (solve_weight_le hω hγ hτ hδ a s) (ha.mul_left (solveBound γ τ δ))

/-- The weighted ℓ¹ cohomological estimate for every real exponent `τ ≥ 0`. -/
theorem weightedNorm_solve_le {ω : Fin n → ℝ} {γ τ s δ : ℝ}
    (hω : Condition ω γ τ) (hγ : 0 < γ) (hτ : 0 ≤ τ) (hδ : 0 < δ)
    {a : (Fin n → ℤ) → ℂ} (ha : SummableWeighted s a) :
    weightedNorm (s - δ) (solve ω a) ≤ solveBound γ τ δ * weightedNorm s a := by
  calc
    weightedNorm (s - δ) (solve ω a) ≤
        ∑' k, solveBound γ τ δ * (‖a k‖ * Real.exp (s * modeSize k)) :=
      Summable.tsum_le_tsum (solve_weight_le hω hγ hτ hδ a s)
        (summableWeighted_solve hω hγ hτ hδ ha) (ha.mul_left _)
    _ = solveBound γ τ δ * weightedNorm s a := tsum_mul_left

/-- Existence, uniqueness, summability, and the explicit estimate in one statement. -/
theorem existsUnique_cohomological {ω : Fin n → ℝ} {γ τ s δ : ℝ}
    (hω : Condition ω γ τ) (hγ : 0 < γ) (hτ : 0 ≤ τ) (hδ : 0 < δ)
    {a : (Fin n → ℤ) → ℂ} (ha : SummableWeighted s a) :
    ∃! u : (Fin n → ℤ) → ℂ,
      u 0 = 0 ∧ directionalCoeff ω u = removeAverage a ∧
      SummableWeighted (s - δ) u ∧
      weightedNorm (s - δ) u ≤ solveBound γ τ δ * weightedNorm s a := by
  refine ⟨solve ω a, ⟨solve_zero_mode ω a, directionalCoeff_solve (hω.nonresonant hγ) a,
    summableWeighted_solve hω hγ hτ hδ ha, weightedNorm_solve_le hω hγ hτ hδ ha⟩, ?_⟩
  intro u hu
  exact solve_unique (hω.nonresonant hγ) hu.1 hu.2.1

end KAM.Diophantine
