/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Diophantine.Cohomological
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Dependence of the cohomological solution on the frequency

An exact resolvent identity expresses the difference of two solutions as two
cohomological inverses with one directional derivative between them. Three
positive radius losses give a Lipschitz bound on a fixed Diophantine set.
This concerns the linear cohomological solver, not the nonlinear family of KAM tori.
-/

public section

noncomputable section

namespace KAM.Diophantine

open Fourier

variable {n : ℕ}

theorem frequencyDot_sub (ω ν : Fin n → ℝ) (k : Fin n → ℤ) :
    frequencyDot (ν - ω) k = frequencyDot ν k - frequencyDot ω k := by
  simp [frequencyDot, mul_sub, Finset.sum_sub_distrib]

theorem flowMultiplier_sub (ω ν : Fin n → ℝ) (k : Fin n → ℤ) :
    flowMultiplier (ν - ω) k = flowMultiplier ν k - flowMultiplier ω k := by
  simp [flowMultiplier, frequencyDot_sub, mul_sub]

/-- The frequency pairing is bounded using the sup norm on frequency vectors. -/
theorem abs_frequencyDot_le (ω : Fin n → ℝ) (k : Fin n → ℤ) :
    |frequencyDot ω k| ≤ modeSize k * ‖ω‖ := by
  calc
    |frequencyDot ω k| ≤ ∑ j, |(k j : ℝ) * ω j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, |(k j : ℝ)| * ‖ω‖ := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (norm_le_pi_norm ω j) (abs_nonneg _)
    _ = modeSize k * ‖ω‖ := by rw [modeSize, Finset.sum_mul]

/-- A directional derivative loses one power of the radius gap. -/
theorem directionalCoeff_weight_le (ω : Fin n → ℝ) (a : (Fin n → ℤ) → ℂ)
    (s : ℝ) {δ : ℝ} (hδ : 0 < δ) (k : Fin n → ℤ) :
    ‖directionalCoeff ω a k‖ * Real.exp ((s - δ) * modeSize k) ≤
      (2 * Real.pi / (Real.exp 1 * δ)) * ‖ω‖ *
        (‖a k‖ * Real.exp (s * modeSize k)) := by
  rw [directionalCoeff, norm_mul, norm_flowMultiplier]
  calc
    (2 * Real.pi * |frequencyDot ω k| * ‖a k‖) *
        Real.exp ((s - δ) * modeSize k) ≤
        (2 * Real.pi * (modeSize k * ‖ω‖) * ‖a k‖) *
          Real.exp ((s - δ) * modeSize k) := by
      gcongr
      exact abs_frequencyDot_le ω k
    _ = (2 * Real.pi * ‖ω‖ * ‖a k‖) *
        (modeSize k * Real.exp ((s - δ) * modeSize k)) := by ring
    _ ≤ (2 * Real.pi * ‖ω‖ * ‖a k‖) *
        ((Real.exp (-1) / δ) * Real.exp (s * modeSize k)) := by
      exact mul_le_mul_of_nonneg_left (mul_exp_radius_sub_le s (modeSize k) hδ)
        (by positivity)
    _ = (2 * Real.pi / (Real.exp 1 * δ)) * ‖ω‖ *
        (‖a k‖ * Real.exp (s * modeSize k)) := by
      rw [Real.exp_neg]
      ring

theorem summableWeighted_directionalCoeff (ω : Fin n → ℝ) {a : (Fin n → ℤ) → ℂ}
    {s δ : ℝ} (ha : SummableWeighted s a) (hδ : 0 < δ) :
    SummableWeighted (s - δ) (directionalCoeff ω a) := by
  exact Summable.of_nonneg_of_le (fun _ => by positivity)
    (directionalCoeff_weight_le ω a s hδ)
    (ha.mul_left ((2 * Real.pi / (Real.exp 1 * δ)) * ‖ω‖))

theorem weightedNorm_directionalCoeff_le (ω : Fin n → ℝ) {a : (Fin n → ℤ) → ℂ}
    {s δ : ℝ} (ha : SummableWeighted s a) (hδ : 0 < δ) :
    weightedNorm (s - δ) (directionalCoeff ω a) ≤
      (2 * Real.pi / (Real.exp 1 * δ)) * ‖ω‖ * weightedNorm s a := by
  calc
    weightedNorm (s - δ) (directionalCoeff ω a) ≤
        ∑' k, ((2 * Real.pi / (Real.exp 1 * δ)) * ‖ω‖) *
          (‖a k‖ * Real.exp (s * modeSize k)) :=
      Summable.tsum_le_tsum (directionalCoeff_weight_le ω a s hδ)
        (summableWeighted_directionalCoeff ω ha hδ) (ha.mul_left _)
    _ = (2 * Real.pi / (Real.exp 1 * δ)) * ‖ω‖ * weightedNorm s a := tsum_mul_left

/-- The inverse-difference identity behind Lipschitz dependence on the frequency. -/
theorem solve_sub_solve {ω ν : Fin n → ℝ} (hω : Nonresonant ω) (hν : Nonresonant ν)
    (a : (Fin n → ℤ) → ℂ) :
    (fun k => solve ω a k - solve ν a k) =
      solve ω (directionalCoeff (ν - ω) (solve ν a)) := by
  funext k
  by_cases hk : k = 0
  · simp [hk]
  · simp only [solve, ite_eq_right hk, directionalCoeff, flowMultiplier_sub]
    field_simp [hω.flowMultiplier_ne_zero hk, hν.flowMultiplier_ne_zero hk]

/-- The difference of solutions is summable after three independent positive radius losses. -/
theorem summableWeighted_solve_sub_solve {ω ν : Fin n → ℝ} {γ τ s δ₁ δ₂ δ₃ : ℝ}
    (hω : Condition ω γ τ) (hν : Condition ν γ τ) (hγ : 0 < γ) (hτ : 0 ≤ τ)
    (h₁ : 0 < δ₁) (h₂ : 0 < δ₂) (h₃ : 0 < δ₃)
    {a : (Fin n → ℤ) → ℂ} (ha : SummableWeighted s a) :
    SummableWeighted (s - (δ₁ + δ₂ + δ₃)) (fun k => solve ω a k - solve ν a k) := by
  rw [solve_sub_solve (hω.nonresonant hγ) (hν.nonresonant hγ)]
  have h := summableWeighted_solve hω hγ hτ h₃
    (summableWeighted_directionalCoeff (ν - ω) (summableWeighted_solve hν hγ hτ h₁ ha) h₂)
  convert h using 1
  ring

/-- A quantitative Lipschitz estimate for the inverse on a fixed Diophantine set. -/
theorem weightedNorm_solve_sub_solve_le {ω ν : Fin n → ℝ} {γ τ s δ₁ δ₂ δ₃ : ℝ}
    (hω : Condition ω γ τ) (hν : Condition ν γ τ) (hγ : 0 < γ) (hτ : 0 ≤ τ)
    (h₁ : 0 < δ₁) (h₂ : 0 < δ₂) (h₃ : 0 < δ₃)
    {a : (Fin n → ℤ) → ℂ} (ha : SummableWeighted s a) :
    weightedNorm (s - (δ₁ + δ₂ + δ₃)) (fun k => solve ω a k - solve ν a k) ≤
      (solveBound γ τ δ₃ * (2 * Real.pi / (Real.exp 1 * δ₂)) * solveBound γ τ δ₁) *
        ‖ν - ω‖ * weightedNorm s a := by
  rw [solve_sub_solve (hω.nonresonant hγ) (hν.nonresonant hγ)]
  have hνa := summableWeighted_solve hν hγ hτ h₁ ha
  have hda := summableWeighted_directionalCoeff (ν - ω) hνa h₂
  have hr : s - (δ₁ + δ₂ + δ₃) = (s - δ₁ - δ₂) - δ₃ := by ring
  rw [hr]
  calc
    weightedNorm (s - δ₁ - δ₂ - δ₃)
        (solve ω (directionalCoeff (ν - ω) (solve ν a))) ≤
        solveBound γ τ δ₃ * weightedNorm (s - δ₁ - δ₂)
          (directionalCoeff (ν - ω) (solve ν a)) :=
      weightedNorm_solve_le hω hγ hτ h₃ hda
    _ ≤ solveBound γ τ δ₃ * ((2 * Real.pi / (Real.exp 1 * δ₂)) * ‖ν - ω‖ *
        weightedNorm (s - δ₁) (solve ν a)) :=
      mul_le_mul_of_nonneg_left (weightedNorm_directionalCoeff_le (ν - ω) hνa h₂)
        (solveBound_nonneg hγ hτ h₃)
    _ ≤ solveBound γ τ δ₃ * ((2 * Real.pi / (Real.exp 1 * δ₂)) * ‖ν - ω‖ *
        (solveBound γ τ δ₁ * weightedNorm s a)) := by
      apply mul_le_mul_of_nonneg_left _ (solveBound_nonneg hγ hτ h₃)
      exact mul_le_mul_of_nonneg_left (weightedNorm_solve_le hν hγ hτ h₁ ha) (by positivity)
    _ = (solveBound γ τ δ₃ * (2 * Real.pi / (Real.exp 1 * δ₂)) * solveBound γ τ δ₁) *
        ‖ν - ω‖ * weightedNorm s a := by ring

/-- Splitting one radius gap into thirds gives a single uniform Lipschitz constant. -/
theorem weightedNorm_solve_sub_solve_thirds_le {ω ν : Fin n → ℝ} {γ τ s δ : ℝ}
    (hω : Condition ω γ τ) (hν : Condition ν γ τ) (hγ : 0 < γ) (hτ : 0 ≤ τ)
    (hδ : 0 < δ) {a : (Fin n → ℤ) → ℂ} (ha : SummableWeighted s a) :
    weightedNorm (s - δ) (fun k => solve ω a k - solve ν a k) ≤
      ((2 * Real.pi / (Real.exp 1 * (δ / 3))) * solveBound γ τ (δ / 3) ^ 2) *
        ‖ν - ω‖ * weightedNorm s a := by
  have ht : 0 < δ / 3 := by positivity
  have h := weightedNorm_solve_sub_solve_le hω hν hγ hτ ht ht ht ha
  have hr : δ / 3 + δ / 3 + δ / 3 = δ := by ring
  rw [hr] at h
  convert h using 1
  ring

end KAM.Diophantine
