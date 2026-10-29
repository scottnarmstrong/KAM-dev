/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Diophantine.Cohomological
import Mathlib.Tactic.Ring

/-!
# Linearity and reality of the cohomological solver

The solver is complex linear and preserves the conjugate symmetry of Fourier
coefficients of real functions. Its inverse identity holds after removing the
average. These algebraic properties do not require any analytic-function bridge.
-/

@[expose] public section

noncomputable section

namespace KAM.Fourier

variable {n : ℕ}

/-- The Fourier conjugate symmetry associated with real-valued functions. -/
def ConjugateSymmetric (a : (Fin n → ℤ) → ℂ) : Prop :=
  ∀ k, a (-k) = (starRingEnd ℂ) (a k)

theorem ConjugateSymmetric.partialCoeff {a : (Fin n → ℤ) → ℂ}
    (ha : ConjugateSymmetric a) (j : Fin n) : ConjugateSymmetric (partialCoeff j a) := by
  intro k
  simp [KAM.Fourier.partialCoeff, ha k, map_ofNat]

end KAM.Fourier

namespace KAM.Diophantine

open Fourier

variable {n : ℕ}

theorem solve_add (ω : Fin n → ℝ) (a b : (Fin n → ℤ) → ℂ) :
    solve ω (a + b) = solve ω a + solve ω b := by
  funext k
  by_cases hk : k = 0 <;> simp [solve, hk, add_div]

theorem solve_smul (ω : Fin n → ℝ) (c : ℂ) (a : (Fin n → ℤ) → ℂ) :
    solve ω (c • a) = c • solve ω a := by
  funext k
  by_cases hk : k = 0 <;> simp [solve, hk, mul_div_assoc]

/-- The coefficient solver as a complex linear map. -/
def solveLinearMap (ω : Fin n → ℝ) :
    ((Fin n → ℤ) → ℂ) →ₗ[ℂ] ((Fin n → ℤ) → ℂ) where
  toFun := solve ω
  map_add' := solve_add ω
  map_smul' := solve_smul ω

theorem solve_directionalCoeff {ω : Fin n → ℝ} (hω : Nonresonant ω)
    (a : (Fin n → ℤ) → ℂ) : solve ω (directionalCoeff ω a) = removeAverage a := by
  funext k
  by_cases hk : k = 0
  · simp [solve, removeAverage, hk]
  · simp [solve, removeAverage, directionalCoeff, hk, hω.flowMultiplier_ne_zero hk]

theorem flowMultiplier_neg_conj (ω : Fin n → ℝ) (k : Fin n → ℤ) :
    flowMultiplier ω (-k) = (starRingEnd ℂ) (flowMultiplier ω k) := by
  simp [flowMultiplier, frequencyDot, Finset.sum_neg_distrib, map_ofNat]

/-- Real Fourier data have a real cohomological solution. -/
theorem solve_conjugateSymmetric (ω : Fin n → ℝ) {a : (Fin n → ℤ) → ℂ}
    (ha : ConjugateSymmetric a) : ConjugateSymmetric (solve ω a) := by
  intro k
  by_cases hk : k = 0
  · simp [hk]
  · have hnk : -k ≠ 0 := neg_ne_zero.mpr hk
    simp only [solve, ite_eq_right hk, ite_eq_right hnk, ha k, flowMultiplier_neg_conj,
      map_div₀]

end KAM.Diophantine
