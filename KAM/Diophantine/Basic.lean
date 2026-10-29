/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Fourier.Derivative
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Positivity

/-!
# Diophantine frequencies

The small-divisor condition is `γ / |k|₁ ^ τ ≤ |k · ω|` for every nonzero
integer index. This is the convention of `docs/statement.md` and HL19 (3.1).
Positivity of `γ` and nonnegativity of `τ` are explicit hypotheses where needed.
-/

@[expose] public section

noncomputable section

namespace KAM.Fourier

variable {n : ℕ}

@[simp] theorem modeSize_zero : modeSize (0 : Fin n → ℤ) = 0 := by
  simp [modeSize]

theorem modeSize_pos {k : Fin n → ℤ} (hk : k ≠ 0) : 0 < modeSize k := by
  by_contra h
  apply hk
  funext j
  have hj : |(k j : ℝ)| ≤ 0 := (abs_coord_le_modeSize k j).trans (le_of_not_gt h)
  have hz : (k j : ℝ) = 0 := abs_eq_zero.mp (le_antisymm hj (abs_nonneg _))
  exact_mod_cast hz

end KAM.Fourier

namespace KAM.Diophantine

open Fourier

variable {n : ℕ}

/-- The pairing of a frequency vector with an integer Fourier mode. -/
def frequencyDot (ω : Fin n → ℝ) (k : Fin n → ℤ) : ℝ :=
  ∑ j, (k j : ℝ) * ω j

@[simp] theorem frequencyDot_zero (ω : Fin n → ℝ) : frequencyDot ω 0 = 0 := by
  simp [frequencyDot]

/-- No nonzero integer Fourier mode resonates with `ω`. -/
def Nonresonant (ω : Fin n → ℝ) : Prop :=
  ∀ k : Fin n → ℤ, k ≠ 0 → frequencyDot ω k ≠ 0

/-- The standard real-exponent Diophantine small-divisor inequality. -/
def Condition (ω : Fin n → ℝ) (γ τ : ℝ) : Prop :=
  ∀ k : Fin n → ℤ, k ≠ 0 → γ / modeSize k ^ τ ≤ |frequencyDot ω k|

theorem Condition.nonresonant {ω : Fin n → ℝ} {γ τ : ℝ}
    (hω : Condition ω γ τ) (hγ : 0 < γ) : Nonresonant ω := by
  intro k hk
  have hp : 0 < γ / modeSize k ^ τ :=
    div_pos hγ (Real.rpow_pos_of_pos (modeSize_pos hk) τ)
  exact abs_pos.mp (hp.trans_le (hω k hk))

end KAM.Diophantine
