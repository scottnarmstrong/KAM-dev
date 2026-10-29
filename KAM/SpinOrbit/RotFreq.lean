/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.SpinOrbit.Freq
public import KAM.Certificate.DiophantineTransfer

/-!
# Rotated lunar frequencies

`lunarRotFreq ν κ = κ (ν - 1, 1)`: the rotated reference vector, with its exact `ℚ(√5)`
description (`algFreq`) and Diophantine constant `κ / 42` at `τ = 1`, from the rotated bounds of
`KAM.Certificate.DiophantineTransfer` and positive scaling.
-/

@[expose] public section

noncomputable section

namespace KAM.SpinOrbit

open KAM KAM.Certificate

/-- The rotated reference vector `κ (ν - 1, 1)`. -/
def lunarRotFreq (ν : ℝ) (κ : ℚ) : Fin 2 → ℝ := ![(κ : ℝ) * (ν - 1), κ]

private lemma algFreq_two' (a b c : ℚ) (x : ℝ) :
    algFreq 2 [[a, b], [c]] x = ![(a : ℝ) + b * x, c] := by
  ext i
  fin_cases i <;> simp [algFreq, Finset.sum_range_succ]

theorem lunarRotFreqMinus_eq (κ : ℚ) :
    lunarRotFreq lunarNuMinus κ = algFreq 2 [[-79 * κ / 3118, κ / 3118], [κ]] (Real.sqrt 5) := by
  rw [algFreq_two', lunarNuMinus_eq, lunarRotFreq]
  ext i
  fin_cases i <;> simp
  ring

theorem lunarRotFreqPlus_eq (κ : ℚ) :
    lunarRotFreq lunarNuPlus κ = algFreq 2 [[79 * κ / 3118, -κ / 3118], [κ]] (Real.sqrt 5) := by
  rw [algFreq_two', lunarNuPlus_eq, lunarRotFreq]
  ext i
  fin_cases i <;> simp
  ring

/-- Positive scaling of a Diophantine vector. -/
theorem isDiophantine_smul {n : ℕ} {γ τ t : ℝ} {ω : Fin n → ℝ} (ht : 0 < t)
    (h : IsDiophantine γ τ ω) : IsDiophantine (t * γ) τ (t • ω) := by
  intro k hk
  have hsum : ∑ i, (k i : ℝ) * (t • ω) i = t * ∑ i, (k i : ℝ) * ω i := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [hsum, abs_mul, abs_of_pos ht, mul_div_assoc]
  exact mul_le_mul_of_nonneg_left (h k hk) ht.le

private lemma lunarRotFreq_eq_smul (ν : ℝ) (κ : ℚ) :
    lunarRotFreq ν κ = (κ : ℝ) • ![ν - 1, 1] := by
  ext i
  fin_cases i <;> simp [lunarRotFreq]

/-- From `lunarNuMinus_rot_isDiophantine` (`1/42`) and `isDiophantine_smul`. -/
theorem lunarRotFreqMinus_isDiophantine {κ : ℚ} (hκ : 0 < κ) :
    IsDiophantine ((κ : ℝ) / 42) 1 (lunarRotFreq lunarNuMinus κ) := by
  have := isDiophantine_smul (Rat.cast_pos.mpr hκ) lunarNuMinus_rot_isDiophantine
  rw [lunarRotFreq_eq_smul]
  convert this using 1
  ring

theorem lunarRotFreqPlus_isDiophantine {κ : ℚ} (hκ : 0 < κ) :
    IsDiophantine ((κ : ℝ) / 42) 1 (lunarRotFreq lunarNuPlus κ) := by
  have := isDiophantine_smul (Rat.cast_pos.mpr hκ) lunarNuPlus_rot_isDiophantine
  rw [lunarRotFreq_eq_smul]
  convert this using 1
  ring

end KAM.SpinOrbit
