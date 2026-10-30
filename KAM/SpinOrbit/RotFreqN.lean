/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.SpinOrbit.RotFreq
public import KAM.Certificate.QuadraticDiophantineN

/-!
# Rotated lunar frequencies at a general barrier index `N`

For `ν± = lunarNu{Minus,Plus}N N` the rotated reference vector `lunarRotFreq ν κ = κ (ν - 1, 1)`
has the exact `ℚ(√5)` description `algFreq 2 [[∓κ m/D, ±κ/D], [κ]] √5` with `m = 2N - 1` and
`D = 2 (N² - N - 1)`, and (for `N ≥ 8`, `κ > 0`) Diophantine constant `κ / (N + 2)` at `τ = 1`.
-/

@[expose] public section

noncomputable section

namespace KAM.SpinOrbit

open KAM KAM.Certificate

private lemma algFreq_twoN (a b c : ℚ) (x : ℝ) :
    algFreq 2 [[a, b], [c]] x = ![(a : ℝ) + b * x, c] := by
  ext i
  fin_cases i <;> simp [algFreq, Finset.sum_range_succ]

private lemma lunarDN_ne (N : ℕ) : (2 * ((N : ℝ) ^ 2 - N - 1)) ≠ 0 := by
  rcases Nat.lt_or_ge N 2 with h | h
  · interval_cases N <;> norm_num
  · have : (2 : ℝ) ≤ N := by exact_mod_cast h
    nlinarith

theorem lunarRotFreqMinusN_eq (N : ℕ) (κ : ℚ) :
    lunarRotFreq (lunarNuMinusN N) κ = algFreq 2
      [[-(2 * N - 1) * κ / (2 * (N ^ 2 - N - 1)), κ / (2 * (N ^ 2 - N - 1))], [κ]]
      (Real.sqrt 5) := by
  rw [algFreq_twoN, lunarNuMinusN_eq, lunarRotFreq]
  have hD := lunarDN_ne N
  ext i
  fin_cases i <;> simp
  rw [show ((2 * (N : ℝ) - 1) ^ 2 - 5) / 2 = 2 * ((N : ℝ) ^ 2 - N - 1) by ring]
  field_simp
  ring

theorem lunarRotFreqPlusN_eq (N : ℕ) (κ : ℚ) :
    lunarRotFreq (lunarNuPlusN N) κ = algFreq 2
      [[(2 * N - 1) * κ / (2 * (N ^ 2 - N - 1)), -κ / (2 * (N ^ 2 - N - 1))], [κ]]
      (Real.sqrt 5) := by
  rw [algFreq_twoN, lunarNuPlusN_eq, lunarRotFreq]
  have hD := lunarDN_ne N
  ext i
  fin_cases i <;> simp
  rw [show ((2 * (N : ℝ) - 1) ^ 2 - 5) / 2 = 2 * ((N : ℝ) ^ 2 - N - 1) by ring]
  field_simp
  ring

private lemma lunarRotFreq_eq_smulN (ν : ℝ) (κ : ℚ) :
    lunarRotFreq ν κ = (κ : ℝ) • ![ν - 1, 1] := by
  ext i
  fin_cases i <;> simp [lunarRotFreq]

/-- `κ (ν₋ - 1, 1)` is `(κ / (N + 2), 1)`-Diophantine for `N ≥ 8`, `κ > 0`. -/
theorem lunarRotFreqMinusN_isDiophantine (N : ℕ) (hN : 8 ≤ N) {κ : ℚ} (hκ : 0 < κ) :
    IsDiophantine ((κ : ℝ) / (N + 2)) 1 (lunarRotFreq (lunarNuMinusN N) κ) := by
  have := soIsDiophantine_smul (Rat.cast_pos.mpr hκ) (lunarNuMinusN_rot_isDiophantine N hN)
  rw [lunarRotFreq_eq_smulN]
  convert this using 1
  ring

/-- `κ (ν₊ - 1, 1)` is `(κ / (N + 2), 1)`-Diophantine for `N ≥ 8`, `κ > 0`. -/
theorem lunarRotFreqPlusN_isDiophantine (N : ℕ) (hN : 8 ≤ N) {κ : ℚ} (hκ : 0 < κ) :
    IsDiophantine ((κ : ℝ) / (N + 2)) 1 (lunarRotFreq (lunarNuPlusN N) κ) := by
  have := soIsDiophantine_smul (Rat.cast_pos.mpr hκ) (lunarNuPlusN_rot_isDiophantine N hN)
  rw [lunarRotFreq_eq_smulN]
  convert this using 1
  ring

/-! ### `N = 65` (D38) and the fallbacks `N = 60, 55` -/

theorem lunarRotFreqMinusN_isDiophantine_65 {κ : ℚ} (hκ : 0 < κ) :
    IsDiophantine ((κ : ℝ) / 67) 1 (lunarRotFreq (lunarNuMinusN 65) κ) := by
  have := lunarRotFreqMinusN_isDiophantine 65 (by norm_num) hκ
  norm_num at this; exact this

theorem lunarRotFreqPlusN_isDiophantine_65 {κ : ℚ} (hκ : 0 < κ) :
    IsDiophantine ((κ : ℝ) / 67) 1 (lunarRotFreq (lunarNuPlusN 65) κ) := by
  have := lunarRotFreqPlusN_isDiophantine 65 (by norm_num) hκ
  norm_num at this; exact this

theorem lunarRotFreqMinusN_isDiophantine_60 {κ : ℚ} (hκ : 0 < κ) :
    IsDiophantine ((κ : ℝ) / 62) 1 (lunarRotFreq (lunarNuMinusN 60) κ) := by
  have := lunarRotFreqMinusN_isDiophantine 60 (by norm_num) hκ
  norm_num at this; exact this

theorem lunarRotFreqPlusN_isDiophantine_60 {κ : ℚ} (hκ : 0 < κ) :
    IsDiophantine ((κ : ℝ) / 62) 1 (lunarRotFreq (lunarNuPlusN 60) κ) := by
  have := lunarRotFreqPlusN_isDiophantine 60 (by norm_num) hκ
  norm_num at this; exact this

theorem lunarRotFreqMinusN_isDiophantine_55 {κ : ℚ} (hκ : 0 < κ) :
    IsDiophantine ((κ : ℝ) / 57) 1 (lunarRotFreq (lunarNuMinusN 55) κ) := by
  have := lunarRotFreqMinusN_isDiophantine 55 (by norm_num) hκ
  norm_num at this; exact this

theorem lunarRotFreqPlusN_isDiophantine_55 {κ : ℚ} (hκ : 0 < κ) :
    IsDiophantine ((κ : ℝ) / 57) 1 (lunarRotFreq (lunarNuPlusN 55) κ) := by
  have := lunarRotFreqPlusN_isDiophantine 55 (by norm_num) hκ
  norm_num at this; exact this

/-- At `N = 40` the general constant `κ / (N + 2)` is the landed `κ / 42`. -/
theorem lunarRotFreqMinusN_forty {κ : ℚ} (hκ : 0 < κ) :
    IsDiophantine ((κ : ℝ) / 42) 1 (lunarRotFreq lunarNuMinus κ) := by
  have := lunarRotFreqMinusN_isDiophantine 40 (by norm_num) hκ
  rw [lunarNuMinusN_forty] at this
  norm_num at this; exact this

end KAM.SpinOrbit

end
