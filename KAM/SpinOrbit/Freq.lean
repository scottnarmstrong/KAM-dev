/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Certificate.Freq
public import KAM.Certificate.QuadraticDiophantine

/-!
# Lunar frequencies in `ℚ(√5)`

The isoenergetic reference vectors `(ν± / 2, 1 / 2)` are the exact `ℚ(√5)` instances of
`algFreq`, with coefficients read off `lunarNuMinus_eq` and `lunarNuPlus_eq`.
-/

@[expose] public section

noncomputable section

namespace KAM.SpinOrbit

open KAM.Certificate

private lemma algFreq_two (a b c : ℚ) (x : ℝ) :
    algFreq 2 [[a, b], [c]] x = ![(a : ℝ) + b * x, c] := by
  ext i
  fin_cases i <;> simp [algFreq, Finset.sum_range_succ]

theorem lunarFreqMinus_eq :
    ![lunarNuMinus / 2, 1 / 2] = algFreq 2 [[3039 / 6236, 1 / 6236], [1 / 2]] (Real.sqrt 5) := by
  rw [algFreq_two, lunarNuMinus_eq]
  ext i
  fin_cases i <;> simp
  ring

theorem lunarFreqPlus_eq :
    ![lunarNuPlus / 2, 1 / 2] = algFreq 2 [[3197 / 6236, -1 / 6236], [1 / 2]] (Real.sqrt 5) := by
  rw [algFreq_two, lunarNuPlus_eq]
  ext i
  fin_cases i <;> simp
  ring

end KAM.SpinOrbit
