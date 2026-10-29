/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Certificate.Arith.ComplexExp
public import KAM.Certificate.Arith.Rat

/-!
# Range-reduction tests

Kernel evaluations of `certCExpReduced` on the exact rational backend: `s = 0` small (passes) and
large (`‖z‖ + r = 3/2`, rejected); the centre `z = 2` rejected at `s = 0` and accepted at
`s = 2`; a large imaginary pin `2πi k·U(0) ≈ 19i` at `s = 5`.
-/

public section

namespace KAM.Certificate

theorem cexpTest_zero_small : (certCExpReduced (⟨1 / 2, 0⟩ : CC ℚ) 0 0 8).isSome = true := by
  decide +kernel

theorem cexpTest_zero_large : certCExpReduced (⟨1, 0⟩ : CC ℚ) (1 / 2) 0 8 = none := by
  decide +kernel

theorem cexpTest_two_rejected : certCExpReduced (⟨2, 0⟩ : CC ℚ) 0 0 8 = none := by
  decide +kernel

theorem cexpTest_two_reduced : (certCExpReduced (⟨2, 0⟩ : CC ℚ) 0 2 8).isSome = true := by
  decide +kernel

theorem cexpTest_large_pin :
    (certCExpReduced (⟨0, 19⟩ : CC ℚ) (1 / 1000) 5 12).isSome = true := by
  decide +kernel

end KAM.Certificate
