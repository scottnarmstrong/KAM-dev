/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Certificate.Positivity
public import KAM.Certificate.Arith.Rat

/-!
# Tests of `checkRealLowerBound` (`ℚ` backend, `decide +kernel`)

`f = 3 + (χ₁ + χ₋₁)/2` has real part `3 + cos 2πθ ≥ 2`. With `w = 11/10` the model of
`(f + f*) - 2 g g* - 2 m₀` has sup bound `2 w = 11/5`, so the check passes iff `m ≤ m₀ - 11/10`.
The SOS term `g = χ₁` (`g g* = 1`) is shifted by the constant `4`; a degree `≠ 0` is rejected.
-/

public section

namespace KAM.Certificate

open CertArith

/-- The test weight `w = 11/10` at width `1/100`. -/
def posTestW : CertWeight := ⟨1 / 100, 11 / 10⟩

def posTestCfg : ModelConfig ℚ := ⟨100, 0, 0, fun _ _ => none, []⟩

def posTestQ (cs : List (CertKey × ℚ)) : CertPoly ℚ := ⟨cs.map fun t => (t.1, ⟨t.2, 0⟩)⟩

def posTestF (c : ℚ) : CertModel ℚ :=
  ⟨0, posTestQ [([-1], 1 / 2), ([0], c), ([1], 1 / 2)], 0⟩

theorem posTest_pass : checkRealLowerBound posTestW posTestCfg (posTestF 3) 3 (19 / 10)
    (posTestQ []) = true := by decide +kernel

theorem posTest_reject_slack : checkRealLowerBound posTestW posTestCfg (posTestF 3) 3 2
    (posTestQ []) = false := by decide +kernel

theorem posTest_sos : checkRealLowerBound posTestW posTestCfg (posTestF 4) 3 (19 / 10)
    (posTestQ [([1], 1)]) = true := by decide +kernel

theorem posTest_sos_reject : checkRealLowerBound posTestW posTestCfg (posTestF 4) 3 2
    (posTestQ [([1], 1)]) = false := by decide +kernel

theorem posTest_deg : checkRealLowerBound posTestW posTestCfg
    ⟨1, posTestQ [([0], 3)], 0⟩ 3 0 (posTestQ []) = false := by decide +kernel

end KAM.Certificate
