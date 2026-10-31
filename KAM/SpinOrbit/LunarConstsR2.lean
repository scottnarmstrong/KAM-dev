/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.Data.Rat.Init

/-!
# The literal constants of the `N = 65` lunar data (package R2, v2 certifier; SO-DATA3)

* `err` and `disp` of the two tori, as emitted (never rounded down): `err` is the largest checked
  invariance/energy row × 1.001, rounded up to three digits; `disp` is the exact minimum of the
  refined route's final test, `C·err/(γ²ρ²)`, rounded up to three digits.
* The band `δ = 2755/100000` (rule B of FREEZE-PROPOSAL-2 §1.4: the smallest five-decimal literal
  `≥ M`, `M = 0.0275469…` the certified `max |p − 1|` over both barriers) and the window
  `lunarR2PLo = 9934/10000`, `lunarR2PHi = 10066/10000` (rule W: the four-decimal literals just
  outside the certified ranges of the barriers).
-/

@[expose] public section

namespace KAM.SpinOrbit

/-- `err` of the lower torus (`1.6·10⁻¹⁶`). -/
def lunarR2LowerErr : ℚ := 16 / 10 ^ 17

/-- `disp` of the lower torus (`5.78·10⁻¹¹`). -/
def lunarR2LowerDisp : ℚ := 578 / 10 ^ 13

/-- `err` of the upper torus (`1.83·10⁻¹⁶`). -/
def lunarR2UpperErr : ℚ := 183 / 10 ^ 18

/-- `disp` of the upper torus (`6.62·10⁻¹¹`). -/
def lunarR2UpperDisp : ℚ := 662 / 10 ^ 13

/-- The certified band half-width `δ` (rule B). -/
def lunarR2Delta : ℚ := 2755 / 100000

/-- The lower end `1 − δ` of the band. -/
def lunarR2BandLo : ℚ := 97245 / 100000

/-- The upper end `1 + δ` of the band. -/
def lunarR2BandHi : ℚ := 102755 / 100000

/-- The lower end of the confined window (rule W). -/
def lunarR2PLo : ℚ := 9934 / 10000

/-- The upper end of the confined window (rule W). -/
def lunarR2PHi : ℚ := 10066 / 10000

end KAM.SpinOrbit
