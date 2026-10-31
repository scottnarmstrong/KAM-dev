/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Frozen.SpinOrbit.Defs.SoBarrier
public import KAM.Frozen.SpinOrbit.Defs.LunarPLo
public import KAM.Frozen.SpinOrbit.Defs.LunarPHi
import KAM.SpinOrbit.LunarFinalR2V2

/-!
# Provider for the frozen theorem `KAM.SpinOrbit.lunar_barriers`

The proof of `KAM.SpinOrbit.lunar_barriers` is assembled here as
`KAM.Provider.SpinOrbit.lunar_barriers`, from landed results only. While the frozen anchor is
`DRAFT_SORRY`, this module is quarantined: no module other than the anchor may import it.

* `KAM.Provider.SpinOrbit.lunar_barriers` has exactly the type of the frozen theorem. It is the
  landed `KAM.SpinOrbit.lunar_barriers_65_v2` (`KAM/SpinOrbit/LunarFinalR2V2.lean`, SO-DATA3), whose
  band `[lunarR2BandLo, lunarR2BandHi]` and window `(lunarR2PLo, lunarR2PHi)` are the frozen
  literals: the two band casts are rewritten by `norm_num` equalities (`rw` reaches inside the
  dependent `SoBarrier` type), the window ends are equal to `lunarPLo`, `lunarPHi` by `rfl`. Since
  Q11 of FREEZE-PROPOSAL-2 the landed code uses the frozen `SoBarrier` and `soField`, so no bridge
  is needed. This module does not import the frozen theorem.
-/

public section

namespace KAM.Provider.SpinOrbit

open KAM.SpinOrbit

/-- **Theorem A (continuous form)**: the provider of the frozen `KAM.SpinOrbit.lunar_barriers`, with
exactly its type. -/
theorem lunar_barriers :
    ∃ (Bm : SoBarrier (97245 / 100000) (102755 / 100000))
      (Bp : SoBarrier (97245 / 100000) (102755 / 100000)),
      (∀ q φ, Bm.P q φ < Bp.P q φ) ∧
      (∀ q φ, Bm.P q φ < lunarPLo) ∧ (∀ q φ, (lunarPHi : ℝ) < Bp.P q φ) := by
  have hlo : ((lunarR2BandLo : ℚ) : ℝ) = 97245 / 100000 := by norm_num [lunarR2BandLo]
  have hhi : ((lunarR2BandHi : ℚ) : ℝ) = 102755 / 100000 := by norm_num [lunarR2BandHi]
  have hpl : lunarR2PLo = lunarPLo := rfl
  have hph : lunarR2PHi = lunarPHi := rfl
  have h := lunar_barriers_65_v2
  rw [hlo, hhi, hpl, hph] at h
  exact h

end KAM.Provider.SpinOrbit

end
