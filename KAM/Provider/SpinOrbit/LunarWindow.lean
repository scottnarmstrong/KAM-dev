/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Frozen.SpinOrbit.Defs.LunarPLo
public import KAM.Frozen.SpinOrbit.Defs.LunarPHi

/-!
# Provider for the frozen theorem `KAM.SpinOrbit.lunarPLo_lt_lunarPHi`

The proof of `KAM.SpinOrbit.lunarPLo_lt_lunarPHi` is assembled here as
`KAM.Provider.SpinOrbit.lunarPLo_lt_lunarPHi`. While the frozen anchor is `DRAFT_SORRY`, this module
is quarantined: no module other than the anchor may import it.

* `KAM.Provider.SpinOrbit.lunarPLo_lt_lunarPHi` has exactly the type of the frozen theorem:
  `9934 / 10000 < 10066 / 10000` in `ℚ`, by `decide +kernel` (plain `decide` does not reduce the
  `ℚ` division literals). This module does not import the frozen theorem.
-/

public section

namespace KAM.Provider.SpinOrbit

open KAM.SpinOrbit

/-- The initial momentum window of `lunar_spin_confinement` is nonempty: the provider of the frozen
`KAM.SpinOrbit.lunarPLo_lt_lunarPHi`, with exactly its type. -/
theorem lunarPLo_lt_lunarPHi : lunarPLo < lunarPHi := by
  decide +kernel

end KAM.Provider.SpinOrbit

end
