/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import KAM.Frozen.SpinOrbit.Defs.LunarPLo
public import KAM.Frozen.SpinOrbit.Defs.LunarPHi
import KAM.Provider.SpinOrbit.LunarWindow

/-!
# Frozen theorem `KAM.SpinOrbit.lunarPLo_lt_lunarPHi`

Owner-approved on 2026-10-31 (decision D40, docs/tracks/SO/FREEZE-PROPOSAL-2.md; literals D47 and
D49). This file is frozen: it is hashed in `manifest/frozen-anchors.json`; any change needs an
owner-approved versioned successor. Only the proof body between the markers may change, and only to
`by exact KAM.Provider.SpinOrbit.lunarPLo_lt_lunarPHi …` when the provider
`KAM.Provider.SpinOrbit.LunarWindow` is complete (sealing).
-/

@[expose] public section

namespace KAM.SpinOrbit

/-- The initial momentum window of `lunar_spin_confinement` is nonempty. -/
theorem lunarPLo_lt_lunarPHi : lunarPLo < lunarPHi :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact KAM.Provider.SpinOrbit.lunarPLo_lt_lunarPHi
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end KAM.SpinOrbit

end
-- FROZEN_ANCHOR_SUFFIX_END
