/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.Data.Rat.Init

/-!
# Frozen definition `KAM.SpinOrbit.lunarPLo`

Owner-approved on 2026-10-31 (decision D40, docs/tracks/SO/FREEZE-PROPOSAL-2.md; literals D46 and
D48). This file is frozen: it is hashed in `manifest/frozen-anchors.json`; any change needs an
owner-approved versioned successor.
-/

@[expose] public section

namespace KAM.SpinOrbit

/-- Lower end of the certified initial momentum window (ruling O1). -/
def lunarPLo : ℚ := 9934 / 10000

end KAM.SpinOrbit

end
