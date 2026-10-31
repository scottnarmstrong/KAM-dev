/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.Basic.Real.Basic

/-!
# Frozen definition `KAM.SpinOrbit.soEcc`

Owner-approved on 2026-10-31 (decision D40, docs/tracks/SO/FREEZE-PROPOSAL-2.md; literals D47 and
D49). This file is frozen: it is hashed in `manifest/frozen-anchors.json`; any change needs an
owner-approved versioned successor.
-/

@[expose] public noncomputable section

namespace KAM.SpinOrbit

/-- The eccentricity `e_* = 549/10000` of the lunar model. -/
def soEcc : ℝ := 549 / 10000

end KAM.SpinOrbit

end
