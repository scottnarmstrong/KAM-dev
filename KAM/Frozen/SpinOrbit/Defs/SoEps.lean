/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.Basic.Real.Basic

/-!
# Frozen definition `KAM.SpinOrbit.soEps`

Owner-approved on 2026-10-31 (decision D40, docs/tracks/SO/FREEZE-PROPOSAL-2.md; literals D46 and
D48). This file is frozen: it is hashed in `manifest/frozen-anchors.json`; any change needs an
owner-approved versioned successor.
-/

@[expose] public noncomputable section

namespace KAM.SpinOrbit

/-- The asphericity parameter `ε_* = 69/200000` (`ε = (3/2)(B − A)/C`) of the lunar model. -/
def soEps : ℝ := 69 / 200000

end KAM.SpinOrbit

end
