/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Frozen.SpinOrbit.Defs.SoEcc
public import KAM.Frozen.SpinOrbit.Defs.SoCoeffPoly

/-!
# Frozen definition `KAM.SpinOrbit.soA`

Owner-approved on 2026-10-31 (decision D40, docs/tracks/SO/FREEZE-PROPOSAL-2.md; literals D46 and
D48). This file is frozen: it is hashed in `manifest/frozen-anchors.json`; any change needs an
owner-approved versioned successor.
-/

@[expose] public noncomputable section

namespace KAM.SpinOrbit

/-- `A_m(e_*)` as a real number. -/
def soA (m : ℕ) : ℝ := soCoeffPoly soEcc m

end KAM.SpinOrbit

end
