/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.Data.Rat.Defs

/-!
# Frozen definition `KAM.SpinOrbit.lunarOmega`

Owner-approved on 2026-10-31 (decision D49, route D45; docs/tracks/SO/design/FREEZE-PROPOSAL-LOCK.md
§1, with the recommended answers of §2). This file is frozen: it is hashed in
`manifest/frozen-anchors.json`; any change needs an owner-approved versioned successor.
-/

@[expose] public noncomputable section

namespace KAM.SpinOrbit

def lunarOmega : ℚ := 8 / 65

end KAM.SpinOrbit

end
