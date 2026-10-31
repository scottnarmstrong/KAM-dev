/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.Order.Interval.Finset.Nat

/-!
# Frozen definition `KAM.SpinOrbit.soModes`

Owner-approved on 2026-10-31 (decision D40, docs/tracks/SO/FREEZE-PROPOSAL-2.md; literals D46 and
D48). This file is frozen: it is hashed in `manifest/frozen-anchors.json`; any change needs an
owner-approved versioned successor.
-/

@[expose] public section

namespace KAM.SpinOrbit

/-- The index set `{1, …, 7}` of the seven forcing modes. -/
def soModes : Finset ℕ := Finset.Icc 1 7

end KAM.SpinOrbit

end
