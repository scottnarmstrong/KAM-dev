/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Frozen.EffectiveStability.SJSU.SJSU18O2Part0
public import KAM.Frozen.EffectiveStability.SJSU.SJSU18O2Part1
public import KAM.Frozen.EffectiveStability.SJSU.SJSU18O2Part2
public import KAM.Frozen.EffectiveStability.SJSU.SJSU18O2Part3
public import KAM.Frozen.EffectiveStability.SJSU.SJSU18O2Part4
public import KAM.Frozen.EffectiveStability.SJSU.SJSU18O2Part5

/-!
# Frozen definition `KAM.EffectiveStability.sjsu18O2Terms`

Owner-approved on 2026-11-06 (decision D76; exact text: draft v2 of
`docs/explorations/sjsu-g2-t2conf-proposal.md`, program T2-CONF). Part of the opt-in application
library `KAMSJSU` (D51). This file is frozen: it is hashed in `manifest/frozen-anchors.json`;
any change needs an owner-approved versioned successor.
-/

@[expose] public section

namespace KAM.EffectiveStability

/-- The 7,941 rows of the complex form of `SJSU18-O2` (D75), in file order. -/
def sjsu18O2Terms : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℚ) :=
  sjsu18O2Part0 ++ sjsu18O2Part1 ++ sjsu18O2Part2 ++ sjsu18O2Part3 ++ sjsu18O2Part4 ++ sjsu18O2Part5

end KAM.EffectiveStability

end
