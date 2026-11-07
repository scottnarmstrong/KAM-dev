/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.SJSU.Ledger.H.HData

/-!
# Ledger kernel checks (generated)
-/

@[expose] public section

namespace KAM.EffectiveStability.SJSU

open KAM.EffectiveStability.Tube

theorem hb_0_1_1 : ((sjsuHD.hIdx (0, 1, 1)).isEmpty || sjsuHD.hBlock (0, 1, 1) (sjsuHp (0, 1, 1))) =
  true := by
  decide +kernel

theorem hb_0_0_2 : ((sjsuHD.hIdx (0, 0, 2)).isEmpty || sjsuHD.hBlock (0, 0, 2) (sjsuHp (0, 0, 2))) =
  true := by
  decide +kernel

theorem hb_3_0_0 : ((sjsuHD.hIdx (3, 0, 0)).isEmpty || sjsuHD.hBlock (3, 0, 0) (sjsuHp (3, 0, 0))) =
  true := by
  decide +kernel

theorem hb_2_1_0 : ((sjsuHD.hIdx (2, 1, 0)).isEmpty || sjsuHD.hBlock (2, 1, 0) (sjsuHp (2, 1, 0))) =
  true := by
  decide +kernel


end KAM.EffectiveStability.SJSU

end
