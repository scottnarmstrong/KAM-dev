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

theorem hb_0_3_2 : ((sjsuHD.hIdx (0, 3, 2)).isEmpty || sjsuHD.hBlock (0, 3, 2) (sjsuHp (0, 3, 2))) =
  true := by
  decide +kernel

theorem hb_0_2_3 : ((sjsuHD.hIdx (0, 2, 3)).isEmpty || sjsuHD.hBlock (0, 2, 3) (sjsuHp (0, 2, 3))) =
  true := by
  decide +kernel

theorem hb_0_1_4 : ((sjsuHD.hIdx (0, 1, 4)).isEmpty || sjsuHD.hBlock (0, 1, 4) (sjsuHp (0, 1, 4))) =
  true := by
  decide +kernel

theorem hb_0_0_5 : ((sjsuHD.hIdx (0, 0, 5)).isEmpty || sjsuHD.hBlock (0, 0, 5) (sjsuHp (0, 0, 5))) =
  true := by
  decide +kernel


end KAM.EffectiveStability.SJSU

end
