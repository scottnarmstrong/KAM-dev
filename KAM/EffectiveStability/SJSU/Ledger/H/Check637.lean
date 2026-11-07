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

theorem hb_0_4_4 : ((sjsuHD.hIdx (0, 4, 4)).isEmpty || sjsuHD.hBlock (0, 4, 4) (sjsuHp (0, 4, 4))) =
  true := by
  decide +kernel

theorem hb_0_3_5 : ((sjsuHD.hIdx (0, 3, 5)).isEmpty || sjsuHD.hBlock (0, 3, 5) (sjsuHp (0, 3, 5))) =
  true := by
  decide +kernel

theorem hb_0_2_6 : ((sjsuHD.hIdx (0, 2, 6)).isEmpty || sjsuHD.hBlock (0, 2, 6) (sjsuHp (0, 2, 6))) =
  true := by
  decide +kernel

theorem hb_0_1_7 : ((sjsuHD.hIdx (0, 1, 7)).isEmpty || sjsuHD.hBlock (0, 1, 7) (sjsuHp (0, 1, 7))) =
  true := by
  decide +kernel


end KAM.EffectiveStability.SJSU

end
