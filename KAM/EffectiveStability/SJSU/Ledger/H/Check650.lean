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

theorem hb_0_7_2 : ((sjsuHD.hIdx (0, 7, 2)).isEmpty || sjsuHD.hBlock (0, 7, 2) (sjsuHp (0, 7, 2))) =
  true := by
  decide +kernel

theorem hb_0_6_3 : ((sjsuHD.hIdx (0, 6, 3)).isEmpty || sjsuHD.hBlock (0, 6, 3) (sjsuHp (0, 6, 3))) =
  true := by
  decide +kernel

theorem hb_0_5_4 : ((sjsuHD.hIdx (0, 5, 4)).isEmpty || sjsuHD.hBlock (0, 5, 4) (sjsuHp (0, 5, 4))) =
  true := by
  decide +kernel

theorem hb_0_4_5 : ((sjsuHD.hIdx (0, 4, 5)).isEmpty || sjsuHD.hBlock (0, 4, 5) (sjsuHp (0, 4, 5))) =
  true := by
  decide +kernel


end KAM.EffectiveStability.SJSU

end
