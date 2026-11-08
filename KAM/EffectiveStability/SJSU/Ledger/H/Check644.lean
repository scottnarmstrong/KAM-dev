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

theorem hb_3_4_2 : ((sjsuHD.hIdx (3, 4, 2)).isEmpty || sjsuHD.hBlock (3, 4, 2) (sjsuHp (3, 4, 2))) =
  true := by
  decide +kernel

theorem hb_3_3_3 : ((sjsuHD.hIdx (3, 3, 3)).isEmpty || sjsuHD.hBlock (3, 3, 3) (sjsuHp (3, 3, 3))) =
  true := by
  decide +kernel

theorem hb_3_2_4 : ((sjsuHD.hIdx (3, 2, 4)).isEmpty || sjsuHD.hBlock (3, 2, 4) (sjsuHp (3, 2, 4))) =
  true := by
  decide +kernel

theorem hb_3_1_5 : ((sjsuHD.hIdx (3, 1, 5)).isEmpty || sjsuHD.hBlock (3, 1, 5) (sjsuHp (3, 1, 5))) =
  true := by
  decide +kernel


end KAM.EffectiveStability.SJSU

end
