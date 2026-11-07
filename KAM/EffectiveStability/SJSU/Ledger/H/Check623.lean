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

theorem hb_2_0_5 : ((sjsuHD.hIdx (2, 0, 5)).isEmpty || sjsuHD.hBlock (2, 0, 5) (sjsuHp (2, 0, 5))) =
  true := by
  decide +kernel

theorem hb_1_6_0 : ((sjsuHD.hIdx (1, 6, 0)).isEmpty || sjsuHD.hBlock (1, 6, 0) (sjsuHp (1, 6, 0))) =
  true := by
  decide +kernel

theorem hb_1_5_1 : ((sjsuHD.hIdx (1, 5, 1)).isEmpty || sjsuHD.hBlock (1, 5, 1) (sjsuHp (1, 5, 1))) =
  true := by
  decide +kernel

theorem hb_1_4_2 : ((sjsuHD.hIdx (1, 4, 2)).isEmpty || sjsuHD.hBlock (1, 4, 2) (sjsuHp (1, 4, 2))) =
  true := by
  decide +kernel


end KAM.EffectiveStability.SJSU

end
