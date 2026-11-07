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

theorem hb_2_3_3 : ((sjsuHD.hIdx (2, 3, 3)).isEmpty || sjsuHD.hBlock (2, 3, 3) (sjsuHp (2, 3, 3))) =
  true := by
  decide +kernel

theorem hb_2_2_4 : ((sjsuHD.hIdx (2, 2, 4)).isEmpty || sjsuHD.hBlock (2, 2, 4) (sjsuHp (2, 2, 4))) =
  true := by
  decide +kernel

theorem hb_2_1_5 : ((sjsuHD.hIdx (2, 1, 5)).isEmpty || sjsuHD.hBlock (2, 1, 5) (sjsuHp (2, 1, 5))) =
  true := by
  decide +kernel

theorem hb_2_0_6 : ((sjsuHD.hIdx (2, 0, 6)).isEmpty || sjsuHD.hBlock (2, 0, 6) (sjsuHp (2, 0, 6))) =
  true := by
  decide +kernel


end KAM.EffectiveStability.SJSU

end
