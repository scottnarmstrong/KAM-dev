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

theorem hb_5_1_1 : ((sjsuHD.hIdx (5, 1, 1)).isEmpty || sjsuHD.hBlock (5, 1, 1) (sjsuHp (5, 1, 1))) =
  true := by
  decide +kernel

theorem hb_5_0_2 : ((sjsuHD.hIdx (5, 0, 2)).isEmpty || sjsuHD.hBlock (5, 0, 2) (sjsuHp (5, 0, 2))) =
  true := by
  decide +kernel

theorem hb_4_3_0 : ((sjsuHD.hIdx (4, 3, 0)).isEmpty || sjsuHD.hBlock (4, 3, 0) (sjsuHp (4, 3, 0))) =
  true := by
  decide +kernel

theorem hb_4_2_1 : ((sjsuHD.hIdx (4, 2, 1)).isEmpty || sjsuHD.hBlock (4, 2, 1) (sjsuHp (4, 2, 1))) =
  true := by
  decide +kernel


end KAM.EffectiveStability.SJSU

end
