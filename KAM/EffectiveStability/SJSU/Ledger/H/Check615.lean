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

theorem hb_1_4_1 : ((sjsuHD.hIdx (1, 4, 1)).isEmpty || sjsuHD.hBlock (1, 4, 1) (sjsuHp (1, 4, 1))) =
  true := by
  decide +kernel

theorem hb_1_3_2 : ((sjsuHD.hIdx (1, 3, 2)).isEmpty || sjsuHD.hBlock (1, 3, 2) (sjsuHp (1, 3, 2))) =
  true := by
  decide +kernel

theorem hb_1_2_3 : ((sjsuHD.hIdx (1, 2, 3)).isEmpty || sjsuHD.hBlock (1, 2, 3) (sjsuHp (1, 2, 3))) =
  true := by
  decide +kernel

theorem hb_1_1_4 : ((sjsuHD.hIdx (1, 1, 4)).isEmpty || sjsuHD.hBlock (1, 1, 4) (sjsuHp (1, 1, 4))) =
  true := by
  decide +kernel


end KAM.EffectiveStability.SJSU

end
