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

theorem hb_1_1_2 : ((sjsuHD.hIdx (1, 1, 2)).isEmpty || sjsuHD.hBlock (1, 1, 2) (sjsuHp (1, 1, 2))) =
  true := by
  decide +kernel

theorem hb_1_0_3 : ((sjsuHD.hIdx (1, 0, 3)).isEmpty || sjsuHD.hBlock (1, 0, 3) (sjsuHp (1, 0, 3))) =
  true := by
  decide +kernel

theorem hb_0_4_0 : ((sjsuHD.hIdx (0, 4, 0)).isEmpty || sjsuHD.hBlock (0, 4, 0) (sjsuHp (0, 4, 0))) =
  true := by
  decide +kernel

theorem hb_0_3_1 : ((sjsuHD.hIdx (0, 3, 1)).isEmpty || sjsuHD.hBlock (0, 3, 1) (sjsuHp (0, 3, 1))) =
  true := by
  decide +kernel


end KAM.EffectiveStability.SJSU

end
