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

theorem hb_2_0_3 : ((sjsuHD.hIdx (2, 0, 3)).isEmpty || sjsuHD.hBlock (2, 0, 3) (sjsuHp (2, 0, 3))) =
  true := by
  decide +kernel

theorem hb_1_4_0 : ((sjsuHD.hIdx (1, 4, 0)).isEmpty || sjsuHD.hBlock (1, 4, 0) (sjsuHp (1, 4, 0))) =
  true := by
  decide +kernel

theorem hb_1_3_1 : ((sjsuHD.hIdx (1, 3, 1)).isEmpty || sjsuHD.hBlock (1, 3, 1) (sjsuHp (1, 3, 1))) =
  true := by
  decide +kernel

theorem hb_1_2_2 : ((sjsuHD.hIdx (1, 2, 2)).isEmpty || sjsuHD.hBlock (1, 2, 2) (sjsuHp (1, 2, 2))) =
  true := by
  decide +kernel


end KAM.EffectiveStability.SJSU

end
