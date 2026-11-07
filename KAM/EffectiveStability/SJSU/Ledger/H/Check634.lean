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

theorem hb_1_7_0 : ((sjsuHD.hIdx (1, 7, 0)).isEmpty || sjsuHD.hBlock (1, 7, 0) (sjsuHp (1, 7, 0))) =
  true := by
  decide +kernel

theorem hb_1_6_1 : ((sjsuHD.hIdx (1, 6, 1)).isEmpty || sjsuHD.hBlock (1, 6, 1) (sjsuHp (1, 6, 1))) =
  true := by
  decide +kernel

theorem hb_1_5_2 : ((sjsuHD.hIdx (1, 5, 2)).isEmpty || sjsuHD.hBlock (1, 5, 2) (sjsuHp (1, 5, 2))) =
  true := by
  decide +kernel

theorem hb_1_4_3 : ((sjsuHD.hIdx (1, 4, 3)).isEmpty || sjsuHD.hBlock (1, 4, 3) (sjsuHp (1, 4, 3))) =
  true := by
  decide +kernel


end KAM.EffectiveStability.SJSU

end
