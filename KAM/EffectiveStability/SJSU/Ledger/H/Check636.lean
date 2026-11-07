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

theorem hb_0_8_0 : ((sjsuHD.hIdx (0, 8, 0)).isEmpty || sjsuHD.hBlock (0, 8, 0) (sjsuHp (0, 8, 0))) =
  true := by
  decide +kernel

theorem hb_0_7_1 : ((sjsuHD.hIdx (0, 7, 1)).isEmpty || sjsuHD.hBlock (0, 7, 1) (sjsuHp (0, 7, 1))) =
  true := by
  decide +kernel

theorem hb_0_6_2 : ((sjsuHD.hIdx (0, 6, 2)).isEmpty || sjsuHD.hBlock (0, 6, 2) (sjsuHp (0, 6, 2))) =
  true := by
  decide +kernel

theorem hb_0_5_3 : ((sjsuHD.hIdx (0, 5, 3)).isEmpty || sjsuHD.hBlock (0, 5, 3) (sjsuHp (0, 5, 3))) =
  true := by
  decide +kernel


end KAM.EffectiveStability.SJSU

end
