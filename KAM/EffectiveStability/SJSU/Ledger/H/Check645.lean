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

theorem hb_3_0_6 : ((sjsuHD.hIdx (3, 0, 6)).isEmpty || sjsuHD.hBlock (3, 0, 6) (sjsuHp (3, 0, 6))) =
  true := by
  decide +kernel

theorem hb_2_7_0 : ((sjsuHD.hIdx (2, 7, 0)).isEmpty || sjsuHD.hBlock (2, 7, 0) (sjsuHp (2, 7, 0))) =
  true := by
  decide +kernel

theorem hb_2_6_1 : ((sjsuHD.hIdx (2, 6, 1)).isEmpty || sjsuHD.hBlock (2, 6, 1) (sjsuHp (2, 6, 1))) =
  true := by
  decide +kernel

theorem hb_2_5_2 : ((sjsuHD.hIdx (2, 5, 2)).isEmpty || sjsuHD.hBlock (2, 5, 2) (sjsuHp (2, 5, 2))) =
  true := by
  decide +kernel


end KAM.EffectiveStability.SJSU

end
