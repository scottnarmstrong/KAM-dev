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

theorem hb_7_2_0 : ((sjsuHD.hIdx (7, 2, 0)).isEmpty || sjsuHD.hBlock (7, 2, 0) (sjsuHp (7, 2, 0))) =
  true := by
  decide +kernel

theorem hb_7_1_1 : ((sjsuHD.hIdx (7, 1, 1)).isEmpty || sjsuHD.hBlock (7, 1, 1) (sjsuHp (7, 1, 1))) =
  true := by
  decide +kernel

theorem hb_7_0_2 : ((sjsuHD.hIdx (7, 0, 2)).isEmpty || sjsuHD.hBlock (7, 0, 2) (sjsuHp (7, 0, 2))) =
  true := by
  decide +kernel

theorem hb_6_3_0 : ((sjsuHD.hIdx (6, 3, 0)).isEmpty || sjsuHD.hBlock (6, 3, 0) (sjsuHp (6, 3, 0))) =
  true := by
  decide +kernel


end KAM.EffectiveStability.SJSU

end
