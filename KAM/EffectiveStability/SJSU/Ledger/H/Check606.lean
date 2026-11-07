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

theorem hb_4_1_0 : ((sjsuHD.hIdx (4, 1, 0)).isEmpty || sjsuHD.hBlock (4, 1, 0) (sjsuHp (4, 1, 0))) =
  true := by
  decide +kernel

theorem hb_4_0_1 : ((sjsuHD.hIdx (4, 0, 1)).isEmpty || sjsuHD.hBlock (4, 0, 1) (sjsuHp (4, 0, 1))) =
  true := by
  decide +kernel

theorem hb_3_2_0 : ((sjsuHD.hIdx (3, 2, 0)).isEmpty || sjsuHD.hBlock (3, 2, 0) (sjsuHp (3, 2, 0))) =
  true := by
  decide +kernel

theorem hb_3_1_1 : ((sjsuHD.hIdx (3, 1, 1)).isEmpty || sjsuHD.hBlock (3, 1, 1) (sjsuHp (3, 1, 1))) =
  true := by
  decide +kernel


end KAM.EffectiveStability.SJSU

end
