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

theorem hb_1_1_7 : ((sjsuHD.hIdx (1, 1, 7)).isEmpty || sjsuHD.hBlock (1, 1, 7) (sjsuHp (1, 1, 7))) =
  true := by
  decide +kernel

theorem hb_1_0_8 : ((sjsuHD.hIdx (1, 0, 8)).isEmpty || sjsuHD.hBlock (1, 0, 8) (sjsuHp (1, 0, 8))) =
  true := by
  decide +kernel

theorem hb_0_9_0 : ((sjsuHD.hIdx (0, 9, 0)).isEmpty || sjsuHD.hBlock (0, 9, 0) (sjsuHp (0, 9, 0))) =
  true := by
  decide +kernel

theorem hb_0_8_1 : ((sjsuHD.hIdx (0, 8, 1)).isEmpty || sjsuHD.hBlock (0, 8, 1) (sjsuHp (0, 8, 1))) =
  true := by
  decide +kernel


end KAM.EffectiveStability.SJSU

end
