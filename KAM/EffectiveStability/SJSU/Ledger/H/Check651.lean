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

theorem hb_0_3_6 : ((sjsuHD.hIdx (0, 3, 6)).isEmpty || sjsuHD.hBlock (0, 3, 6) (sjsuHp (0, 3, 6))) =
  true := by
  decide +kernel

theorem hb_0_2_7 : ((sjsuHD.hIdx (0, 2, 7)).isEmpty || sjsuHD.hBlock (0, 2, 7) (sjsuHp (0, 2, 7))) =
  true := by
  decide +kernel

theorem hb_0_1_8 : ((sjsuHD.hIdx (0, 1, 8)).isEmpty || sjsuHD.hBlock (0, 1, 8) (sjsuHp (0, 1, 8))) =
  true := by
  decide +kernel

theorem hb_0_0_9 : ((sjsuHD.hIdx (0, 0, 9)).isEmpty || sjsuHD.hBlock (0, 0, 9) (sjsuHp (0, 0, 9))) =
  true := by
  decide +kernel


end KAM.EffectiveStability.SJSU

end
