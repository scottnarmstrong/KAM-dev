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

theorem hb_0_2_2 : ((sjsuHD.hIdx (0, 2, 2)).isEmpty || sjsuHD.hBlock (0, 2, 2) (sjsuHp (0, 2, 2))) =
  true := by
  decide +kernel

theorem hb_0_1_3 : ((sjsuHD.hIdx (0, 1, 3)).isEmpty || sjsuHD.hBlock (0, 1, 3) (sjsuHp (0, 1, 3))) =
  true := by
  decide +kernel

theorem hb_0_0_4 : ((sjsuHD.hIdx (0, 0, 4)).isEmpty || sjsuHD.hBlock (0, 0, 4) (sjsuHp (0, 0, 4))) =
  true := by
  decide +kernel

theorem hb_5_0_0 : ((sjsuHD.hIdx (5, 0, 0)).isEmpty || sjsuHD.hBlock (5, 0, 0) (sjsuHp (5, 0, 0))) =
  true := by
  decide +kernel


end KAM.EffectiveStability.SJSU

end
