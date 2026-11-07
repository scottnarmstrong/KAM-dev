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

theorem hb_4_5_0 : ((sjsuHD.hIdx (4, 5, 0)).isEmpty || sjsuHD.hBlock (4, 5, 0) (sjsuHp (4, 5, 0))) =
  true := by
  decide +kernel

theorem hb_4_4_1 : ((sjsuHD.hIdx (4, 4, 1)).isEmpty || sjsuHD.hBlock (4, 4, 1) (sjsuHp (4, 4, 1))) =
  true := by
  decide +kernel

theorem hb_4_3_2 : ((sjsuHD.hIdx (4, 3, 2)).isEmpty || sjsuHD.hBlock (4, 3, 2) (sjsuHp (4, 3, 2))) =
  true := by
  decide +kernel

theorem hb_4_2_3 : ((sjsuHD.hIdx (4, 2, 3)).isEmpty || sjsuHD.hBlock (4, 2, 3) (sjsuHp (4, 2, 3))) =
  true := by
  decide +kernel


end KAM.EffectiveStability.SJSU

end
