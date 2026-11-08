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

theorem hb_8_0_0 : ((sjsuHD.hIdx (8, 0, 0)).isEmpty || sjsuHD.hBlock (8, 0, 0) (sjsuHp (8, 0, 0))) =
  true := by
  decide +kernel

theorem hb_7_1_0 : ((sjsuHD.hIdx (7, 1, 0)).isEmpty || sjsuHD.hBlock (7, 1, 0) (sjsuHp (7, 1, 0))) =
  true := by
  decide +kernel

theorem hb_7_0_1 : ((sjsuHD.hIdx (7, 0, 1)).isEmpty || sjsuHD.hBlock (7, 0, 1) (sjsuHp (7, 0, 1))) =
  true := by
  decide +kernel

theorem hb_6_2_0 : ((sjsuHD.hIdx (6, 2, 0)).isEmpty || sjsuHD.hBlock (6, 2, 0) (sjsuHp (6, 2, 0))) =
  true := by
  decide +kernel


end KAM.EffectiveStability.SJSU

end
