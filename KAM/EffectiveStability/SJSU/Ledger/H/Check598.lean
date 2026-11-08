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

theorem hb_2_0_0 : ((sjsuHD.hIdx (2, 0, 0)).isEmpty || sjsuHD.hBlock (2, 0, 0) (sjsuHp (2, 0, 0))) =
  true := by
  decide +kernel

theorem hb_1_1_0 : ((sjsuHD.hIdx (1, 1, 0)).isEmpty || sjsuHD.hBlock (1, 1, 0) (sjsuHp (1, 1, 0))) =
  true := by
  decide +kernel

theorem hb_1_0_1 : ((sjsuHD.hIdx (1, 0, 1)).isEmpty || sjsuHD.hBlock (1, 0, 1) (sjsuHp (1, 0, 1))) =
  true := by
  decide +kernel

theorem hb_0_2_0 : ((sjsuHD.hIdx (0, 2, 0)).isEmpty || sjsuHD.hBlock (0, 2, 0) (sjsuHp (0, 2, 0))) =
  true := by
  decide +kernel


end KAM.EffectiveStability.SJSU

end
