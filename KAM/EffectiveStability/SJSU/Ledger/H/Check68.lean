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

theorem tin_136 : ([(3, 0, 5), (3, 0, 7)] : List (Nat × Nat × Nat)).all sjsuHD.tIn = true := by
  decide +kernel

theorem tin_137 : ([(3, 0, 9), (3, 0, 11)] : List (Nat × Nat × Nat)).all sjsuHD.tIn = true := by
  decide +kernel


end KAM.EffectiveStability.SJSU

end
