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

theorem tin_202 : ([(4, 13, 1), (4, 14, 0)] : List (Nat × Nat × Nat)).all sjsuHD.tIn = true := by
  decide +kernel

theorem tin_203 : ([(5, 0, 1), (5, 0, 3)] : List (Nat × Nat × Nat)).all sjsuHD.tIn = true := by
  decide +kernel


end KAM.EffectiveStability.SJSU

end
