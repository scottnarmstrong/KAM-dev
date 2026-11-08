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

theorem tin_42 : ([(0, 12, 2), (0, 12, 4)] : List (Nat × Nat × Nat)).all sjsuHD.tIn = true := by
  decide +kernel

theorem tin_43 : ([(0, 12, 6), (0, 13, 1)] : List (Nat × Nat × Nat)).all sjsuHD.tIn = true := by
  decide +kernel


end KAM.EffectiveStability.SJSU

end
