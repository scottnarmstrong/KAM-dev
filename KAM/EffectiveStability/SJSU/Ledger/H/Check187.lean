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

theorem pw_1_11 : (fun k : Nat => decide (k < 3) || sjsuHD.powOk 1 ((k : Int) - 2) 2 k (sjsuPp 1 k))
  11 = true := by
  decide +kernel

theorem pw_1_12 : (fun k : Nat => decide (k < 3) || sjsuHD.powOk 1 ((k : Int) - 2) 2 k (sjsuPp 1 k))
  12 = true := by
  decide +kernel

theorem pw_1_13 : (fun k : Nat => decide (k < 3) || sjsuHD.powOk 1 ((k : Int) - 2) 2 k (sjsuPp 1 k))
  13 = true := by
  decide +kernel

theorem pw_1_14 : (fun k : Nat => decide (k < 3) || sjsuHD.powOk 1 ((k : Int) - 2) 2 k (sjsuPp 1 k))
  14 = true := by
  decide +kernel

theorem pw_1_15 : (fun k : Nat => decide (k < 3) || sjsuHD.powOk 1 ((k : Int) - 2) 2 k (sjsuPp 1 k))
  15 = true := by
  decide +kernel

theorem pw_1_16 : (fun k : Nat => decide (k < 3) || sjsuHD.powOk 1 ((k : Int) - 2) 2 k (sjsuPp 1 k))
  16 = true := by
  decide +kernel

theorem pw_1_17 : (fun k : Nat => decide (k < 3) || sjsuHD.powOk 1 ((k : Int) - 2) 2 k (sjsuPp 1 k))
  17 = true := by
  decide +kernel

theorem pw_1_18 : (fun k : Nat => decide (k < 3) || sjsuHD.powOk 1 ((k : Int) - 2) 2 k (sjsuPp 1 k))
  18 = true := by
  decide +kernel


end KAM.EffectiveStability.SJSU

end
