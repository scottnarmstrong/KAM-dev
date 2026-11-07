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

theorem pw_0_3 : (fun k : Nat => decide (k < 3) || sjsuHD.powOk 0 ((k : Int) - 2) 2 k (sjsuPp 0 k))
  3 = true := by
  decide +kernel

theorem pw_0_4 : (fun k : Nat => decide (k < 3) || sjsuHD.powOk 0 ((k : Int) - 2) 2 k (sjsuPp 0 k))
  4 = true := by
  decide +kernel

theorem pw_0_5 : (fun k : Nat => decide (k < 3) || sjsuHD.powOk 0 ((k : Int) - 2) 2 k (sjsuPp 0 k))
  5 = true := by
  decide +kernel

theorem pw_0_6 : (fun k : Nat => decide (k < 3) || sjsuHD.powOk 0 ((k : Int) - 2) 2 k (sjsuPp 0 k))
  6 = true := by
  decide +kernel

theorem pw_0_7 : (fun k : Nat => decide (k < 3) || sjsuHD.powOk 0 ((k : Int) - 2) 2 k (sjsuPp 0 k))
  7 = true := by
  decide +kernel

theorem pw_0_8 : (fun k : Nat => decide (k < 3) || sjsuHD.powOk 0 ((k : Int) - 2) 2 k (sjsuPp 0 k))
  8 = true := by
  decide +kernel

theorem pw_0_9 : (fun k : Nat => decide (k < 3) || sjsuHD.powOk 0 ((k : Int) - 2) 2 k (sjsuPp 0 k))
  9 = true := by
  decide +kernel

theorem pw_0_10 : (fun k : Nat => decide (k < 3) || sjsuHD.powOk 0 ((k : Int) - 2) 2 k (sjsuPp 0 k))
  10 = true := by
  decide +kernel


end KAM.EffectiveStability.SJSU

end
