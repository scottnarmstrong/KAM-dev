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

theorem pn_0_10 : (fun k : Nat => decide (k < 3) || sjsuHD.powOk 0 (- ((k : Int) - 2)) (-2) (- (k :
  Int)) (sjsuPp 0 (- (k : Int)))) 10 = true := by
  decide +kernel

theorem pn_0_11 : (fun k : Nat => decide (k < 3) || sjsuHD.powOk 0 (- ((k : Int) - 2)) (-2) (- (k :
  Int)) (sjsuPp 0 (- (k : Int)))) 11 = true := by
  decide +kernel

theorem pn_0_12 : (fun k : Nat => decide (k < 3) || sjsuHD.powOk 0 (- ((k : Int) - 2)) (-2) (- (k :
  Int)) (sjsuPp 0 (- (k : Int)))) 12 = true := by
  decide +kernel

theorem pn_0_13 : (fun k : Nat => decide (k < 3) || sjsuHD.powOk 0 (- ((k : Int) - 2)) (-2) (- (k :
  Int)) (sjsuPp 0 (- (k : Int)))) 13 = true := by
  decide +kernel

theorem pn_0_14 : (fun k : Nat => decide (k < 3) || sjsuHD.powOk 0 (- ((k : Int) - 2)) (-2) (- (k :
  Int)) (sjsuPp 0 (- (k : Int)))) 14 = true := by
  decide +kernel

theorem pn_0_15 : (fun k : Nat => decide (k < 3) || sjsuHD.powOk 0 (- ((k : Int) - 2)) (-2) (- (k :
  Int)) (sjsuPp 0 (- (k : Int)))) 15 = true := by
  decide +kernel

theorem pn_0_16 : (fun k : Nat => decide (k < 3) || sjsuHD.powOk 0 (- ((k : Int) - 2)) (-2) (- (k :
  Int)) (sjsuPp 0 (- (k : Int)))) 16 = true := by
  decide +kernel

theorem pn_0_17 : (fun k : Nat => decide (k < 3) || sjsuHD.powOk 0 (- ((k : Int) - 2)) (-2) (- (k :
  Int)) (sjsuPp 0 (- (k : Int)))) 17 = true := by
  decide +kernel


end KAM.EffectiveStability.SJSU

end
