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

theorem pm_0 : sjsuHD.powOk 0 (-1) (-1) (-2) (sjsuPp 0 (-2)) = true := by
  decide +kernel

theorem pn_0_3 : (fun k : Nat => decide (k < 3) || sjsuHD.powOk 0 (- ((k : Int) - 2)) (-2) (- (k :
  Int)) (sjsuPp 0 (- (k : Int)))) 3 = true := by
  decide +kernel

theorem pn_0_4 : (fun k : Nat => decide (k < 3) || sjsuHD.powOk 0 (- ((k : Int) - 2)) (-2) (- (k :
  Int)) (sjsuPp 0 (- (k : Int)))) 4 = true := by
  decide +kernel

theorem pn_0_5 : (fun k : Nat => decide (k < 3) || sjsuHD.powOk 0 (- ((k : Int) - 2)) (-2) (- (k :
  Int)) (sjsuPp 0 (- (k : Int)))) 5 = true := by
  decide +kernel

theorem pn_0_6 : (fun k : Nat => decide (k < 3) || sjsuHD.powOk 0 (- ((k : Int) - 2)) (-2) (- (k :
  Int)) (sjsuPp 0 (- (k : Int)))) 6 = true := by
  decide +kernel

theorem pn_0_7 : (fun k : Nat => decide (k < 3) || sjsuHD.powOk 0 (- ((k : Int) - 2)) (-2) (- (k :
  Int)) (sjsuPp 0 (- (k : Int)))) 7 = true := by
  decide +kernel

theorem pn_0_8 : (fun k : Nat => decide (k < 3) || sjsuHD.powOk 0 (- ((k : Int) - 2)) (-2) (- (k :
  Int)) (sjsuPp 0 (- (k : Int)))) 8 = true := by
  decide +kernel

theorem pn_0_9 : (fun k : Nat => decide (k < 3) || sjsuHD.powOk 0 (- ((k : Int) - 2)) (-2) (- (k :
  Int)) (sjsuPp 0 (- (k : Int)))) 9 = true := by
  decide +kernel


end KAM.EffectiveStability.SJSU

end
