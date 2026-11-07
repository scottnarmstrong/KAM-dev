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

theorem pm_2 : sjsuHD.powOk 2 (-1) (-1) (-2) (sjsuPp 2 (-2)) = true := by
  decide +kernel

theorem pn_2_3 : (fun k : Nat => decide (k < 3) || sjsuHD.powOk 2 (- ((k : Int) - 2)) (-2) (- (k :
  Int)) (sjsuPp 2 (- (k : Int)))) 3 = true := by
  decide +kernel

theorem pn_2_4 : (fun k : Nat => decide (k < 3) || sjsuHD.powOk 2 (- ((k : Int) - 2)) (-2) (- (k :
  Int)) (sjsuPp 2 (- (k : Int)))) 4 = true := by
  decide +kernel

theorem pn_2_5 : (fun k : Nat => decide (k < 3) || sjsuHD.powOk 2 (- ((k : Int) - 2)) (-2) (- (k :
  Int)) (sjsuPp 2 (- (k : Int)))) 5 = true := by
  decide +kernel

theorem pn_2_6 : (fun k : Nat => decide (k < 3) || sjsuHD.powOk 2 (- ((k : Int) - 2)) (-2) (- (k :
  Int)) (sjsuPp 2 (- (k : Int)))) 6 = true := by
  decide +kernel

theorem pn_2_7 : (fun k : Nat => decide (k < 3) || sjsuHD.powOk 2 (- ((k : Int) - 2)) (-2) (- (k :
  Int)) (sjsuPp 2 (- (k : Int)))) 7 = true := by
  decide +kernel

theorem pn_2_8 : (fun k : Nat => decide (k < 3) || sjsuHD.powOk 2 (- ((k : Int) - 2)) (-2) (- (k :
  Int)) (sjsuPp 2 (- (k : Int)))) 8 = true := by
  decide +kernel

theorem pn_2_9 : (fun k : Nat => decide (k < 3) || sjsuHD.powOk 2 (- ((k : Int) - 2)) (-2) (- (k :
  Int)) (sjsuPp 2 (- (k : Int)))) 9 = true := by
  decide +kernel


end KAM.EffectiveStability.SJSU

end
