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

theorem pn_0_18 : (fun k : Nat => decide (k < 3) || sjsuHD.powOk 0 (- ((k : Int) - 2)) (-2) (- (k :
  Int)) (sjsuPp 0 (- (k : Int)))) 18 = true := by
  decide +kernel

theorem pn_0_19 : (fun k : Nat => decide (k < 3) || sjsuHD.powOk 0 (- ((k : Int) - 2)) (-2) (- (k :
  Int)) (sjsuPp 0 (- (k : Int)))) 19 = true := by
  decide +kernel


end KAM.EffectiveStability.SJSU

end
