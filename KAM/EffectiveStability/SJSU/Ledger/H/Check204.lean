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

theorem vv_0_1_2 : (fun m2 : Nat => (sjsuHD.vIdx 0 m2 1).isEmpty || sjsuHD.vOk 0 m2 1 (sjsuUp 0 1) (
  ((sjsuVp 0 1).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 2 = true := by
  decide +kernel

theorem vv_0_1_3 : (fun m2 : Nat => (sjsuHD.vIdx 0 m2 1).isEmpty || sjsuHD.vOk 0 m2 1 (sjsuUp 0 1) (
  ((sjsuVp 0 1).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 3 = true := by
  decide +kernel

theorem vv_0_1_4 : (fun m2 : Nat => (sjsuHD.vIdx 0 m2 1).isEmpty || sjsuHD.vOk 0 m2 1 (sjsuUp 0 1) (
  ((sjsuVp 0 1).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 4 = true := by
  decide +kernel

theorem vv_0_1_5 : (fun m2 : Nat => (sjsuHD.vIdx 0 m2 1).isEmpty || sjsuHD.vOk 0 m2 1 (sjsuUp 0 1) (
  ((sjsuVp 0 1).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 5 = true := by
  decide +kernel


end KAM.EffectiveStability.SJSU

end
