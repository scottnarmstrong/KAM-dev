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

theorem vv_4_3_3 : (fun m2 : Nat => (sjsuHD.vIdx 4 m2 3).isEmpty || sjsuHD.vOk 4 m2 3 (sjsuUp 4 3) (
  ((sjsuVp 4 3).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 3 = true := by
  decide +kernel

theorem vv_4_3_4 : (fun m2 : Nat => (sjsuHD.vIdx 4 m2 3).isEmpty || sjsuHD.vOk 4 m2 3 (sjsuUp 4 3) (
  ((sjsuVp 4 3).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 4 = true := by
  decide +kernel

theorem vv_4_3_5 : (fun m2 : Nat => (sjsuHD.vIdx 4 m2 3).isEmpty || sjsuHD.vOk 4 m2 3 (sjsuUp 4 3) (
  ((sjsuVp 4 3).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 5 = true := by
  decide +kernel

theorem vv_4_3_6 : (fun m2 : Nat => (sjsuHD.vIdx 4 m2 3).isEmpty || sjsuHD.vOk 4 m2 3 (sjsuUp 4 3) (
  ((sjsuVp 4 3).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 6 = true := by
  decide +kernel


end KAM.EffectiveStability.SJSU

end
