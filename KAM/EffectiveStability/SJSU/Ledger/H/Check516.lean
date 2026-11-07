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

theorem vv_12_2_3 : (fun m2 : Nat => (sjsuHD.vIdx 12 m2 2).isEmpty || sjsuHD.vOk 12 m2 2 (sjsuUp 12
  2) (((sjsuVp 12 2).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 3 = true := by
  decide +kernel

theorem vv_12_2_4 : (fun m2 : Nat => (sjsuHD.vIdx 12 m2 2).isEmpty || sjsuHD.vOk 12 m2 2 (sjsuUp 12
  2) (((sjsuVp 12 2).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 4 = true := by
  decide +kernel

theorem vv_12_2_5 : (fun m2 : Nat => (sjsuHD.vIdx 12 m2 2).isEmpty || sjsuHD.vOk 12 m2 2 (sjsuUp 12
  2) (((sjsuVp 12 2).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 5 = true := by
  decide +kernel

theorem vv_12_2_6 : (fun m2 : Nat => (sjsuHD.vIdx 12 m2 2).isEmpty || sjsuHD.vOk 12 m2 2 (sjsuUp 12
  2) (((sjsuVp 12 2).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 6 = true := by
  decide +kernel


end KAM.EffectiveStability.SJSU

end
