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

theorem vv_16_0_4 : (fun m2 : Nat => (sjsuHD.vIdx 16 m2 0).isEmpty || sjsuHD.vOk 16 m2 0 (sjsuUp 16
  0) (((sjsuVp 16 0).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 4 = true := by
  decide +kernel

theorem vv_16_0_5 : (fun m2 : Nat => (sjsuHD.vIdx 16 m2 0).isEmpty || sjsuHD.vOk 16 m2 0 (sjsuUp 16
  0) (((sjsuVp 16 0).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 5 = true := by
  decide +kernel

theorem vv_16_0_6 : (fun m2 : Nat => (sjsuHD.vIdx 16 m2 0).isEmpty || sjsuHD.vOk 16 m2 0 (sjsuUp 16
  0) (((sjsuVp 16 0).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 6 = true := by
  decide +kernel

theorem vv_16_0_7 : (fun m2 : Nat => (sjsuHD.vIdx 16 m2 0).isEmpty || sjsuHD.vOk 16 m2 0 (sjsuUp 16
  0) (((sjsuVp 16 0).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 7 = true := by
  decide +kernel


end KAM.EffectiveStability.SJSU

end
