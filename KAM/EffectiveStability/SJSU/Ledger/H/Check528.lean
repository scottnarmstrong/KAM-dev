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

theorem vu_13_0_5 : (fun n2 : Nat => (sjsuHD.uIdx 13 n2 0).isEmpty || sjsuHD.uOk 13 n2 0 (uPrmOf (
  sjsuUp 13 0) n2)) 5 = true := by
  decide +kernel

theorem vv_13_0_0 : (fun m2 : Nat => (sjsuHD.vIdx 13 m2 0).isEmpty || sjsuHD.vOk 13 m2 0 (sjsuUp 13
  0) (((sjsuVp 13 0).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 0 = true := by
  decide +kernel

theorem vv_13_0_1 : (fun m2 : Nat => (sjsuHD.vIdx 13 m2 0).isEmpty || sjsuHD.vOk 13 m2 0 (sjsuUp 13
  0) (((sjsuVp 13 0).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 1 = true := by
  decide +kernel

theorem vv_13_0_2 : (fun m2 : Nat => (sjsuHD.vIdx 13 m2 0).isEmpty || sjsuHD.vOk 13 m2 0 (sjsuUp 13
  0) (((sjsuVp 13 0).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 2 = true := by
  decide +kernel


end KAM.EffectiveStability.SJSU

end
