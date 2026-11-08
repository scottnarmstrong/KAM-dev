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

theorem vv_10_5_1 : (fun m2 : Nat => (sjsuHD.vIdx 10 m2 5).isEmpty || sjsuHD.vOk 10 m2 5 (sjsuUp 10
  5) (((sjsuVp 10 5).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 1 = true := by
  decide +kernel

theorem vv_10_5_2 : (fun m2 : Nat => (sjsuHD.vIdx 10 m2 5).isEmpty || sjsuHD.vOk 10 m2 5 (sjsuUp 10
  5) (((sjsuVp 10 5).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 2 = true := by
  decide +kernel

theorem vv_10_5_3 : (fun m2 : Nat => (sjsuHD.vIdx 10 m2 5).isEmpty || sjsuHD.vOk 10 m2 5 (sjsuUp 10
  5) (((sjsuVp 10 5).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 3 = true := by
  decide +kernel

theorem vv_10_5_4 : (fun m2 : Nat => (sjsuHD.vIdx 10 m2 5).isEmpty || sjsuHD.vOk 10 m2 5 (sjsuUp 10
  5) (((sjsuVp 10 5).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 4 = true := by
  decide +kernel

theorem vu_10_6_0 : (fun n2 : Nat => (sjsuHD.uIdx 10 n2 6).isEmpty || sjsuHD.uOk 10 n2 6 (uPrmOf (
  sjsuUp 10 6) n2)) 0 = true := by
  decide +kernel


end KAM.EffectiveStability.SJSU

end
