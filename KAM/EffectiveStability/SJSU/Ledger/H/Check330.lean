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

theorem vv_4_2_5 : (fun m2 : Nat => (sjsuHD.vIdx 4 m2 2).isEmpty || sjsuHD.vOk 4 m2 2 (sjsuUp 4 2) (
  ((sjsuVp 4 2).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 5 = true := by
  decide +kernel

theorem vv_4_2_6 : (fun m2 : Nat => (sjsuHD.vIdx 4 m2 2).isEmpty || sjsuHD.vOk 4 m2 2 (sjsuUp 4 2) (
  ((sjsuVp 4 2).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 6 = true := by
  decide +kernel

theorem vv_4_2_7 : (fun m2 : Nat => (sjsuHD.vIdx 4 m2 2).isEmpty || sjsuHD.vOk 4 m2 2 (sjsuUp 4 2) (
  ((sjsuVp 4 2).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 7 = true := by
  decide +kernel

theorem vu_4_3_0 : (fun n2 : Nat => (sjsuHD.uIdx 4 n2 3).isEmpty || sjsuHD.uOk 4 n2 3 (uPrmOf (
  sjsuUp 4 3) n2)) 0 = true := by
  decide +kernel

theorem vu_4_3_1 : (fun n2 : Nat => (sjsuHD.uIdx 4 n2 3).isEmpty || sjsuHD.uOk 4 n2 3 (uPrmOf (
  sjsuUp 4 3) n2)) 1 = true := by
  decide +kernel


end KAM.EffectiveStability.SJSU

end
