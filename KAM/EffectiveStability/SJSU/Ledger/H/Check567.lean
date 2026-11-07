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

theorem vv_15_2_0 : (fun m2 : Nat => (sjsuHD.vIdx 15 m2 2).isEmpty || sjsuHD.vOk 15 m2 2 (sjsuUp 15
  2) (((sjsuVp 15 2).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 0 = true := by
  decide +kernel

theorem vv_15_2_1 : (fun m2 : Nat => (sjsuHD.vIdx 15 m2 2).isEmpty || sjsuHD.vOk 15 m2 2 (sjsuUp 15
  2) (((sjsuVp 15 2).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 1 = true := by
  decide +kernel

theorem vv_15_2_2 : (fun m2 : Nat => (sjsuHD.vIdx 15 m2 2).isEmpty || sjsuHD.vOk 15 m2 2 (sjsuUp 15
  2) (((sjsuVp 15 2).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 2 = true := by
  decide +kernel

theorem vv_15_2_3 : (fun m2 : Nat => (sjsuHD.vIdx 15 m2 2).isEmpty || sjsuHD.vOk 15 m2 2 (sjsuUp 15
  2) (((sjsuVp 15 2).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 3 = true := by
  decide +kernel

theorem vv_15_2_4 : (fun m2 : Nat => (sjsuHD.vIdx 15 m2 2).isEmpty || sjsuHD.vOk 15 m2 2 (sjsuUp 15
  2) (((sjsuVp 15 2).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 4 = true := by
  decide +kernel

theorem vv_15_2_5 : (fun m2 : Nat => (sjsuHD.vIdx 15 m2 2).isEmpty || sjsuHD.vOk 15 m2 2 (sjsuUp 15
  2) (((sjsuVp 15 2).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 5 = true := by
  decide +kernel

theorem vv_15_2_6 : (fun m2 : Nat => (sjsuHD.vIdx 15 m2 2).isEmpty || sjsuHD.vOk 15 m2 2 (sjsuUp 15
  2) (((sjsuVp 15 2).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 6 = true := by
  decide +kernel

theorem vv_15_2_7 : (fun m2 : Nat => (sjsuHD.vIdx 15 m2 2).isEmpty || sjsuHD.vOk 15 m2 2 (sjsuUp 15
  2) (((sjsuVp 15 2).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 7 = true := by
  decide +kernel

theorem vu_15_3_0 : (fun n2 : Nat => (sjsuHD.uIdx 15 n2 3).isEmpty || sjsuHD.uOk 15 n2 3 (uPrmOf (
  sjsuUp 15 3) n2)) 0 = true := by
  decide +kernel

theorem vu_15_3_1 : (fun n2 : Nat => (sjsuHD.uIdx 15 n2 3).isEmpty || sjsuHD.uOk 15 n2 3 (uPrmOf (
  sjsuUp 15 3) n2)) 1 = true := by
  decide +kernel

theorem vu_15_3_2 : (fun n2 : Nat => (sjsuHD.uIdx 15 n2 3).isEmpty || sjsuHD.uOk 15 n2 3 (uPrmOf (
  sjsuUp 15 3) n2)) 2 = true := by
  decide +kernel

theorem vu_15_3_3 : (fun n2 : Nat => (sjsuHD.uIdx 15 n2 3).isEmpty || sjsuHD.uOk 15 n2 3 (uPrmOf (
  sjsuUp 15 3) n2)) 3 = true := by
  decide +kernel

theorem vv_15_3_0 : (fun m2 : Nat => (sjsuHD.vIdx 15 m2 3).isEmpty || sjsuHD.vOk 15 m2 3 (sjsuUp 15
  3) (((sjsuVp 15 3).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 0 = true := by
  decide +kernel


end KAM.EffectiveStability.SJSU

end
