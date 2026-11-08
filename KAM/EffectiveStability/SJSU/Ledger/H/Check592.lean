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

theorem vv_17_1_0 : (fun m2 : Nat => (sjsuHD.vIdx 17 m2 1).isEmpty || sjsuHD.vOk 17 m2 1 (sjsuUp 17
  1) (((sjsuVp 17 1).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 0 = true := by
  decide +kernel

theorem vv_17_1_1 : (fun m2 : Nat => (sjsuHD.vIdx 17 m2 1).isEmpty || sjsuHD.vOk 17 m2 1 (sjsuUp 17
  1) (((sjsuVp 17 1).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 1 = true := by
  decide +kernel

theorem vv_17_1_2 : (fun m2 : Nat => (sjsuHD.vIdx 17 m2 1).isEmpty || sjsuHD.vOk 17 m2 1 (sjsuUp 17
  1) (((sjsuVp 17 1).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 2 = true := by
  decide +kernel

theorem vv_17_1_3 : (fun m2 : Nat => (sjsuHD.vIdx 17 m2 1).isEmpty || sjsuHD.vOk 17 m2 1 (sjsuUp 17
  1) (((sjsuVp 17 1).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 3 = true := by
  decide +kernel

theorem vv_17_1_4 : (fun m2 : Nat => (sjsuHD.vIdx 17 m2 1).isEmpty || sjsuHD.vOk 17 m2 1 (sjsuUp 17
  1) (((sjsuVp 17 1).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 4 = true := by
  decide +kernel

theorem vv_17_1_5 : (fun m2 : Nat => (sjsuHD.vIdx 17 m2 1).isEmpty || sjsuHD.vOk 17 m2 1 (sjsuUp 17
  1) (((sjsuVp 17 1).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 5 = true := by
  decide +kernel

theorem vv_17_1_6 : (fun m2 : Nat => (sjsuHD.vIdx 17 m2 1).isEmpty || sjsuHD.vOk 17 m2 1 (sjsuUp 17
  1) (((sjsuVp 17 1).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 6 = true := by
  decide +kernel

theorem vv_17_1_7 : (fun m2 : Nat => (sjsuHD.vIdx 17 m2 1).isEmpty || sjsuHD.vOk 17 m2 1 (sjsuUp 17
  1) (((sjsuVp 17 1).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 7 = true := by
  decide +kernel

theorem vv_17_1_8 : (fun m2 : Nat => (sjsuHD.vIdx 17 m2 1).isEmpty || sjsuHD.vOk 17 m2 1 (sjsuUp 17
  1) (((sjsuVp 17 1).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 8 = true := by
  decide +kernel

theorem vu_17_2_0 : (fun n2 : Nat => (sjsuHD.uIdx 17 n2 2).isEmpty || sjsuHD.uOk 17 n2 2 (uPrmOf (
  sjsuUp 17 2) n2)) 0 = true := by
  decide +kernel

theorem vu_17_2_1 : (fun n2 : Nat => (sjsuHD.uIdx 17 n2 2).isEmpty || sjsuHD.uOk 17 n2 2 (uPrmOf (
  sjsuUp 17 2) n2)) 1 = true := by
  decide +kernel

theorem vv_17_2_0 : (fun m2 : Nat => (sjsuHD.vIdx 17 m2 2).isEmpty || sjsuHD.vOk 17 m2 2 (sjsuUp 17
  2) (((sjsuVp 17 2).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 0 = true := by
  decide +kernel

theorem vv_17_2_1 : (fun m2 : Nat => (sjsuHD.vIdx 17 m2 2).isEmpty || sjsuHD.vOk 17 m2 2 (sjsuUp 17
  2) (((sjsuVp 17 2).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 1 = true := by
  decide +kernel

theorem vv_17_2_2 : (fun m2 : Nat => (sjsuHD.vIdx 17 m2 2).isEmpty || sjsuHD.vOk 17 m2 2 (sjsuUp 17
  2) (((sjsuVp 17 2).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 2 = true := by
  decide +kernel

theorem vv_17_2_3 : (fun m2 : Nat => (sjsuHD.vIdx 17 m2 2).isEmpty || sjsuHD.vOk 17 m2 2 (sjsuUp 17
  2) (((sjsuVp 17 2).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 3 = true := by
  decide +kernel

theorem vv_17_2_4 : (fun m2 : Nat => (sjsuHD.vIdx 17 m2 2).isEmpty || sjsuHD.vOk 17 m2 2 (sjsuUp 17
  2) (((sjsuVp 17 2).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 4 = true := by
  decide +kernel

theorem vv_17_2_5 : (fun m2 : Nat => (sjsuHD.vIdx 17 m2 2).isEmpty || sjsuHD.vOk 17 m2 2 (sjsuUp 17
  2) (((sjsuVp 17 2).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 5 = true := by
  decide +kernel

theorem vv_17_2_6 : (fun m2 : Nat => (sjsuHD.vIdx 17 m2 2).isEmpty || sjsuHD.vOk 17 m2 2 (sjsuUp 17
  2) (((sjsuVp 17 2).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 6 = true := by
  decide +kernel

theorem vv_17_2_7 : (fun m2 : Nat => (sjsuHD.vIdx 17 m2 2).isEmpty || sjsuHD.vOk 17 m2 2 (sjsuUp 17
  2) (((sjsuVp 17 2).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 7 = true := by
  decide +kernel

theorem vu_17_3_0 : (fun n2 : Nat => (sjsuHD.uIdx 17 n2 3).isEmpty || sjsuHD.uOk 17 n2 3 (uPrmOf (
  sjsuUp 17 3) n2)) 0 = true := by
  decide +kernel

theorem vu_17_3_1 : (fun n2 : Nat => (sjsuHD.uIdx 17 n2 3).isEmpty || sjsuHD.uOk 17 n2 3 (uPrmOf (
  sjsuUp 17 3) n2)) 1 = true := by
  decide +kernel

theorem vv_17_3_0 : (fun m2 : Nat => (sjsuHD.vIdx 17 m2 3).isEmpty || sjsuHD.vOk 17 m2 3 (sjsuUp 17
  3) (((sjsuVp 17 3).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 0 = true := by
  decide +kernel

theorem vv_17_3_1 : (fun m2 : Nat => (sjsuHD.vIdx 17 m2 3).isEmpty || sjsuHD.vOk 17 m2 3 (sjsuUp 17
  3) (((sjsuVp 17 3).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 1 = true := by
  decide +kernel

theorem vv_17_3_2 : (fun m2 : Nat => (sjsuHD.vIdx 17 m2 3).isEmpty || sjsuHD.vOk 17 m2 3 (sjsuUp 17
  3) (((sjsuVp 17 3).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 2 = true := by
  decide +kernel


end KAM.EffectiveStability.SJSU

end
