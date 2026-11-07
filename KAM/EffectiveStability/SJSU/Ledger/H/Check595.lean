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

theorem vu_17_9_0 : (fun n2 : Nat => (sjsuHD.uIdx 17 n2 9).isEmpty || sjsuHD.uOk 17 n2 9 (uPrmOf (
  sjsuUp 17 9) n2)) 0 = true := by
  decide +kernel

theorem vu_17_9_1 : (fun n2 : Nat => (sjsuHD.uIdx 17 n2 9).isEmpty || sjsuHD.uOk 17 n2 9 (uPrmOf (
  sjsuUp 17 9) n2)) 1 = true := by
  decide +kernel

theorem vv_17_9_0 : (fun m2 : Nat => (sjsuHD.vIdx 17 m2 9).isEmpty || sjsuHD.vOk 17 m2 9 (sjsuUp 17
  9) (((sjsuVp 17 9).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 0 = true := by
  decide +kernel

theorem vu_18_0_0 : (fun n2 : Nat => (sjsuHD.uIdx 18 n2 0).isEmpty || sjsuHD.uOk 18 n2 0 (uPrmOf (
  sjsuUp 18 0) n2)) 0 = true := by
  decide +kernel

theorem vv_18_0_0 : (fun m2 : Nat => (sjsuHD.vIdx 18 m2 0).isEmpty || sjsuHD.vOk 18 m2 0 (sjsuUp 18
  0) (((sjsuVp 18 0).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 0 = true := by
  decide +kernel

theorem vv_18_0_1 : (fun m2 : Nat => (sjsuHD.vIdx 18 m2 0).isEmpty || sjsuHD.vOk 18 m2 0 (sjsuUp 18
  0) (((sjsuVp 18 0).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 1 = true := by
  decide +kernel

theorem vv_18_0_2 : (fun m2 : Nat => (sjsuHD.vIdx 18 m2 0).isEmpty || sjsuHD.vOk 18 m2 0 (sjsuUp 18
  0) (((sjsuVp 18 0).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 2 = true := by
  decide +kernel

theorem vv_18_0_3 : (fun m2 : Nat => (sjsuHD.vIdx 18 m2 0).isEmpty || sjsuHD.vOk 18 m2 0 (sjsuUp 18
  0) (((sjsuVp 18 0).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 3 = true := by
  decide +kernel

theorem vv_18_0_4 : (fun m2 : Nat => (sjsuHD.vIdx 18 m2 0).isEmpty || sjsuHD.vOk 18 m2 0 (sjsuUp 18
  0) (((sjsuVp 18 0).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 4 = true := by
  decide +kernel

theorem vv_18_0_5 : (fun m2 : Nat => (sjsuHD.vIdx 18 m2 0).isEmpty || sjsuHD.vOk 18 m2 0 (sjsuUp 18
  0) (((sjsuVp 18 0).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 5 = true := by
  decide +kernel

theorem vv_18_0_6 : (fun m2 : Nat => (sjsuHD.vIdx 18 m2 0).isEmpty || sjsuHD.vOk 18 m2 0 (sjsuUp 18
  0) (((sjsuVp 18 0).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 6 = true := by
  decide +kernel

theorem vv_18_0_7 : (fun m2 : Nat => (sjsuHD.vIdx 18 m2 0).isEmpty || sjsuHD.vOk 18 m2 0 (sjsuUp 18
  0) (((sjsuVp 18 0).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 7 = true := by
  decide +kernel

theorem vv_18_0_8 : (fun m2 : Nat => (sjsuHD.vIdx 18 m2 0).isEmpty || sjsuHD.vOk 18 m2 0 (sjsuUp 18
  0) (((sjsuVp 18 0).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 8 = true := by
  decide +kernel

theorem vv_18_0_9 : (fun m2 : Nat => (sjsuHD.vIdx 18 m2 0).isEmpty || sjsuHD.vOk 18 m2 0 (sjsuUp 18
  0) (((sjsuVp 18 0).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 9 = true := by
  decide +kernel

theorem vu_18_1_0 : (fun n2 : Nat => (sjsuHD.uIdx 18 n2 1).isEmpty || sjsuHD.uOk 18 n2 1 (uPrmOf (
  sjsuUp 18 1) n2)) 0 = true := by
  decide +kernel

theorem vv_18_1_0 : (fun m2 : Nat => (sjsuHD.vIdx 18 m2 1).isEmpty || sjsuHD.vOk 18 m2 1 (sjsuUp 18
  1) (((sjsuVp 18 1).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 0 = true := by
  decide +kernel

theorem vv_18_1_1 : (fun m2 : Nat => (sjsuHD.vIdx 18 m2 1).isEmpty || sjsuHD.vOk 18 m2 1 (sjsuUp 18
  1) (((sjsuVp 18 1).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 1 = true := by
  decide +kernel

theorem vv_18_1_2 : (fun m2 : Nat => (sjsuHD.vIdx 18 m2 1).isEmpty || sjsuHD.vOk 18 m2 1 (sjsuUp 18
  1) (((sjsuVp 18 1).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 2 = true := by
  decide +kernel

theorem vv_18_1_3 : (fun m2 : Nat => (sjsuHD.vIdx 18 m2 1).isEmpty || sjsuHD.vOk 18 m2 1 (sjsuUp 18
  1) (((sjsuVp 18 1).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 3 = true := by
  decide +kernel

theorem vv_18_1_4 : (fun m2 : Nat => (sjsuHD.vIdx 18 m2 1).isEmpty || sjsuHD.vOk 18 m2 1 (sjsuUp 18
  1) (((sjsuVp 18 1).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 4 = true := by
  decide +kernel

theorem vv_18_1_5 : (fun m2 : Nat => (sjsuHD.vIdx 18 m2 1).isEmpty || sjsuHD.vOk 18 m2 1 (sjsuUp 18
  1) (((sjsuVp 18 1).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 5 = true := by
  decide +kernel

theorem vv_18_1_6 : (fun m2 : Nat => (sjsuHD.vIdx 18 m2 1).isEmpty || sjsuHD.vOk 18 m2 1 (sjsuUp 18
  1) (((sjsuVp 18 1).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 6 = true := by
  decide +kernel

theorem vv_18_1_7 : (fun m2 : Nat => (sjsuHD.vIdx 18 m2 1).isEmpty || sjsuHD.vOk 18 m2 1 (sjsuUp 18
  1) (((sjsuVp 18 1).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 7 = true := by
  decide +kernel

theorem vv_18_1_8 : (fun m2 : Nat => (sjsuHD.vIdx 18 m2 1).isEmpty || sjsuHD.vOk 18 m2 1 (sjsuUp 18
  1) (((sjsuVp 18 1).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 8 = true := by
  decide +kernel


end KAM.EffectiveStability.SJSU

end
