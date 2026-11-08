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

theorem vv_17_3_3 : (fun m2 : Nat => (sjsuHD.vIdx 17 m2 3).isEmpty || sjsuHD.vOk 17 m2 3 (sjsuUp 17
  3) (((sjsuVp 17 3).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 3 = true := by
  decide +kernel

theorem vv_17_3_4 : (fun m2 : Nat => (sjsuHD.vIdx 17 m2 3).isEmpty || sjsuHD.vOk 17 m2 3 (sjsuUp 17
  3) (((sjsuVp 17 3).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 4 = true := by
  decide +kernel

theorem vv_17_3_5 : (fun m2 : Nat => (sjsuHD.vIdx 17 m2 3).isEmpty || sjsuHD.vOk 17 m2 3 (sjsuUp 17
  3) (((sjsuVp 17 3).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 5 = true := by
  decide +kernel

theorem vv_17_3_6 : (fun m2 : Nat => (sjsuHD.vIdx 17 m2 3).isEmpty || sjsuHD.vOk 17 m2 3 (sjsuUp 17
  3) (((sjsuVp 17 3).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 6 = true := by
  decide +kernel

theorem vu_17_4_0 : (fun n2 : Nat => (sjsuHD.uIdx 17 n2 4).isEmpty || sjsuHD.uOk 17 n2 4 (uPrmOf (
  sjsuUp 17 4) n2)) 0 = true := by
  decide +kernel

theorem vu_17_4_1 : (fun n2 : Nat => (sjsuHD.uIdx 17 n2 4).isEmpty || sjsuHD.uOk 17 n2 4 (uPrmOf (
  sjsuUp 17 4) n2)) 1 = true := by
  decide +kernel

theorem vv_17_4_0 : (fun m2 : Nat => (sjsuHD.vIdx 17 m2 4).isEmpty || sjsuHD.vOk 17 m2 4 (sjsuUp 17
  4) (((sjsuVp 17 4).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 0 = true := by
  decide +kernel

theorem vv_17_4_1 : (fun m2 : Nat => (sjsuHD.vIdx 17 m2 4).isEmpty || sjsuHD.vOk 17 m2 4 (sjsuUp 17
  4) (((sjsuVp 17 4).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 1 = true := by
  decide +kernel

theorem vv_17_4_2 : (fun m2 : Nat => (sjsuHD.vIdx 17 m2 4).isEmpty || sjsuHD.vOk 17 m2 4 (sjsuUp 17
  4) (((sjsuVp 17 4).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 2 = true := by
  decide +kernel

theorem vv_17_4_3 : (fun m2 : Nat => (sjsuHD.vIdx 17 m2 4).isEmpty || sjsuHD.vOk 17 m2 4 (sjsuUp 17
  4) (((sjsuVp 17 4).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 3 = true := by
  decide +kernel

theorem vv_17_4_4 : (fun m2 : Nat => (sjsuHD.vIdx 17 m2 4).isEmpty || sjsuHD.vOk 17 m2 4 (sjsuUp 17
  4) (((sjsuVp 17 4).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 4 = true := by
  decide +kernel

theorem vv_17_4_5 : (fun m2 : Nat => (sjsuHD.vIdx 17 m2 4).isEmpty || sjsuHD.vOk 17 m2 4 (sjsuUp 17
  4) (((sjsuVp 17 4).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 5 = true := by
  decide +kernel

theorem vu_17_5_0 : (fun n2 : Nat => (sjsuHD.uIdx 17 n2 5).isEmpty || sjsuHD.uOk 17 n2 5 (uPrmOf (
  sjsuUp 17 5) n2)) 0 = true := by
  decide +kernel

theorem vu_17_5_1 : (fun n2 : Nat => (sjsuHD.uIdx 17 n2 5).isEmpty || sjsuHD.uOk 17 n2 5 (uPrmOf (
  sjsuUp 17 5) n2)) 1 = true := by
  decide +kernel

theorem vv_17_5_0 : (fun m2 : Nat => (sjsuHD.vIdx 17 m2 5).isEmpty || sjsuHD.vOk 17 m2 5 (sjsuUp 17
  5) (((sjsuVp 17 5).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 0 = true := by
  decide +kernel

theorem vv_17_5_1 : (fun m2 : Nat => (sjsuHD.vIdx 17 m2 5).isEmpty || sjsuHD.vOk 17 m2 5 (sjsuUp 17
  5) (((sjsuVp 17 5).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 1 = true := by
  decide +kernel

theorem vv_17_5_2 : (fun m2 : Nat => (sjsuHD.vIdx 17 m2 5).isEmpty || sjsuHD.vOk 17 m2 5 (sjsuUp 17
  5) (((sjsuVp 17 5).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 2 = true := by
  decide +kernel

theorem vv_17_5_3 : (fun m2 : Nat => (sjsuHD.vIdx 17 m2 5).isEmpty || sjsuHD.vOk 17 m2 5 (sjsuUp 17
  5) (((sjsuVp 17 5).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 3 = true := by
  decide +kernel

theorem vv_17_5_4 : (fun m2 : Nat => (sjsuHD.vIdx 17 m2 5).isEmpty || sjsuHD.vOk 17 m2 5 (sjsuUp 17
  5) (((sjsuVp 17 5).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 4 = true := by
  decide +kernel

theorem vu_17_6_0 : (fun n2 : Nat => (sjsuHD.uIdx 17 n2 6).isEmpty || sjsuHD.uOk 17 n2 6 (uPrmOf (
  sjsuUp 17 6) n2)) 0 = true := by
  decide +kernel

theorem vu_17_6_1 : (fun n2 : Nat => (sjsuHD.uIdx 17 n2 6).isEmpty || sjsuHD.uOk 17 n2 6 (uPrmOf (
  sjsuUp 17 6) n2)) 1 = true := by
  decide +kernel


end KAM.EffectiveStability.SJSU

end
