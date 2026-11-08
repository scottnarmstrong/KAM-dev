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

theorem vu_18_5_0 : (fun n2 : Nat => (sjsuHD.uIdx 18 n2 5).isEmpty || sjsuHD.uOk 18 n2 5 (uPrmOf (
  sjsuUp 18 5) n2)) 0 = true := by
  decide +kernel

theorem vv_18_5_0 : (fun m2 : Nat => (sjsuHD.vIdx 18 m2 5).isEmpty || sjsuHD.vOk 18 m2 5 (sjsuUp 18
  5) (((sjsuVp 18 5).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 0 = true := by
  decide +kernel

theorem vv_18_5_1 : (fun m2 : Nat => (sjsuHD.vIdx 18 m2 5).isEmpty || sjsuHD.vOk 18 m2 5 (sjsuUp 18
  5) (((sjsuVp 18 5).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 1 = true := by
  decide +kernel

theorem vv_18_5_2 : (fun m2 : Nat => (sjsuHD.vIdx 18 m2 5).isEmpty || sjsuHD.vOk 18 m2 5 (sjsuUp 18
  5) (((sjsuVp 18 5).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 2 = true := by
  decide +kernel

theorem vv_18_5_3 : (fun m2 : Nat => (sjsuHD.vIdx 18 m2 5).isEmpty || sjsuHD.vOk 18 m2 5 (sjsuUp 18
  5) (((sjsuVp 18 5).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 3 = true := by
  decide +kernel

theorem vv_18_5_4 : (fun m2 : Nat => (sjsuHD.vIdx 18 m2 5).isEmpty || sjsuHD.vOk 18 m2 5 (sjsuUp 18
  5) (((sjsuVp 18 5).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 4 = true := by
  decide +kernel

theorem vu_18_6_0 : (fun n2 : Nat => (sjsuHD.uIdx 18 n2 6).isEmpty || sjsuHD.uOk 18 n2 6 (uPrmOf (
  sjsuUp 18 6) n2)) 0 = true := by
  decide +kernel

theorem vv_18_6_0 : (fun m2 : Nat => (sjsuHD.vIdx 18 m2 6).isEmpty || sjsuHD.vOk 18 m2 6 (sjsuUp 18
  6) (((sjsuVp 18 6).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 0 = true := by
  decide +kernel

theorem vv_18_6_1 : (fun m2 : Nat => (sjsuHD.vIdx 18 m2 6).isEmpty || sjsuHD.vOk 18 m2 6 (sjsuUp 18
  6) (((sjsuVp 18 6).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 1 = true := by
  decide +kernel

theorem vv_18_6_2 : (fun m2 : Nat => (sjsuHD.vIdx 18 m2 6).isEmpty || sjsuHD.vOk 18 m2 6 (sjsuUp 18
  6) (((sjsuVp 18 6).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 2 = true := by
  decide +kernel

theorem vv_18_6_3 : (fun m2 : Nat => (sjsuHD.vIdx 18 m2 6).isEmpty || sjsuHD.vOk 18 m2 6 (sjsuUp 18
  6) (((sjsuVp 18 6).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 3 = true := by
  decide +kernel

theorem vu_18_7_0 : (fun n2 : Nat => (sjsuHD.uIdx 18 n2 7).isEmpty || sjsuHD.uOk 18 n2 7 (uPrmOf (
  sjsuUp 18 7) n2)) 0 = true := by
  decide +kernel

theorem vv_18_7_0 : (fun m2 : Nat => (sjsuHD.vIdx 18 m2 7).isEmpty || sjsuHD.vOk 18 m2 7 (sjsuUp 18
  7) (((sjsuVp 18 7).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 0 = true := by
  decide +kernel

theorem vv_18_7_1 : (fun m2 : Nat => (sjsuHD.vIdx 18 m2 7).isEmpty || sjsuHD.vOk 18 m2 7 (sjsuUp 18
  7) (((sjsuVp 18 7).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 1 = true := by
  decide +kernel

theorem vv_18_7_2 : (fun m2 : Nat => (sjsuHD.vIdx 18 m2 7).isEmpty || sjsuHD.vOk 18 m2 7 (sjsuUp 18
  7) (((sjsuVp 18 7).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 2 = true := by
  decide +kernel

theorem vu_18_8_0 : (fun n2 : Nat => (sjsuHD.uIdx 18 n2 8).isEmpty || sjsuHD.uOk 18 n2 8 (uPrmOf (
  sjsuUp 18 8) n2)) 0 = true := by
  decide +kernel

theorem vv_18_8_0 : (fun m2 : Nat => (sjsuHD.vIdx 18 m2 8).isEmpty || sjsuHD.vOk 18 m2 8 (sjsuUp 18
  8) (((sjsuVp 18 8).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 0 = true := by
  decide +kernel

theorem vv_18_8_1 : (fun m2 : Nat => (sjsuHD.vIdx 18 m2 8).isEmpty || sjsuHD.vOk 18 m2 8 (sjsuUp 18
  8) (((sjsuVp 18 8).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 1 = true := by
  decide +kernel

theorem vu_18_9_0 : (fun n2 : Nat => (sjsuHD.uIdx 18 n2 9).isEmpty || sjsuHD.uOk 18 n2 9 (uPrmOf (
  sjsuUp 18 9) n2)) 0 = true := by
  decide +kernel

theorem vv_18_9_0 : (fun m2 : Nat => (sjsuHD.vIdx 18 m2 9).isEmpty || sjsuHD.vOk 18 m2 9 (sjsuUp 18
  9) (((sjsuVp 18 9).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 0 = true := by
  decide +kernel

theorem hb_0_0_0 : ((sjsuHD.hIdx (0, 0, 0)).isEmpty || sjsuHD.hBlock (0, 0, 0) (sjsuHp (0, 0, 0))) =
  true := by
  decide +kernel

theorem hb_1_0_0 : ((sjsuHD.hIdx (1, 0, 0)).isEmpty || sjsuHD.hBlock (1, 0, 0) (sjsuHp (1, 0, 0))) =
  true := by
  decide +kernel

theorem hb_0_1_0 : ((sjsuHD.hIdx (0, 1, 0)).isEmpty || sjsuHD.hBlock (0, 1, 0) (sjsuHp (0, 1, 0))) =
  true := by
  decide +kernel

theorem hb_0_0_1 : ((sjsuHD.hIdx (0, 0, 1)).isEmpty || sjsuHD.hBlock (0, 0, 1) (sjsuHp (0, 0, 1))) =
  true := by
  decide +kernel


end KAM.EffectiveStability.SJSU

end
