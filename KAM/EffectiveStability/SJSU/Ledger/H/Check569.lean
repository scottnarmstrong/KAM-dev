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

theorem vu_15_5_0 : (fun n2 : Nat => (sjsuHD.uIdx 15 n2 5).isEmpty || sjsuHD.uOk 15 n2 5 (uPrmOf (
  sjsuUp 15 5) n2)) 0 = true := by
  decide +kernel

theorem vu_15_5_1 : (fun n2 : Nat => (sjsuHD.uIdx 15 n2 5).isEmpty || sjsuHD.uOk 15 n2 5 (uPrmOf (
  sjsuUp 15 5) n2)) 1 = true := by
  decide +kernel

theorem vu_15_5_2 : (fun n2 : Nat => (sjsuHD.uIdx 15 n2 5).isEmpty || sjsuHD.uOk 15 n2 5 (uPrmOf (
  sjsuUp 15 5) n2)) 2 = true := by
  decide +kernel

theorem vu_15_5_3 : (fun n2 : Nat => (sjsuHD.uIdx 15 n2 5).isEmpty || sjsuHD.uOk 15 n2 5 (uPrmOf (
  sjsuUp 15 5) n2)) 3 = true := by
  decide +kernel

theorem vv_15_5_0 : (fun m2 : Nat => (sjsuHD.vIdx 15 m2 5).isEmpty || sjsuHD.vOk 15 m2 5 (sjsuUp 15
  5) (((sjsuVp 15 5).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 0 = true := by
  decide +kernel

theorem vv_15_5_1 : (fun m2 : Nat => (sjsuHD.vIdx 15 m2 5).isEmpty || sjsuHD.vOk 15 m2 5 (sjsuUp 15
  5) (((sjsuVp 15 5).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 1 = true := by
  decide +kernel

theorem vv_15_5_2 : (fun m2 : Nat => (sjsuHD.vIdx 15 m2 5).isEmpty || sjsuHD.vOk 15 m2 5 (sjsuUp 15
  5) (((sjsuVp 15 5).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 2 = true := by
  decide +kernel

theorem vv_15_5_3 : (fun m2 : Nat => (sjsuHD.vIdx 15 m2 5).isEmpty || sjsuHD.vOk 15 m2 5 (sjsuUp 15
  5) (((sjsuVp 15 5).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 3 = true := by
  decide +kernel

theorem vv_15_5_4 : (fun m2 : Nat => (sjsuHD.vIdx 15 m2 5).isEmpty || sjsuHD.vOk 15 m2 5 (sjsuUp 15
  5) (((sjsuVp 15 5).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 4 = true := by
  decide +kernel

theorem vu_15_6_0 : (fun n2 : Nat => (sjsuHD.uIdx 15 n2 6).isEmpty || sjsuHD.uOk 15 n2 6 (uPrmOf (
  sjsuUp 15 6) n2)) 0 = true := by
  decide +kernel

theorem vu_15_6_1 : (fun n2 : Nat => (sjsuHD.uIdx 15 n2 6).isEmpty || sjsuHD.uOk 15 n2 6 (uPrmOf (
  sjsuUp 15 6) n2)) 1 = true := by
  decide +kernel

theorem vu_15_6_2 : (fun n2 : Nat => (sjsuHD.uIdx 15 n2 6).isEmpty || sjsuHD.uOk 15 n2 6 (uPrmOf (
  sjsuUp 15 6) n2)) 2 = true := by
  decide +kernel

theorem vu_15_6_3 : (fun n2 : Nat => (sjsuHD.uIdx 15 n2 6).isEmpty || sjsuHD.uOk 15 n2 6 (uPrmOf (
  sjsuUp 15 6) n2)) 3 = true := by
  decide +kernel


end KAM.EffectiveStability.SJSU

end
