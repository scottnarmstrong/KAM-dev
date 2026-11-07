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

theorem vv_17_6_0 : (fun m2 : Nat => (sjsuHD.vIdx 17 m2 6).isEmpty || sjsuHD.vOk 17 m2 6 (sjsuUp 17
  6) (((sjsuVp 17 6).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 0 = true := by
  decide +kernel

theorem vv_17_6_1 : (fun m2 : Nat => (sjsuHD.vIdx 17 m2 6).isEmpty || sjsuHD.vOk 17 m2 6 (sjsuUp 17
  6) (((sjsuVp 17 6).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 1 = true := by
  decide +kernel

theorem vv_17_6_2 : (fun m2 : Nat => (sjsuHD.vIdx 17 m2 6).isEmpty || sjsuHD.vOk 17 m2 6 (sjsuUp 17
  6) (((sjsuVp 17 6).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 2 = true := by
  decide +kernel

theorem vv_17_6_3 : (fun m2 : Nat => (sjsuHD.vIdx 17 m2 6).isEmpty || sjsuHD.vOk 17 m2 6 (sjsuUp 17
  6) (((sjsuVp 17 6).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 3 = true := by
  decide +kernel

theorem vu_17_7_0 : (fun n2 : Nat => (sjsuHD.uIdx 17 n2 7).isEmpty || sjsuHD.uOk 17 n2 7 (uPrmOf (
  sjsuUp 17 7) n2)) 0 = true := by
  decide +kernel

theorem vu_17_7_1 : (fun n2 : Nat => (sjsuHD.uIdx 17 n2 7).isEmpty || sjsuHD.uOk 17 n2 7 (uPrmOf (
  sjsuUp 17 7) n2)) 1 = true := by
  decide +kernel

theorem vv_17_7_0 : (fun m2 : Nat => (sjsuHD.vIdx 17 m2 7).isEmpty || sjsuHD.vOk 17 m2 7 (sjsuUp 17
  7) (((sjsuVp 17 7).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 0 = true := by
  decide +kernel

theorem vv_17_7_1 : (fun m2 : Nat => (sjsuHD.vIdx 17 m2 7).isEmpty || sjsuHD.vOk 17 m2 7 (sjsuUp 17
  7) (((sjsuVp 17 7).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 1 = true := by
  decide +kernel

theorem vv_17_7_2 : (fun m2 : Nat => (sjsuHD.vIdx 17 m2 7).isEmpty || sjsuHD.vOk 17 m2 7 (sjsuUp 17
  7) (((sjsuVp 17 7).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 2 = true := by
  decide +kernel

theorem vu_17_8_0 : (fun n2 : Nat => (sjsuHD.uIdx 17 n2 8).isEmpty || sjsuHD.uOk 17 n2 8 (uPrmOf (
  sjsuUp 17 8) n2)) 0 = true := by
  decide +kernel

theorem vu_17_8_1 : (fun n2 : Nat => (sjsuHD.uIdx 17 n2 8).isEmpty || sjsuHD.uOk 17 n2 8 (uPrmOf (
  sjsuUp 17 8) n2)) 1 = true := by
  decide +kernel

theorem vv_17_8_0 : (fun m2 : Nat => (sjsuHD.vIdx 17 m2 8).isEmpty || sjsuHD.vOk 17 m2 8 (sjsuUp 17
  8) (((sjsuVp 17 8).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 0 = true := by
  decide +kernel

theorem vv_17_8_1 : (fun m2 : Nat => (sjsuHD.vIdx 17 m2 8).isEmpty || sjsuHD.vOk 17 m2 8 (sjsuUp 17
  8) (((sjsuVp 17 8).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 1 = true := by
  decide +kernel


end KAM.EffectiveStability.SJSU

end
