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

theorem vv_11_3_5 : (fun m2 : Nat => (sjsuHD.vIdx 11 m2 3).isEmpty || sjsuHD.vOk 11 m2 3 (sjsuUp 11
  3) (((sjsuVp 11 3).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 5 = true := by
  decide +kernel

theorem vv_11_3_6 : (fun m2 : Nat => (sjsuHD.vIdx 11 m2 3).isEmpty || sjsuHD.vOk 11 m2 3 (sjsuUp 11
  3) (((sjsuVp 11 3).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 6 = true := by
  decide +kernel

theorem vu_11_4_0 : (fun n2 : Nat => (sjsuHD.uIdx 11 n2 4).isEmpty || sjsuHD.uOk 11 n2 4 (uPrmOf (
  sjsuUp 11 4) n2)) 0 = true := by
  decide +kernel

theorem vu_11_4_1 : (fun n2 : Nat => (sjsuHD.uIdx 11 n2 4).isEmpty || sjsuHD.uOk 11 n2 4 (uPrmOf (
  sjsuUp 11 4) n2)) 1 = true := by
  decide +kernel

theorem vu_11_4_2 : (fun n2 : Nat => (sjsuHD.uIdx 11 n2 4).isEmpty || sjsuHD.uOk 11 n2 4 (uPrmOf (
  sjsuUp 11 4) n2)) 2 = true := by
  decide +kernel

theorem vu_11_4_3 : (fun n2 : Nat => (sjsuHD.uIdx 11 n2 4).isEmpty || sjsuHD.uOk 11 n2 4 (uPrmOf (
  sjsuUp 11 4) n2)) 3 = true := by
  decide +kernel

theorem vu_11_4_4 : (fun n2 : Nat => (sjsuHD.uIdx 11 n2 4).isEmpty || sjsuHD.uOk 11 n2 4 (uPrmOf (
  sjsuUp 11 4) n2)) 4 = true := by
  decide +kernel

theorem vu_11_4_5 : (fun n2 : Nat => (sjsuHD.uIdx 11 n2 4).isEmpty || sjsuHD.uOk 11 n2 4 (uPrmOf (
  sjsuUp 11 4) n2)) 5 = true := by
  decide +kernel

theorem vu_11_4_6 : (fun n2 : Nat => (sjsuHD.uIdx 11 n2 4).isEmpty || sjsuHD.uOk 11 n2 4 (uPrmOf (
  sjsuUp 11 4) n2)) 6 = true := by
  decide +kernel

theorem vu_11_4_7 : (fun n2 : Nat => (sjsuHD.uIdx 11 n2 4).isEmpty || sjsuHD.uOk 11 n2 4 (uPrmOf (
  sjsuUp 11 4) n2)) 7 = true := by
  decide +kernel


end KAM.EffectiveStability.SJSU

end
