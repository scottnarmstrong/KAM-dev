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

theorem vv_11_7_2 : (fun m2 : Nat => (sjsuHD.vIdx 11 m2 7).isEmpty || sjsuHD.vOk 11 m2 7 (sjsuUp 11
  7) (((sjsuVp 11 7).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 2 = true := by
  decide +kernel

theorem vu_11_8_0 : (fun n2 : Nat => (sjsuHD.uIdx 11 n2 8).isEmpty || sjsuHD.uOk 11 n2 8 (uPrmOf (
  sjsuUp 11 8) n2)) 0 = true := by
  decide +kernel

theorem vu_11_8_1 : (fun n2 : Nat => (sjsuHD.uIdx 11 n2 8).isEmpty || sjsuHD.uOk 11 n2 8 (uPrmOf (
  sjsuUp 11 8) n2)) 1 = true := by
  decide +kernel

theorem vu_11_8_2 : (fun n2 : Nat => (sjsuHD.uIdx 11 n2 8).isEmpty || sjsuHD.uOk 11 n2 8 (uPrmOf (
  sjsuUp 11 8) n2)) 2 = true := by
  decide +kernel

theorem vu_11_8_3 : (fun n2 : Nat => (sjsuHD.uIdx 11 n2 8).isEmpty || sjsuHD.uOk 11 n2 8 (uPrmOf (
  sjsuUp 11 8) n2)) 3 = true := by
  decide +kernel

theorem vu_11_8_4 : (fun n2 : Nat => (sjsuHD.uIdx 11 n2 8).isEmpty || sjsuHD.uOk 11 n2 8 (uPrmOf (
  sjsuUp 11 8) n2)) 4 = true := by
  decide +kernel

theorem vu_11_8_5 : (fun n2 : Nat => (sjsuHD.uIdx 11 n2 8).isEmpty || sjsuHD.uOk 11 n2 8 (uPrmOf (
  sjsuUp 11 8) n2)) 5 = true := by
  decide +kernel

theorem vu_11_8_6 : (fun n2 : Nat => (sjsuHD.uIdx 11 n2 8).isEmpty || sjsuHD.uOk 11 n2 8 (uPrmOf (
  sjsuUp 11 8) n2)) 6 = true := by
  decide +kernel

theorem vu_11_8_7 : (fun n2 : Nat => (sjsuHD.uIdx 11 n2 8).isEmpty || sjsuHD.uOk 11 n2 8 (uPrmOf (
  sjsuUp 11 8) n2)) 7 = true := by
  decide +kernel

theorem vv_11_8_0 : (fun m2 : Nat => (sjsuHD.vIdx 11 m2 8).isEmpty || sjsuHD.vOk 11 m2 8 (sjsuUp 11
  8) (((sjsuVp 11 8).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 0 = true := by
  decide +kernel


end KAM.EffectiveStability.SJSU

end
