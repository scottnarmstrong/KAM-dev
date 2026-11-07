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

theorem vv_8_6_2 : (fun m2 : Nat => (sjsuHD.vIdx 8 m2 6).isEmpty || sjsuHD.vOk 8 m2 6 (sjsuUp 8 6) (
  ((sjsuVp 8 6).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 2 = true := by
  decide +kernel

theorem vv_8_6_3 : (fun m2 : Nat => (sjsuHD.vIdx 8 m2 6).isEmpty || sjsuHD.vOk 8 m2 6 (sjsuUp 8 6) (
  ((sjsuVp 8 6).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 3 = true := by
  decide +kernel

theorem vu_8_7_0 : (fun n2 : Nat => (sjsuHD.uIdx 8 n2 7).isEmpty || sjsuHD.uOk 8 n2 7 (uPrmOf (
  sjsuUp 8 7) n2)) 0 = true := by
  decide +kernel

theorem vu_8_7_1 : (fun n2 : Nat => (sjsuHD.uIdx 8 n2 7).isEmpty || sjsuHD.uOk 8 n2 7 (uPrmOf (
  sjsuUp 8 7) n2)) 1 = true := by
  decide +kernel

theorem vu_8_7_2 : (fun n2 : Nat => (sjsuHD.uIdx 8 n2 7).isEmpty || sjsuHD.uOk 8 n2 7 (uPrmOf (
  sjsuUp 8 7) n2)) 2 = true := by
  decide +kernel

theorem vu_8_7_3 : (fun n2 : Nat => (sjsuHD.uIdx 8 n2 7).isEmpty || sjsuHD.uOk 8 n2 7 (uPrmOf (
  sjsuUp 8 7) n2)) 3 = true := by
  decide +kernel

theorem vu_8_7_4 : (fun n2 : Nat => (sjsuHD.uIdx 8 n2 7).isEmpty || sjsuHD.uOk 8 n2 7 (uPrmOf (
  sjsuUp 8 7) n2)) 4 = true := by
  decide +kernel

theorem vu_8_7_5 : (fun n2 : Nat => (sjsuHD.uIdx 8 n2 7).isEmpty || sjsuHD.uOk 8 n2 7 (uPrmOf (
  sjsuUp 8 7) n2)) 5 = true := by
  decide +kernel

theorem vu_8_7_6 : (fun n2 : Nat => (sjsuHD.uIdx 8 n2 7).isEmpty || sjsuHD.uOk 8 n2 7 (uPrmOf (
  sjsuUp 8 7) n2)) 6 = true := by
  decide +kernel

theorem vu_8_7_7 : (fun n2 : Nat => (sjsuHD.uIdx 8 n2 7).isEmpty || sjsuHD.uOk 8 n2 7 (uPrmOf (
  sjsuUp 8 7) n2)) 7 = true := by
  decide +kernel

theorem vu_8_7_8 : (fun n2 : Nat => (sjsuHD.uIdx 8 n2 7).isEmpty || sjsuHD.uOk 8 n2 7 (uPrmOf (
  sjsuUp 8 7) n2)) 8 = true := by
  decide +kernel


end KAM.EffectiveStability.SJSU

end
