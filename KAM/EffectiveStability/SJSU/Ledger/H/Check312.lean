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

theorem vu_3_6_4 : (fun n2 : Nat => (sjsuHD.uIdx 3 n2 6).isEmpty || sjsuHD.uOk 3 n2 6 (uPrmOf (
  sjsuUp 3 6) n2)) 4 = true := by
  decide +kernel

theorem vu_3_6_5 : (fun n2 : Nat => (sjsuHD.uIdx 3 n2 6).isEmpty || sjsuHD.uOk 3 n2 6 (uPrmOf (
  sjsuUp 3 6) n2)) 5 = true := by
  decide +kernel

theorem vu_3_6_6 : (fun n2 : Nat => (sjsuHD.uIdx 3 n2 6).isEmpty || sjsuHD.uOk 3 n2 6 (uPrmOf (
  sjsuUp 3 6) n2)) 6 = true := by
  decide +kernel

theorem vu_3_6_7 : (fun n2 : Nat => (sjsuHD.uIdx 3 n2 6).isEmpty || sjsuHD.uOk 3 n2 6 (uPrmOf (
  sjsuUp 3 6) n2)) 7 = true := by
  decide +kernel

theorem vu_3_6_8 : (fun n2 : Nat => (sjsuHD.uIdx 3 n2 6).isEmpty || sjsuHD.uOk 3 n2 6 (uPrmOf (
  sjsuUp 3 6) n2)) 8 = true := by
  decide +kernel

theorem vu_3_6_9 : (fun n2 : Nat => (sjsuHD.uIdx 3 n2 6).isEmpty || sjsuHD.uOk 3 n2 6 (uPrmOf (
  sjsuUp 3 6) n2)) 9 = true := by
  decide +kernel

theorem vu_3_6_10 : (fun n2 : Nat => (sjsuHD.uIdx 3 n2 6).isEmpty || sjsuHD.uOk 3 n2 6 (uPrmOf (
  sjsuUp 3 6) n2)) 10 = true := by
  decide +kernel

theorem vu_3_6_11 : (fun n2 : Nat => (sjsuHD.uIdx 3 n2 6).isEmpty || sjsuHD.uOk 3 n2 6 (uPrmOf (
  sjsuUp 3 6) n2)) 11 = true := by
  decide +kernel

theorem vu_3_6_12 : (fun n2 : Nat => (sjsuHD.uIdx 3 n2 6).isEmpty || sjsuHD.uOk 3 n2 6 (uPrmOf (
  sjsuUp 3 6) n2)) 12 = true := by
  decide +kernel

theorem vu_3_6_13 : (fun n2 : Nat => (sjsuHD.uIdx 3 n2 6).isEmpty || sjsuHD.uOk 3 n2 6 (uPrmOf (
  sjsuUp 3 6) n2)) 13 = true := by
  decide +kernel

theorem vu_3_6_14 : (fun n2 : Nat => (sjsuHD.uIdx 3 n2 6).isEmpty || sjsuHD.uOk 3 n2 6 (uPrmOf (
  sjsuUp 3 6) n2)) 14 = true := by
  decide +kernel

theorem vu_3_6_15 : (fun n2 : Nat => (sjsuHD.uIdx 3 n2 6).isEmpty || sjsuHD.uOk 3 n2 6 (uPrmOf (
  sjsuUp 3 6) n2)) 15 = true := by
  decide +kernel

theorem vv_3_6_0 : (fun m2 : Nat => (sjsuHD.vIdx 3 m2 6).isEmpty || sjsuHD.vOk 3 m2 6 (sjsuUp 3 6) (
  ((sjsuVp 3 6).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 0 = true := by
  decide +kernel


end KAM.EffectiveStability.SJSU

end
