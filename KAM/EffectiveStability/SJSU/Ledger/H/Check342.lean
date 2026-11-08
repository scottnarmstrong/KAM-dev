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

theorem vu_4_7_3 : (fun n2 : Nat => (sjsuHD.uIdx 4 n2 7).isEmpty || sjsuHD.uOk 4 n2 7 (uPrmOf (
  sjsuUp 4 7) n2)) 3 = true := by
  decide +kernel

theorem vu_4_7_4 : (fun n2 : Nat => (sjsuHD.uIdx 4 n2 7).isEmpty || sjsuHD.uOk 4 n2 7 (uPrmOf (
  sjsuUp 4 7) n2)) 4 = true := by
  decide +kernel

theorem vu_4_7_5 : (fun n2 : Nat => (sjsuHD.uIdx 4 n2 7).isEmpty || sjsuHD.uOk 4 n2 7 (uPrmOf (
  sjsuUp 4 7) n2)) 5 = true := by
  decide +kernel

theorem vu_4_7_6 : (fun n2 : Nat => (sjsuHD.uIdx 4 n2 7).isEmpty || sjsuHD.uOk 4 n2 7 (uPrmOf (
  sjsuUp 4 7) n2)) 6 = true := by
  decide +kernel

theorem vu_4_7_7 : (fun n2 : Nat => (sjsuHD.uIdx 4 n2 7).isEmpty || sjsuHD.uOk 4 n2 7 (uPrmOf (
  sjsuUp 4 7) n2)) 7 = true := by
  decide +kernel

theorem vu_4_7_8 : (fun n2 : Nat => (sjsuHD.uIdx 4 n2 7).isEmpty || sjsuHD.uOk 4 n2 7 (uPrmOf (
  sjsuUp 4 7) n2)) 8 = true := by
  decide +kernel

theorem vu_4_7_9 : (fun n2 : Nat => (sjsuHD.uIdx 4 n2 7).isEmpty || sjsuHD.uOk 4 n2 7 (uPrmOf (
  sjsuUp 4 7) n2)) 9 = true := by
  decide +kernel

theorem vu_4_7_10 : (fun n2 : Nat => (sjsuHD.uIdx 4 n2 7).isEmpty || sjsuHD.uOk 4 n2 7 (uPrmOf (
  sjsuUp 4 7) n2)) 10 = true := by
  decide +kernel

theorem vu_4_7_11 : (fun n2 : Nat => (sjsuHD.uIdx 4 n2 7).isEmpty || sjsuHD.uOk 4 n2 7 (uPrmOf (
  sjsuUp 4 7) n2)) 11 = true := by
  decide +kernel

theorem vu_4_7_12 : (fun n2 : Nat => (sjsuHD.uIdx 4 n2 7).isEmpty || sjsuHD.uOk 4 n2 7 (uPrmOf (
  sjsuUp 4 7) n2)) 12 = true := by
  decide +kernel

theorem vu_4_7_13 : (fun n2 : Nat => (sjsuHD.uIdx 4 n2 7).isEmpty || sjsuHD.uOk 4 n2 7 (uPrmOf (
  sjsuUp 4 7) n2)) 13 = true := by
  decide +kernel

theorem vu_4_7_14 : (fun n2 : Nat => (sjsuHD.uIdx 4 n2 7).isEmpty || sjsuHD.uOk 4 n2 7 (uPrmOf (
  sjsuUp 4 7) n2)) 14 = true := by
  decide +kernel

theorem vv_4_7_0 : (fun m2 : Nat => (sjsuHD.vIdx 4 m2 7).isEmpty || sjsuHD.vOk 4 m2 7 (sjsuUp 4 7) (
  ((sjsuVp 4 7).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 0 = true := by
  decide +kernel


end KAM.EffectiveStability.SJSU

end
