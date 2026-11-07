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

theorem vu_7_9_4 : (fun n2 : Nat => (sjsuHD.uIdx 7 n2 9).isEmpty || sjsuHD.uOk 7 n2 9 (uPrmOf (
  sjsuUp 7 9) n2)) 4 = true := by
  decide +kernel

theorem vu_7_9_5 : (fun n2 : Nat => (sjsuHD.uIdx 7 n2 9).isEmpty || sjsuHD.uOk 7 n2 9 (uPrmOf (
  sjsuUp 7 9) n2)) 5 = true := by
  decide +kernel

theorem vu_7_9_6 : (fun n2 : Nat => (sjsuHD.uIdx 7 n2 9).isEmpty || sjsuHD.uOk 7 n2 9 (uPrmOf (
  sjsuUp 7 9) n2)) 6 = true := by
  decide +kernel

theorem vu_7_9_7 : (fun n2 : Nat => (sjsuHD.uIdx 7 n2 9).isEmpty || sjsuHD.uOk 7 n2 9 (uPrmOf (
  sjsuUp 7 9) n2)) 7 = true := by
  decide +kernel

theorem vu_7_9_8 : (fun n2 : Nat => (sjsuHD.uIdx 7 n2 9).isEmpty || sjsuHD.uOk 7 n2 9 (uPrmOf (
  sjsuUp 7 9) n2)) 8 = true := by
  decide +kernel

theorem vu_7_9_9 : (fun n2 : Nat => (sjsuHD.uIdx 7 n2 9).isEmpty || sjsuHD.uOk 7 n2 9 (uPrmOf (
  sjsuUp 7 9) n2)) 9 = true := by
  decide +kernel

theorem vu_7_9_10 : (fun n2 : Nat => (sjsuHD.uIdx 7 n2 9).isEmpty || sjsuHD.uOk 7 n2 9 (uPrmOf (
  sjsuUp 7 9) n2)) 10 = true := by
  decide +kernel

theorem vu_7_9_11 : (fun n2 : Nat => (sjsuHD.uIdx 7 n2 9).isEmpty || sjsuHD.uOk 7 n2 9 (uPrmOf (
  sjsuUp 7 9) n2)) 11 = true := by
  decide +kernel

theorem vv_7_9_0 : (fun m2 : Nat => (sjsuHD.vIdx 7 m2 9).isEmpty || sjsuHD.vOk 7 m2 9 (sjsuUp 7 9) (
  ((sjsuVp 7 9).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 0 = true := by
  decide +kernel

theorem vu_8_0_0 : (fun n2 : Nat => (sjsuHD.uIdx 8 n2 0).isEmpty || sjsuHD.uOk 8 n2 0 (uPrmOf (
  sjsuUp 8 0) n2)) 0 = true := by
  decide +kernel

theorem vu_8_0_1 : (fun n2 : Nat => (sjsuHD.uIdx 8 n2 0).isEmpty || sjsuHD.uOk 8 n2 0 (uPrmOf (
  sjsuUp 8 0) n2)) 1 = true := by
  decide +kernel


end KAM.EffectiveStability.SJSU

end
