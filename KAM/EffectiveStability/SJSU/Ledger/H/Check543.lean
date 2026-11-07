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

theorem vv_13_8_1 : (fun m2 : Nat => (sjsuHD.vIdx 13 m2 8).isEmpty || sjsuHD.vOk 13 m2 8 (sjsuUp 13
  8) (((sjsuVp 13 8).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 1 = true := by
  decide +kernel

theorem vu_13_9_0 : (fun n2 : Nat => (sjsuHD.uIdx 13 n2 9).isEmpty || sjsuHD.uOk 13 n2 9 (uPrmOf (
  sjsuUp 13 9) n2)) 0 = true := by
  decide +kernel

theorem vu_13_9_1 : (fun n2 : Nat => (sjsuHD.uIdx 13 n2 9).isEmpty || sjsuHD.uOk 13 n2 9 (uPrmOf (
  sjsuUp 13 9) n2)) 1 = true := by
  decide +kernel

theorem vu_13_9_2 : (fun n2 : Nat => (sjsuHD.uIdx 13 n2 9).isEmpty || sjsuHD.uOk 13 n2 9 (uPrmOf (
  sjsuUp 13 9) n2)) 2 = true := by
  decide +kernel

theorem vu_13_9_3 : (fun n2 : Nat => (sjsuHD.uIdx 13 n2 9).isEmpty || sjsuHD.uOk 13 n2 9 (uPrmOf (
  sjsuUp 13 9) n2)) 3 = true := by
  decide +kernel

theorem vu_13_9_4 : (fun n2 : Nat => (sjsuHD.uIdx 13 n2 9).isEmpty || sjsuHD.uOk 13 n2 9 (uPrmOf (
  sjsuUp 13 9) n2)) 4 = true := by
  decide +kernel

theorem vu_13_9_5 : (fun n2 : Nat => (sjsuHD.uIdx 13 n2 9).isEmpty || sjsuHD.uOk 13 n2 9 (uPrmOf (
  sjsuUp 13 9) n2)) 5 = true := by
  decide +kernel

theorem vv_13_9_0 : (fun m2 : Nat => (sjsuHD.vIdx 13 m2 9).isEmpty || sjsuHD.vOk 13 m2 9 (sjsuUp 13
  9) (((sjsuVp 13 9).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 0 = true := by
  decide +kernel

theorem vu_14_0_0 : (fun n2 : Nat => (sjsuHD.uIdx 14 n2 0).isEmpty || sjsuHD.uOk 14 n2 0 (uPrmOf (
  sjsuUp 14 0) n2)) 0 = true := by
  decide +kernel


end KAM.EffectiveStability.SJSU

end
