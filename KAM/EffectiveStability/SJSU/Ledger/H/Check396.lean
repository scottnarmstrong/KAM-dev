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

theorem vv_6_8_0 : (fun m2 : Nat => (sjsuHD.vIdx 6 m2 8).isEmpty || sjsuHD.vOk 6 m2 8 (sjsuUp 6 8) (
  ((sjsuVp 6 8).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 0 = true := by
  decide +kernel

theorem vv_6_8_1 : (fun m2 : Nat => (sjsuHD.vIdx 6 m2 8).isEmpty || sjsuHD.vOk 6 m2 8 (sjsuUp 6 8) (
  ((sjsuVp 6 8).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 1 = true := by
  decide +kernel

theorem vu_6_9_0 : (fun n2 : Nat => (sjsuHD.uIdx 6 n2 9).isEmpty || sjsuHD.uOk 6 n2 9 (uPrmOf (
  sjsuUp 6 9) n2)) 0 = true := by
  decide +kernel

theorem vu_6_9_1 : (fun n2 : Nat => (sjsuHD.uIdx 6 n2 9).isEmpty || sjsuHD.uOk 6 n2 9 (uPrmOf (
  sjsuUp 6 9) n2)) 1 = true := by
  decide +kernel

theorem vu_6_9_2 : (fun n2 : Nat => (sjsuHD.uIdx 6 n2 9).isEmpty || sjsuHD.uOk 6 n2 9 (uPrmOf (
  sjsuUp 6 9) n2)) 2 = true := by
  decide +kernel

theorem vu_6_9_3 : (fun n2 : Nat => (sjsuHD.uIdx 6 n2 9).isEmpty || sjsuHD.uOk 6 n2 9 (uPrmOf (
  sjsuUp 6 9) n2)) 3 = true := by
  decide +kernel

theorem vu_6_9_4 : (fun n2 : Nat => (sjsuHD.uIdx 6 n2 9).isEmpty || sjsuHD.uOk 6 n2 9 (uPrmOf (
  sjsuUp 6 9) n2)) 4 = true := by
  decide +kernel

theorem vu_6_9_5 : (fun n2 : Nat => (sjsuHD.uIdx 6 n2 9).isEmpty || sjsuHD.uOk 6 n2 9 (uPrmOf (
  sjsuUp 6 9) n2)) 5 = true := by
  decide +kernel

theorem vu_6_9_6 : (fun n2 : Nat => (sjsuHD.uIdx 6 n2 9).isEmpty || sjsuHD.uOk 6 n2 9 (uPrmOf (
  sjsuUp 6 9) n2)) 6 = true := by
  decide +kernel

theorem vu_6_9_7 : (fun n2 : Nat => (sjsuHD.uIdx 6 n2 9).isEmpty || sjsuHD.uOk 6 n2 9 (uPrmOf (
  sjsuUp 6 9) n2)) 7 = true := by
  decide +kernel

theorem vu_6_9_8 : (fun n2 : Nat => (sjsuHD.uIdx 6 n2 9).isEmpty || sjsuHD.uOk 6 n2 9 (uPrmOf (
  sjsuUp 6 9) n2)) 8 = true := by
  decide +kernel


end KAM.EffectiveStability.SJSU

end
