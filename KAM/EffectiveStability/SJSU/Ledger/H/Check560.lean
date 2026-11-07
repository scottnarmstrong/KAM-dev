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

theorem vv_14_8_0 : (fun m2 : Nat => (sjsuHD.vIdx 14 m2 8).isEmpty || sjsuHD.vOk 14 m2 8 (sjsuUp 14
  8) (((sjsuVp 14 8).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 0 = true := by
  decide +kernel

theorem vv_14_8_1 : (fun m2 : Nat => (sjsuHD.vIdx 14 m2 8).isEmpty || sjsuHD.vOk 14 m2 8 (sjsuUp 14
  8) (((sjsuVp 14 8).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 1 = true := by
  decide +kernel

theorem vu_14_9_0 : (fun n2 : Nat => (sjsuHD.uIdx 14 n2 9).isEmpty || sjsuHD.uOk 14 n2 9 (uPrmOf (
  sjsuUp 14 9) n2)) 0 = true := by
  decide +kernel

theorem vu_14_9_1 : (fun n2 : Nat => (sjsuHD.uIdx 14 n2 9).isEmpty || sjsuHD.uOk 14 n2 9 (uPrmOf (
  sjsuUp 14 9) n2)) 1 = true := by
  decide +kernel

theorem vu_14_9_2 : (fun n2 : Nat => (sjsuHD.uIdx 14 n2 9).isEmpty || sjsuHD.uOk 14 n2 9 (uPrmOf (
  sjsuUp 14 9) n2)) 2 = true := by
  decide +kernel

theorem vu_14_9_3 : (fun n2 : Nat => (sjsuHD.uIdx 14 n2 9).isEmpty || sjsuHD.uOk 14 n2 9 (uPrmOf (
  sjsuUp 14 9) n2)) 3 = true := by
  decide +kernel

theorem vu_14_9_4 : (fun n2 : Nat => (sjsuHD.uIdx 14 n2 9).isEmpty || sjsuHD.uOk 14 n2 9 (uPrmOf (
  sjsuUp 14 9) n2)) 4 = true := by
  decide +kernel

theorem vv_14_9_0 : (fun m2 : Nat => (sjsuHD.vIdx 14 m2 9).isEmpty || sjsuHD.vOk 14 m2 9 (sjsuUp 14
  9) (((sjsuVp 14 9).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 0 = true := by
  decide +kernel


end KAM.EffectiveStability.SJSU

end
