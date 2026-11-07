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

theorem vv_3_0_9 : (fun m2 : Nat => (sjsuHD.vIdx 3 m2 0).isEmpty || sjsuHD.vOk 3 m2 0 (sjsuUp 3 0) (
  ((sjsuVp 3 0).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 9 = true := by
  decide +kernel

theorem vu_3_1_0 : (fun n2 : Nat => (sjsuHD.uIdx 3 n2 1).isEmpty || sjsuHD.uOk 3 n2 1 (uPrmOf (
  sjsuUp 3 1) n2)) 0 = true := by
  decide +kernel

theorem vu_3_1_1 : (fun n2 : Nat => (sjsuHD.uIdx 3 n2 1).isEmpty || sjsuHD.uOk 3 n2 1 (uPrmOf (
  sjsuUp 3 1) n2)) 1 = true := by
  decide +kernel

theorem vu_3_1_2 : (fun n2 : Nat => (sjsuHD.uIdx 3 n2 1).isEmpty || sjsuHD.uOk 3 n2 1 (uPrmOf (
  sjsuUp 3 1) n2)) 2 = true := by
  decide +kernel

theorem vu_3_1_3 : (fun n2 : Nat => (sjsuHD.uIdx 3 n2 1).isEmpty || sjsuHD.uOk 3 n2 1 (uPrmOf (
  sjsuUp 3 1) n2)) 3 = true := by
  decide +kernel

theorem vu_3_1_4 : (fun n2 : Nat => (sjsuHD.uIdx 3 n2 1).isEmpty || sjsuHD.uOk 3 n2 1 (uPrmOf (
  sjsuUp 3 1) n2)) 4 = true := by
  decide +kernel

theorem vu_3_1_5 : (fun n2 : Nat => (sjsuHD.uIdx 3 n2 1).isEmpty || sjsuHD.uOk 3 n2 1 (uPrmOf (
  sjsuUp 3 1) n2)) 5 = true := by
  decide +kernel


end KAM.EffectiveStability.SJSU

end
