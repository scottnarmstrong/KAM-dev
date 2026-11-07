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

theorem vu_4_3_11 : (fun n2 : Nat => (sjsuHD.uIdx 4 n2 3).isEmpty || sjsuHD.uOk 4 n2 3 (uPrmOf (
  sjsuUp 4 3) n2)) 11 = true := by
  decide +kernel

theorem vu_4_3_12 : (fun n2 : Nat => (sjsuHD.uIdx 4 n2 3).isEmpty || sjsuHD.uOk 4 n2 3 (uPrmOf (
  sjsuUp 4 3) n2)) 12 = true := by
  decide +kernel

theorem vu_4_3_13 : (fun n2 : Nat => (sjsuHD.uIdx 4 n2 3).isEmpty || sjsuHD.uOk 4 n2 3 (uPrmOf (
  sjsuUp 4 3) n2)) 13 = true := by
  decide +kernel

theorem vu_4_3_14 : (fun n2 : Nat => (sjsuHD.uIdx 4 n2 3).isEmpty || sjsuHD.uOk 4 n2 3 (uPrmOf (
  sjsuUp 4 3) n2)) 14 = true := by
  decide +kernel

theorem vv_4_3_0 : (fun m2 : Nat => (sjsuHD.vIdx 4 m2 3).isEmpty || sjsuHD.vOk 4 m2 3 (sjsuUp 4 3) (
  ((sjsuVp 4 3).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 0 = true := by
  decide +kernel

theorem vv_4_3_1 : (fun m2 : Nat => (sjsuHD.vIdx 4 m2 3).isEmpty || sjsuHD.vOk 4 m2 3 (sjsuUp 4 3) (
  ((sjsuVp 4 3).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 1 = true := by
  decide +kernel

theorem vv_4_3_2 : (fun m2 : Nat => (sjsuHD.vIdx 4 m2 3).isEmpty || sjsuHD.vOk 4 m2 3 (sjsuUp 4 3) (
  ((sjsuVp 4 3).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 2 = true := by
  decide +kernel


end KAM.EffectiveStability.SJSU

end
