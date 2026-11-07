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

theorem vu_3_4_12 : (fun n2 : Nat => (sjsuHD.uIdx 3 n2 4).isEmpty || sjsuHD.uOk 3 n2 4 (uPrmOf (
  sjsuUp 3 4) n2)) 12 = true := by
  decide +kernel

theorem vu_3_4_13 : (fun n2 : Nat => (sjsuHD.uIdx 3 n2 4).isEmpty || sjsuHD.uOk 3 n2 4 (uPrmOf (
  sjsuUp 3 4) n2)) 13 = true := by
  decide +kernel

theorem vu_3_4_14 : (fun n2 : Nat => (sjsuHD.uIdx 3 n2 4).isEmpty || sjsuHD.uOk 3 n2 4 (uPrmOf (
  sjsuUp 3 4) n2)) 14 = true := by
  decide +kernel

theorem vu_3_4_15 : (fun n2 : Nat => (sjsuHD.uIdx 3 n2 4).isEmpty || sjsuHD.uOk 3 n2 4 (uPrmOf (
  sjsuUp 3 4) n2)) 15 = true := by
  decide +kernel

theorem vv_3_4_0 : (fun m2 : Nat => (sjsuHD.vIdx 3 m2 4).isEmpty || sjsuHD.vOk 3 m2 4 (sjsuUp 3 4) (
  ((sjsuVp 3 4).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 0 = true := by
  decide +kernel

theorem vv_3_4_1 : (fun m2 : Nat => (sjsuHD.vIdx 3 m2 4).isEmpty || sjsuHD.vOk 3 m2 4 (sjsuUp 3 4) (
  ((sjsuVp 3 4).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 1 = true := by
  decide +kernel

theorem vv_3_4_2 : (fun m2 : Nat => (sjsuHD.vIdx 3 m2 4).isEmpty || sjsuHD.vOk 3 m2 4 (sjsuUp 3 4) (
  ((sjsuVp 3 4).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 2 = true := by
  decide +kernel


end KAM.EffectiveStability.SJSU

end
