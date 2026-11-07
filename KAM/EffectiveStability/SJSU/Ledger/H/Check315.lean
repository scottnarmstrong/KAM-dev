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

theorem vv_3_7_0 : (fun m2 : Nat => (sjsuHD.vIdx 3 m2 7).isEmpty || sjsuHD.vOk 3 m2 7 (sjsuUp 3 7) (
  ((sjsuVp 3 7).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 0 = true := by
  decide +kernel

theorem vv_3_7_1 : (fun m2 : Nat => (sjsuHD.vIdx 3 m2 7).isEmpty || sjsuHD.vOk 3 m2 7 (sjsuUp 3 7) (
  ((sjsuVp 3 7).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 1 = true := by
  decide +kernel

theorem vv_3_7_2 : (fun m2 : Nat => (sjsuHD.vIdx 3 m2 7).isEmpty || sjsuHD.vOk 3 m2 7 (sjsuUp 3 7) (
  ((sjsuVp 3 7).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 2 = true := by
  decide +kernel

theorem vu_3_8_0 : (fun n2 : Nat => (sjsuHD.uIdx 3 n2 8).isEmpty || sjsuHD.uOk 3 n2 8 (uPrmOf (
  sjsuUp 3 8) n2)) 0 = true := by
  decide +kernel

theorem vu_3_8_1 : (fun n2 : Nat => (sjsuHD.uIdx 3 n2 8).isEmpty || sjsuHD.uOk 3 n2 8 (uPrmOf (
  sjsuUp 3 8) n2)) 1 = true := by
  decide +kernel

theorem vu_3_8_2 : (fun n2 : Nat => (sjsuHD.uIdx 3 n2 8).isEmpty || sjsuHD.uOk 3 n2 8 (uPrmOf (
  sjsuUp 3 8) n2)) 2 = true := by
  decide +kernel

theorem vu_3_8_3 : (fun n2 : Nat => (sjsuHD.uIdx 3 n2 8).isEmpty || sjsuHD.uOk 3 n2 8 (uPrmOf (
  sjsuUp 3 8) n2)) 3 = true := by
  decide +kernel


end KAM.EffectiveStability.SJSU

end
