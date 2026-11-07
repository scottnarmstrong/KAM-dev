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

theorem vu_5_7_12 : (fun n2 : Nat => (sjsuHD.uIdx 5 n2 7).isEmpty || sjsuHD.uOk 5 n2 7 (uPrmOf (
  sjsuUp 5 7) n2)) 12 = true := by
  decide +kernel

theorem vu_5_7_13 : (fun n2 : Nat => (sjsuHD.uIdx 5 n2 7).isEmpty || sjsuHD.uOk 5 n2 7 (uPrmOf (
  sjsuUp 5 7) n2)) 13 = true := by
  decide +kernel

theorem vv_5_7_0 : (fun m2 : Nat => (sjsuHD.vIdx 5 m2 7).isEmpty || sjsuHD.vOk 5 m2 7 (sjsuUp 5 7) (
  ((sjsuVp 5 7).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 0 = true := by
  decide +kernel

theorem vv_5_7_1 : (fun m2 : Nat => (sjsuHD.vIdx 5 m2 7).isEmpty || sjsuHD.vOk 5 m2 7 (sjsuUp 5 7) (
  ((sjsuVp 5 7).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 1 = true := by
  decide +kernel

theorem vv_5_7_2 : (fun m2 : Nat => (sjsuHD.vIdx 5 m2 7).isEmpty || sjsuHD.vOk 5 m2 7 (sjsuUp 5 7) (
  ((sjsuVp 5 7).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 2 = true := by
  decide +kernel

theorem vu_5_8_0 : (fun n2 : Nat => (sjsuHD.uIdx 5 n2 8).isEmpty || sjsuHD.uOk 5 n2 8 (uPrmOf (
  sjsuUp 5 8) n2)) 0 = true := by
  decide +kernel

theorem vu_5_8_1 : (fun n2 : Nat => (sjsuHD.uIdx 5 n2 8).isEmpty || sjsuHD.uOk 5 n2 8 (uPrmOf (
  sjsuUp 5 8) n2)) 1 = true := by
  decide +kernel


end KAM.EffectiveStability.SJSU

end
