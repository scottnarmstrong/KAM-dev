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

theorem vu_7_2_6 : (fun n2 : Nat => (sjsuHD.uIdx 7 n2 2).isEmpty || sjsuHD.uOk 7 n2 2 (uPrmOf (
  sjsuUp 7 2) n2)) 6 = true := by
  decide +kernel

theorem vu_7_2_7 : (fun n2 : Nat => (sjsuHD.uIdx 7 n2 2).isEmpty || sjsuHD.uOk 7 n2 2 (uPrmOf (
  sjsuUp 7 2) n2)) 7 = true := by
  decide +kernel

theorem vu_7_2_8 : (fun n2 : Nat => (sjsuHD.uIdx 7 n2 2).isEmpty || sjsuHD.uOk 7 n2 2 (uPrmOf (
  sjsuUp 7 2) n2)) 8 = true := by
  decide +kernel

theorem vu_7_2_9 : (fun n2 : Nat => (sjsuHD.uIdx 7 n2 2).isEmpty || sjsuHD.uOk 7 n2 2 (uPrmOf (
  sjsuUp 7 2) n2)) 9 = true := by
  decide +kernel

theorem vu_7_2_10 : (fun n2 : Nat => (sjsuHD.uIdx 7 n2 2).isEmpty || sjsuHD.uOk 7 n2 2 (uPrmOf (
  sjsuUp 7 2) n2)) 10 = true := by
  decide +kernel

theorem vu_7_2_11 : (fun n2 : Nat => (sjsuHD.uIdx 7 n2 2).isEmpty || sjsuHD.uOk 7 n2 2 (uPrmOf (
  sjsuUp 7 2) n2)) 11 = true := by
  decide +kernel

theorem vv_7_2_0 : (fun m2 : Nat => (sjsuHD.vIdx 7 m2 2).isEmpty || sjsuHD.vOk 7 m2 2 (sjsuUp 7 2) (
  ((sjsuVp 7 2).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 0 = true := by
  decide +kernel

theorem vv_7_2_1 : (fun m2 : Nat => (sjsuHD.vIdx 7 m2 2).isEmpty || sjsuHD.vOk 7 m2 2 (sjsuUp 7 2) (
  ((sjsuVp 7 2).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 1 = true := by
  decide +kernel


end KAM.EffectiveStability.SJSU

end
