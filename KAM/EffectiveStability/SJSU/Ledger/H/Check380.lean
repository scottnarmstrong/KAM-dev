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

theorem vv_6_1_8 : (fun m2 : Nat => (sjsuHD.vIdx 6 m2 1).isEmpty || sjsuHD.vOk 6 m2 1 (sjsuUp 6 1) (
  ((sjsuVp 6 1).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 8 = true := by
  decide +kernel

theorem vu_6_2_0 : (fun n2 : Nat => (sjsuHD.uIdx 6 n2 2).isEmpty || sjsuHD.uOk 6 n2 2 (uPrmOf (
  sjsuUp 6 2) n2)) 0 = true := by
  decide +kernel

theorem vu_6_2_1 : (fun n2 : Nat => (sjsuHD.uIdx 6 n2 2).isEmpty || sjsuHD.uOk 6 n2 2 (uPrmOf (
  sjsuUp 6 2) n2)) 1 = true := by
  decide +kernel

theorem vu_6_2_2 : (fun n2 : Nat => (sjsuHD.uIdx 6 n2 2).isEmpty || sjsuHD.uOk 6 n2 2 (uPrmOf (
  sjsuUp 6 2) n2)) 2 = true := by
  decide +kernel

theorem vu_6_2_3 : (fun n2 : Nat => (sjsuHD.uIdx 6 n2 2).isEmpty || sjsuHD.uOk 6 n2 2 (uPrmOf (
  sjsuUp 6 2) n2)) 3 = true := by
  decide +kernel

theorem vu_6_2_4 : (fun n2 : Nat => (sjsuHD.uIdx 6 n2 2).isEmpty || sjsuHD.uOk 6 n2 2 (uPrmOf (
  sjsuUp 6 2) n2)) 4 = true := by
  decide +kernel

theorem vu_6_2_5 : (fun n2 : Nat => (sjsuHD.uIdx 6 n2 2).isEmpty || sjsuHD.uOk 6 n2 2 (uPrmOf (
  sjsuUp 6 2) n2)) 5 = true := by
  decide +kernel


end KAM.EffectiveStability.SJSU

end
