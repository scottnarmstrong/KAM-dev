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

theorem vu_5_9_12 : (fun n2 : Nat => (sjsuHD.uIdx 5 n2 9).isEmpty || sjsuHD.uOk 5 n2 9 (uPrmOf (
  sjsuUp 5 9) n2)) 12 = true := by
  decide +kernel

theorem vu_5_9_13 : (fun n2 : Nat => (sjsuHD.uIdx 5 n2 9).isEmpty || sjsuHD.uOk 5 n2 9 (uPrmOf (
  sjsuUp 5 9) n2)) 13 = true := by
  decide +kernel

theorem vv_5_9_0 : (fun m2 : Nat => (sjsuHD.vIdx 5 m2 9).isEmpty || sjsuHD.vOk 5 m2 9 (sjsuUp 5 9) (
  ((sjsuVp 5 9).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 0 = true := by
  decide +kernel

theorem vu_6_0_0 : (fun n2 : Nat => (sjsuHD.uIdx 6 n2 0).isEmpty || sjsuHD.uOk 6 n2 0 (uPrmOf (
  sjsuUp 6 0) n2)) 0 = true := by
  decide +kernel

theorem vu_6_0_1 : (fun n2 : Nat => (sjsuHD.uIdx 6 n2 0).isEmpty || sjsuHD.uOk 6 n2 0 (uPrmOf (
  sjsuUp 6 0) n2)) 1 = true := by
  decide +kernel

theorem vu_6_0_2 : (fun n2 : Nat => (sjsuHD.uIdx 6 n2 0).isEmpty || sjsuHD.uOk 6 n2 0 (uPrmOf (
  sjsuUp 6 0) n2)) 2 = true := by
  decide +kernel

theorem vu_6_0_3 : (fun n2 : Nat => (sjsuHD.uIdx 6 n2 0).isEmpty || sjsuHD.uOk 6 n2 0 (uPrmOf (
  sjsuUp 6 0) n2)) 3 = true := by
  decide +kernel

theorem vu_6_0_4 : (fun n2 : Nat => (sjsuHD.uIdx 6 n2 0).isEmpty || sjsuHD.uOk 6 n2 0 (uPrmOf (
  sjsuUp 6 0) n2)) 4 = true := by
  decide +kernel


end KAM.EffectiveStability.SJSU

end
