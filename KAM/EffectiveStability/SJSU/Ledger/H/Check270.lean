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

theorem vu_2_2_10 : (fun n2 : Nat => (sjsuHD.uIdx 2 n2 2).isEmpty || sjsuHD.uOk 2 n2 2 (uPrmOf (
  sjsuUp 2 2) n2)) 10 = true := by
  decide +kernel

theorem vu_2_2_11 : (fun n2 : Nat => (sjsuHD.uIdx 2 n2 2).isEmpty || sjsuHD.uOk 2 n2 2 (uPrmOf (
  sjsuUp 2 2) n2)) 11 = true := by
  decide +kernel

theorem vu_2_2_12 : (fun n2 : Nat => (sjsuHD.uIdx 2 n2 2).isEmpty || sjsuHD.uOk 2 n2 2 (uPrmOf (
  sjsuUp 2 2) n2)) 12 = true := by
  decide +kernel

theorem vu_2_2_13 : (fun n2 : Nat => (sjsuHD.uIdx 2 n2 2).isEmpty || sjsuHD.uOk 2 n2 2 (uPrmOf (
  sjsuUp 2 2) n2)) 13 = true := by
  decide +kernel

theorem vu_2_2_14 : (fun n2 : Nat => (sjsuHD.uIdx 2 n2 2).isEmpty || sjsuHD.uOk 2 n2 2 (uPrmOf (
  sjsuUp 2 2) n2)) 14 = true := by
  decide +kernel

theorem vu_2_2_15 : (fun n2 : Nat => (sjsuHD.uIdx 2 n2 2).isEmpty || sjsuHD.uOk 2 n2 2 (uPrmOf (
  sjsuUp 2 2) n2)) 15 = true := by
  decide +kernel

theorem vu_2_2_16 : (fun n2 : Nat => (sjsuHD.uIdx 2 n2 2).isEmpty || sjsuHD.uOk 2 n2 2 (uPrmOf (
  sjsuUp 2 2) n2)) 16 = true := by
  decide +kernel

theorem vv_2_2_0 : (fun m2 : Nat => (sjsuHD.vIdx 2 m2 2).isEmpty || sjsuHD.vOk 2 m2 2 (sjsuUp 2 2) (
  ((sjsuVp 2 2).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 0 = true := by
  decide +kernel


end KAM.EffectiveStability.SJSU

end
