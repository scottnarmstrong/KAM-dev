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

theorem vu_1_1_12 : (fun n2 : Nat => (sjsuHD.uIdx 1 n2 1).isEmpty || sjsuHD.uOk 1 n2 1 (uPrmOf (
  sjsuUp 1 1) n2)) 12 = true := by
  decide +kernel

theorem vu_1_1_13 : (fun n2 : Nat => (sjsuHD.uIdx 1 n2 1).isEmpty || sjsuHD.uOk 1 n2 1 (uPrmOf (
  sjsuUp 1 1) n2)) 13 = true := by
  decide +kernel

theorem vu_1_1_14 : (fun n2 : Nat => (sjsuHD.uIdx 1 n2 1).isEmpty || sjsuHD.uOk 1 n2 1 (uPrmOf (
  sjsuUp 1 1) n2)) 14 = true := by
  decide +kernel

theorem vu_1_1_15 : (fun n2 : Nat => (sjsuHD.uIdx 1 n2 1).isEmpty || sjsuHD.uOk 1 n2 1 (uPrmOf (
  sjsuUp 1 1) n2)) 15 = true := by
  decide +kernel

theorem vu_1_1_16 : (fun n2 : Nat => (sjsuHD.uIdx 1 n2 1).isEmpty || sjsuHD.uOk 1 n2 1 (uPrmOf (
  sjsuUp 1 1) n2)) 16 = true := by
  decide +kernel

theorem vu_1_1_17 : (fun n2 : Nat => (sjsuHD.uIdx 1 n2 1).isEmpty || sjsuHD.uOk 1 n2 1 (uPrmOf (
  sjsuUp 1 1) n2)) 17 = true := by
  decide +kernel

theorem vv_1_1_0 : (fun m2 : Nat => (sjsuHD.vIdx 1 m2 1).isEmpty || sjsuHD.vOk 1 m2 1 (sjsuUp 1 1) (
  ((sjsuVp 1 1).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 0 = true := by
  decide +kernel


end KAM.EffectiveStability.SJSU

end
