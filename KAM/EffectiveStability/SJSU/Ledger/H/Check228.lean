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

theorem vu_0_9_11 : (fun n2 : Nat => (sjsuHD.uIdx 0 n2 9).isEmpty || sjsuHD.uOk 0 n2 9 (uPrmOf (
  sjsuUp 0 9) n2)) 11 = true := by
  decide +kernel

theorem vu_0_9_12 : (fun n2 : Nat => (sjsuHD.uIdx 0 n2 9).isEmpty || sjsuHD.uOk 0 n2 9 (uPrmOf (
  sjsuUp 0 9) n2)) 12 = true := by
  decide +kernel

theorem vu_0_9_13 : (fun n2 : Nat => (sjsuHD.uIdx 0 n2 9).isEmpty || sjsuHD.uOk 0 n2 9 (uPrmOf (
  sjsuUp 0 9) n2)) 13 = true := by
  decide +kernel

theorem vu_0_9_14 : (fun n2 : Nat => (sjsuHD.uIdx 0 n2 9).isEmpty || sjsuHD.uOk 0 n2 9 (uPrmOf (
  sjsuUp 0 9) n2)) 14 = true := by
  decide +kernel

theorem vu_0_9_15 : (fun n2 : Nat => (sjsuHD.uIdx 0 n2 9).isEmpty || sjsuHD.uOk 0 n2 9 (uPrmOf (
  sjsuUp 0 9) n2)) 15 = true := by
  decide +kernel

theorem vu_0_9_16 : (fun n2 : Nat => (sjsuHD.uIdx 0 n2 9).isEmpty || sjsuHD.uOk 0 n2 9 (uPrmOf (
  sjsuUp 0 9) n2)) 16 = true := by
  decide +kernel

theorem vu_0_9_17 : (fun n2 : Nat => (sjsuHD.uIdx 0 n2 9).isEmpty || sjsuHD.uOk 0 n2 9 (uPrmOf (
  sjsuUp 0 9) n2)) 17 = true := by
  decide +kernel

theorem vu_0_9_18 : (fun n2 : Nat => (sjsuHD.uIdx 0 n2 9).isEmpty || sjsuHD.uOk 0 n2 9 (uPrmOf (
  sjsuUp 0 9) n2)) 18 = true := by
  decide +kernel

theorem vv_0_9_0 : (fun m2 : Nat => (sjsuHD.vIdx 0 m2 9).isEmpty || sjsuHD.vOk 0 m2 9 (sjsuUp 0 9) (
  ((sjsuVp 0 9).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 0 = true := by
  decide +kernel

theorem vu_1_0_0 : (fun n2 : Nat => (sjsuHD.uIdx 1 n2 0).isEmpty || sjsuHD.uOk 1 n2 0 (uPrmOf (
  sjsuUp 1 0) n2)) 0 = true := by
  decide +kernel

theorem vu_1_0_1 : (fun n2 : Nat => (sjsuHD.uIdx 1 n2 0).isEmpty || sjsuHD.uOk 1 n2 0 (uPrmOf (
  sjsuUp 1 0) n2)) 1 = true := by
  decide +kernel


end KAM.EffectiveStability.SJSU

end
