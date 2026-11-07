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

theorem vu_1_6_10 : (fun n2 : Nat => (sjsuHD.uIdx 1 n2 6).isEmpty || sjsuHD.uOk 1 n2 6 (uPrmOf (
  sjsuUp 1 6) n2)) 10 = true := by
  decide +kernel

theorem vu_1_6_11 : (fun n2 : Nat => (sjsuHD.uIdx 1 n2 6).isEmpty || sjsuHD.uOk 1 n2 6 (uPrmOf (
  sjsuUp 1 6) n2)) 11 = true := by
  decide +kernel

theorem vu_1_6_12 : (fun n2 : Nat => (sjsuHD.uIdx 1 n2 6).isEmpty || sjsuHD.uOk 1 n2 6 (uPrmOf (
  sjsuUp 1 6) n2)) 12 = true := by
  decide +kernel

theorem vu_1_6_13 : (fun n2 : Nat => (sjsuHD.uIdx 1 n2 6).isEmpty || sjsuHD.uOk 1 n2 6 (uPrmOf (
  sjsuUp 1 6) n2)) 13 = true := by
  decide +kernel

theorem vu_1_6_14 : (fun n2 : Nat => (sjsuHD.uIdx 1 n2 6).isEmpty || sjsuHD.uOk 1 n2 6 (uPrmOf (
  sjsuUp 1 6) n2)) 14 = true := by
  decide +kernel

theorem vu_1_6_15 : (fun n2 : Nat => (sjsuHD.uIdx 1 n2 6).isEmpty || sjsuHD.uOk 1 n2 6 (uPrmOf (
  sjsuUp 1 6) n2)) 15 = true := by
  decide +kernel

theorem vu_1_6_16 : (fun n2 : Nat => (sjsuHD.uIdx 1 n2 6).isEmpty || sjsuHD.uOk 1 n2 6 (uPrmOf (
  sjsuUp 1 6) n2)) 16 = true := by
  decide +kernel

theorem vu_1_6_17 : (fun n2 : Nat => (sjsuHD.uIdx 1 n2 6).isEmpty || sjsuHD.uOk 1 n2 6 (uPrmOf (
  sjsuUp 1 6) n2)) 17 = true := by
  decide +kernel

theorem vv_1_6_0 : (fun m2 : Nat => (sjsuHD.vIdx 1 m2 6).isEmpty || sjsuHD.vOk 1 m2 6 (sjsuUp 1 6) (
  ((sjsuVp 1 6).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 0 = true := by
  decide +kernel

theorem vv_1_6_1 : (fun m2 : Nat => (sjsuHD.vIdx 1 m2 6).isEmpty || sjsuHD.vOk 1 m2 6 (sjsuUp 1 6) (
  ((sjsuVp 1 6).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 1 = true := by
  decide +kernel


end KAM.EffectiveStability.SJSU

end
