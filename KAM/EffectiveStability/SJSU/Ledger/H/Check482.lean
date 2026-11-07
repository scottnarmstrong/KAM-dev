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

theorem vv_10_4_5 : (fun m2 : Nat => (sjsuHD.vIdx 10 m2 4).isEmpty || sjsuHD.vOk 10 m2 4 (sjsuUp 10
  4) (((sjsuVp 10 4).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 5 = true := by
  decide +kernel

theorem vu_10_5_0 : (fun n2 : Nat => (sjsuHD.uIdx 10 n2 5).isEmpty || sjsuHD.uOk 10 n2 5 (uPrmOf (
  sjsuUp 10 5) n2)) 0 = true := by
  decide +kernel

theorem vu_10_5_1 : (fun n2 : Nat => (sjsuHD.uIdx 10 n2 5).isEmpty || sjsuHD.uOk 10 n2 5 (uPrmOf (
  sjsuUp 10 5) n2)) 1 = true := by
  decide +kernel

theorem vu_10_5_2 : (fun n2 : Nat => (sjsuHD.uIdx 10 n2 5).isEmpty || sjsuHD.uOk 10 n2 5 (uPrmOf (
  sjsuUp 10 5) n2)) 2 = true := by
  decide +kernel

theorem vu_10_5_3 : (fun n2 : Nat => (sjsuHD.uIdx 10 n2 5).isEmpty || sjsuHD.uOk 10 n2 5 (uPrmOf (
  sjsuUp 10 5) n2)) 3 = true := by
  decide +kernel

theorem vu_10_5_4 : (fun n2 : Nat => (sjsuHD.uIdx 10 n2 5).isEmpty || sjsuHD.uOk 10 n2 5 (uPrmOf (
  sjsuUp 10 5) n2)) 4 = true := by
  decide +kernel

theorem vu_10_5_5 : (fun n2 : Nat => (sjsuHD.uIdx 10 n2 5).isEmpty || sjsuHD.uOk 10 n2 5 (uPrmOf (
  sjsuUp 10 5) n2)) 5 = true := by
  decide +kernel

theorem vu_10_5_6 : (fun n2 : Nat => (sjsuHD.uIdx 10 n2 5).isEmpty || sjsuHD.uOk 10 n2 5 (uPrmOf (
  sjsuUp 10 5) n2)) 6 = true := by
  decide +kernel

theorem vu_10_5_7 : (fun n2 : Nat => (sjsuHD.uIdx 10 n2 5).isEmpty || sjsuHD.uOk 10 n2 5 (uPrmOf (
  sjsuUp 10 5) n2)) 7 = true := by
  decide +kernel

theorem vu_10_5_8 : (fun n2 : Nat => (sjsuHD.uIdx 10 n2 5).isEmpty || sjsuHD.uOk 10 n2 5 (uPrmOf (
  sjsuUp 10 5) n2)) 8 = true := by
  decide +kernel

theorem vv_10_5_0 : (fun m2 : Nat => (sjsuHD.vIdx 10 m2 5).isEmpty || sjsuHD.vOk 10 m2 5 (sjsuUp 10
  5) (((sjsuVp 10 5).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 0 = true := by
  decide +kernel


end KAM.EffectiveStability.SJSU

end
