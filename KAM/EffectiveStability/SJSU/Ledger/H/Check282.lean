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

theorem vv_2_5_4 : (fun m2 : Nat => (sjsuHD.vIdx 2 m2 5).isEmpty || sjsuHD.vOk 2 m2 5 (sjsuUp 2 5) (
  ((sjsuVp 2 5).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 4 = true := by
  decide +kernel

theorem vu_2_6_0 : (fun n2 : Nat => (sjsuHD.uIdx 2 n2 6).isEmpty || sjsuHD.uOk 2 n2 6 (uPrmOf (
  sjsuUp 2 6) n2)) 0 = true := by
  decide +kernel

theorem vu_2_6_1 : (fun n2 : Nat => (sjsuHD.uIdx 2 n2 6).isEmpty || sjsuHD.uOk 2 n2 6 (uPrmOf (
  sjsuUp 2 6) n2)) 1 = true := by
  decide +kernel

theorem vu_2_6_2 : (fun n2 : Nat => (sjsuHD.uIdx 2 n2 6).isEmpty || sjsuHD.uOk 2 n2 6 (uPrmOf (
  sjsuUp 2 6) n2)) 2 = true := by
  decide +kernel

theorem vu_2_6_3 : (fun n2 : Nat => (sjsuHD.uIdx 2 n2 6).isEmpty || sjsuHD.uOk 2 n2 6 (uPrmOf (
  sjsuUp 2 6) n2)) 3 = true := by
  decide +kernel

theorem vu_2_6_4 : (fun n2 : Nat => (sjsuHD.uIdx 2 n2 6).isEmpty || sjsuHD.uOk 2 n2 6 (uPrmOf (
  sjsuUp 2 6) n2)) 4 = true := by
  decide +kernel

theorem vu_2_6_5 : (fun n2 : Nat => (sjsuHD.uIdx 2 n2 6).isEmpty || sjsuHD.uOk 2 n2 6 (uPrmOf (
  sjsuUp 2 6) n2)) 5 = true := by
  decide +kernel

theorem vu_2_6_6 : (fun n2 : Nat => (sjsuHD.uIdx 2 n2 6).isEmpty || sjsuHD.uOk 2 n2 6 (uPrmOf (
  sjsuUp 2 6) n2)) 6 = true := by
  decide +kernel


end KAM.EffectiveStability.SJSU

end
