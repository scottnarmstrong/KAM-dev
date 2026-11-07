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

theorem vv_6_4_4 : (fun m2 : Nat => (sjsuHD.vIdx 6 m2 4).isEmpty || sjsuHD.vOk 6 m2 4 (sjsuUp 6 4) (
  ((sjsuVp 6 4).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 4 = true := by
  decide +kernel

theorem vv_6_4_5 : (fun m2 : Nat => (sjsuHD.vIdx 6 m2 4).isEmpty || sjsuHD.vOk 6 m2 4 (sjsuUp 6 4) (
  ((sjsuVp 6 4).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 5 = true := by
  decide +kernel

theorem vu_6_5_0 : (fun n2 : Nat => (sjsuHD.uIdx 6 n2 5).isEmpty || sjsuHD.uOk 6 n2 5 (uPrmOf (
  sjsuUp 6 5) n2)) 0 = true := by
  decide +kernel

theorem vu_6_5_1 : (fun n2 : Nat => (sjsuHD.uIdx 6 n2 5).isEmpty || sjsuHD.uOk 6 n2 5 (uPrmOf (
  sjsuUp 6 5) n2)) 1 = true := by
  decide +kernel

theorem vu_6_5_2 : (fun n2 : Nat => (sjsuHD.uIdx 6 n2 5).isEmpty || sjsuHD.uOk 6 n2 5 (uPrmOf (
  sjsuUp 6 5) n2)) 2 = true := by
  decide +kernel

theorem vu_6_5_3 : (fun n2 : Nat => (sjsuHD.uIdx 6 n2 5).isEmpty || sjsuHD.uOk 6 n2 5 (uPrmOf (
  sjsuUp 6 5) n2)) 3 = true := by
  decide +kernel

theorem vu_6_5_4 : (fun n2 : Nat => (sjsuHD.uIdx 6 n2 5).isEmpty || sjsuHD.uOk 6 n2 5 (uPrmOf (
  sjsuUp 6 5) n2)) 4 = true := by
  decide +kernel


end KAM.EffectiveStability.SJSU

end
