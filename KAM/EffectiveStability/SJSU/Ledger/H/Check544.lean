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

theorem vu_14_0_1 : (fun n2 : Nat => (sjsuHD.uIdx 14 n2 0).isEmpty || sjsuHD.uOk 14 n2 0 (uPrmOf (
  sjsuUp 14 0) n2)) 1 = true := by
  decide +kernel

theorem vu_14_0_2 : (fun n2 : Nat => (sjsuHD.uIdx 14 n2 0).isEmpty || sjsuHD.uOk 14 n2 0 (uPrmOf (
  sjsuUp 14 0) n2)) 2 = true := by
  decide +kernel

theorem vu_14_0_3 : (fun n2 : Nat => (sjsuHD.uIdx 14 n2 0).isEmpty || sjsuHD.uOk 14 n2 0 (uPrmOf (
  sjsuUp 14 0) n2)) 3 = true := by
  decide +kernel

theorem vu_14_0_4 : (fun n2 : Nat => (sjsuHD.uIdx 14 n2 0).isEmpty || sjsuHD.uOk 14 n2 0 (uPrmOf (
  sjsuUp 14 0) n2)) 4 = true := by
  decide +kernel

theorem vv_14_0_0 : (fun m2 : Nat => (sjsuHD.vIdx 14 m2 0).isEmpty || sjsuHD.vOk 14 m2 0 (sjsuUp 14
  0) (((sjsuVp 14 0).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 0 = true := by
  decide +kernel

theorem vv_14_0_1 : (fun m2 : Nat => (sjsuHD.vIdx 14 m2 0).isEmpty || sjsuHD.vOk 14 m2 0 (sjsuUp 14
  0) (((sjsuVp 14 0).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 1 = true := by
  decide +kernel


end KAM.EffectiveStability.SJSU

end
