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

theorem vu_12_1_4 : (fun n2 : Nat => (sjsuHD.uIdx 12 n2 1).isEmpty || sjsuHD.uOk 12 n2 1 (uPrmOf (
  sjsuUp 12 1) n2)) 4 = true := by
  decide +kernel

theorem vu_12_1_5 : (fun n2 : Nat => (sjsuHD.uIdx 12 n2 1).isEmpty || sjsuHD.uOk 12 n2 1 (uPrmOf (
  sjsuUp 12 1) n2)) 5 = true := by
  decide +kernel

theorem vu_12_1_6 : (fun n2 : Nat => (sjsuHD.uIdx 12 n2 1).isEmpty || sjsuHD.uOk 12 n2 1 (uPrmOf (
  sjsuUp 12 1) n2)) 6 = true := by
  decide +kernel

theorem vv_12_1_0 : (fun m2 : Nat => (sjsuHD.vIdx 12 m2 1).isEmpty || sjsuHD.vOk 12 m2 1 (sjsuUp 12
  1) (((sjsuVp 12 1).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 0 = true := by
  decide +kernel

theorem vv_12_1_1 : (fun m2 : Nat => (sjsuHD.vIdx 12 m2 1).isEmpty || sjsuHD.vOk 12 m2 1 (sjsuUp 12
  1) (((sjsuVp 12 1).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 1 = true := by
  decide +kernel

theorem vv_12_1_2 : (fun m2 : Nat => (sjsuHD.vIdx 12 m2 1).isEmpty || sjsuHD.vOk 12 m2 1 (sjsuUp 12
  1) (((sjsuVp 12 1).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 2 = true := by
  decide +kernel


end KAM.EffectiveStability.SJSU

end
