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

theorem vv_16_0_8 : (fun m2 : Nat => (sjsuHD.vIdx 16 m2 0).isEmpty || sjsuHD.vOk 16 m2 0 (sjsuUp 16
  0) (((sjsuVp 16 0).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 8 = true := by
  decide +kernel

theorem vv_16_0_9 : (fun m2 : Nat => (sjsuHD.vIdx 16 m2 0).isEmpty || sjsuHD.vOk 16 m2 0 (sjsuUp 16
  0) (((sjsuVp 16 0).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 9 = true := by
  decide +kernel

theorem vu_16_1_0 : (fun n2 : Nat => (sjsuHD.uIdx 16 n2 1).isEmpty || sjsuHD.uOk 16 n2 1 (uPrmOf (
  sjsuUp 16 1) n2)) 0 = true := by
  decide +kernel

theorem vu_16_1_1 : (fun n2 : Nat => (sjsuHD.uIdx 16 n2 1).isEmpty || sjsuHD.uOk 16 n2 1 (uPrmOf (
  sjsuUp 16 1) n2)) 1 = true := by
  decide +kernel

theorem vu_16_1_2 : (fun n2 : Nat => (sjsuHD.uIdx 16 n2 1).isEmpty || sjsuHD.uOk 16 n2 1 (uPrmOf (
  sjsuUp 16 1) n2)) 2 = true := by
  decide +kernel

theorem vv_16_1_0 : (fun m2 : Nat => (sjsuHD.vIdx 16 m2 1).isEmpty || sjsuHD.vOk 16 m2 1 (sjsuUp 16
  1) (((sjsuVp 16 1).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 0 = true := by
  decide +kernel


end KAM.EffectiveStability.SJSU

end
