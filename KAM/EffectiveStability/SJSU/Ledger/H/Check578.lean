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

theorem vu_16_2_1 : (fun n2 : Nat => (sjsuHD.uIdx 16 n2 2).isEmpty || sjsuHD.uOk 16 n2 2 (uPrmOf (
  sjsuUp 16 2) n2)) 1 = true := by
  decide +kernel

theorem vu_16_2_2 : (fun n2 : Nat => (sjsuHD.uIdx 16 n2 2).isEmpty || sjsuHD.uOk 16 n2 2 (uPrmOf (
  sjsuUp 16 2) n2)) 2 = true := by
  decide +kernel

theorem vv_16_2_0 : (fun m2 : Nat => (sjsuHD.vIdx 16 m2 2).isEmpty || sjsuHD.vOk 16 m2 2 (sjsuUp 16
  2) (((sjsuVp 16 2).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 0 = true := by
  decide +kernel

theorem vv_16_2_1 : (fun m2 : Nat => (sjsuHD.vIdx 16 m2 2).isEmpty || sjsuHD.vOk 16 m2 2 (sjsuUp 16
  2) (((sjsuVp 16 2).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 1 = true := by
  decide +kernel

theorem vv_16_2_2 : (fun m2 : Nat => (sjsuHD.vIdx 16 m2 2).isEmpty || sjsuHD.vOk 16 m2 2 (sjsuUp 16
  2) (((sjsuVp 16 2).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 2 = true := by
  decide +kernel


end KAM.EffectiveStability.SJSU

end
