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

theorem vu_9_3_8 : (fun n2 : Nat => (sjsuHD.uIdx 9 n2 3).isEmpty || sjsuHD.uOk 9 n2 3 (uPrmOf (
  sjsuUp 9 3) n2)) 8 = true := by
  decide +kernel

theorem vu_9_3_9 : (fun n2 : Nat => (sjsuHD.uIdx 9 n2 3).isEmpty || sjsuHD.uOk 9 n2 3 (uPrmOf (
  sjsuUp 9 3) n2)) 9 = true := by
  decide +kernel

theorem vv_9_3_0 : (fun m2 : Nat => (sjsuHD.vIdx 9 m2 3).isEmpty || sjsuHD.vOk 9 m2 3 (sjsuUp 9 3) (
  ((sjsuVp 9 3).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 0 = true := by
  decide +kernel

theorem vv_9_3_1 : (fun m2 : Nat => (sjsuHD.vIdx 9 m2 3).isEmpty || sjsuHD.vOk 9 m2 3 (sjsuUp 9 3) (
  ((sjsuVp 9 3).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 1 = true := by
  decide +kernel

theorem vv_9_3_2 : (fun m2 : Nat => (sjsuHD.vIdx 9 m2 3).isEmpty || sjsuHD.vOk 9 m2 3 (sjsuUp 9 3) (
  ((sjsuVp 9 3).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 2 = true := by
  decide +kernel


end KAM.EffectiveStability.SJSU

end
