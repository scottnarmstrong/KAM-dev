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

theorem vv_16_8_0 : (fun m2 : Nat => (sjsuHD.vIdx 16 m2 8).isEmpty || sjsuHD.vOk 16 m2 8 (sjsuUp 16
  8) (((sjsuVp 16 8).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 0 = true := by
  decide +kernel

theorem vv_16_8_1 : (fun m2 : Nat => (sjsuHD.vIdx 16 m2 8).isEmpty || sjsuHD.vOk 16 m2 8 (sjsuUp 16
  8) (((sjsuVp 16 8).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 1 = true := by
  decide +kernel

theorem vu_16_9_0 : (fun n2 : Nat => (sjsuHD.uIdx 16 n2 9).isEmpty || sjsuHD.uOk 16 n2 9 (uPrmOf (
  sjsuUp 16 9) n2)) 0 = true := by
  decide +kernel

theorem vu_16_9_1 : (fun n2 : Nat => (sjsuHD.uIdx 16 n2 9).isEmpty || sjsuHD.uOk 16 n2 9 (uPrmOf (
  sjsuUp 16 9) n2)) 1 = true := by
  decide +kernel

theorem vu_16_9_2 : (fun n2 : Nat => (sjsuHD.uIdx 16 n2 9).isEmpty || sjsuHD.uOk 16 n2 9 (uPrmOf (
  sjsuUp 16 9) n2)) 2 = true := by
  decide +kernel

theorem vv_16_9_0 : (fun m2 : Nat => (sjsuHD.vIdx 16 m2 9).isEmpty || sjsuHD.vOk 16 m2 9 (sjsuUp 16
  9) (((sjsuVp 16 9).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 0 = true := by
  decide +kernel

theorem vu_17_0_0 : (fun n2 : Nat => (sjsuHD.uIdx 17 n2 0).isEmpty || sjsuHD.uOk 17 n2 0 (uPrmOf (
  sjsuUp 17 0) n2)) 0 = true := by
  decide +kernel


end KAM.EffectiveStability.SJSU

end
