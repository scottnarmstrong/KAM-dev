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

theorem vu_10_0_4 : (fun n2 : Nat => (sjsuHD.uIdx 10 n2 0).isEmpty || sjsuHD.uOk 10 n2 0 (uPrmOf (
  sjsuUp 10 0) n2)) 4 = true := by
  decide +kernel

theorem vu_10_0_5 : (fun n2 : Nat => (sjsuHD.uIdx 10 n2 0).isEmpty || sjsuHD.uOk 10 n2 0 (uPrmOf (
  sjsuUp 10 0) n2)) 5 = true := by
  decide +kernel

theorem vu_10_0_6 : (fun n2 : Nat => (sjsuHD.uIdx 10 n2 0).isEmpty || sjsuHD.uOk 10 n2 0 (uPrmOf (
  sjsuUp 10 0) n2)) 6 = true := by
  decide +kernel

theorem vu_10_0_7 : (fun n2 : Nat => (sjsuHD.uIdx 10 n2 0).isEmpty || sjsuHD.uOk 10 n2 0 (uPrmOf (
  sjsuUp 10 0) n2)) 7 = true := by
  decide +kernel

theorem vu_10_0_8 : (fun n2 : Nat => (sjsuHD.uIdx 10 n2 0).isEmpty || sjsuHD.uOk 10 n2 0 (uPrmOf (
  sjsuUp 10 0) n2)) 8 = true := by
  decide +kernel

theorem vv_10_0_0 : (fun m2 : Nat => (sjsuHD.vIdx 10 m2 0).isEmpty || sjsuHD.vOk 10 m2 0 (sjsuUp 10
  0) (((sjsuVp 10 0).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 0 = true := by
  decide +kernel


end KAM.EffectiveStability.SJSU

end
