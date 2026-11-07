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

theorem vu_8_6_5 : (fun n2 : Nat => (sjsuHD.uIdx 8 n2 6).isEmpty || sjsuHD.uOk 8 n2 6 (uPrmOf (
  sjsuUp 8 6) n2)) 5 = true := by
  decide +kernel

theorem vu_8_6_6 : (fun n2 : Nat => (sjsuHD.uIdx 8 n2 6).isEmpty || sjsuHD.uOk 8 n2 6 (uPrmOf (
  sjsuUp 8 6) n2)) 6 = true := by
  decide +kernel

theorem vu_8_6_7 : (fun n2 : Nat => (sjsuHD.uIdx 8 n2 6).isEmpty || sjsuHD.uOk 8 n2 6 (uPrmOf (
  sjsuUp 8 6) n2)) 7 = true := by
  decide +kernel

theorem vu_8_6_8 : (fun n2 : Nat => (sjsuHD.uIdx 8 n2 6).isEmpty || sjsuHD.uOk 8 n2 6 (uPrmOf (
  sjsuUp 8 6) n2)) 8 = true := by
  decide +kernel

theorem vu_8_6_9 : (fun n2 : Nat => (sjsuHD.uIdx 8 n2 6).isEmpty || sjsuHD.uOk 8 n2 6 (uPrmOf (
  sjsuUp 8 6) n2)) 9 = true := by
  decide +kernel

theorem vu_8_6_10 : (fun n2 : Nat => (sjsuHD.uIdx 8 n2 6).isEmpty || sjsuHD.uOk 8 n2 6 (uPrmOf (
  sjsuUp 8 6) n2)) 10 = true := by
  decide +kernel

theorem vv_8_6_0 : (fun m2 : Nat => (sjsuHD.vIdx 8 m2 6).isEmpty || sjsuHD.vOk 8 m2 6 (sjsuUp 8 6) (
  ((sjsuVp 8 6).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 0 = true := by
  decide +kernel

theorem vv_8_6_1 : (fun m2 : Nat => (sjsuHD.vIdx 8 m2 6).isEmpty || sjsuHD.vOk 8 m2 6 (sjsuUp 8 6) (
  ((sjsuVp 8 6).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) 1 = true := by
  decide +kernel


end KAM.EffectiveStability.SJSU

end
