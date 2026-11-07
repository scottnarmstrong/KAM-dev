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

theorem vu_2_0_1 : (fun n2 : Nat => (sjsuHD.uIdx 2 n2 0).isEmpty || sjsuHD.uOk 2 n2 0 (uPrmOf (
  sjsuUp 2 0) n2)) 1 = true := by
  decide +kernel

theorem vu_2_0_2 : (fun n2 : Nat => (sjsuHD.uIdx 2 n2 0).isEmpty || sjsuHD.uOk 2 n2 0 (uPrmOf (
  sjsuUp 2 0) n2)) 2 = true := by
  decide +kernel

theorem vu_2_0_3 : (fun n2 : Nat => (sjsuHD.uIdx 2 n2 0).isEmpty || sjsuHD.uOk 2 n2 0 (uPrmOf (
  sjsuUp 2 0) n2)) 3 = true := by
  decide +kernel

theorem vu_2_0_4 : (fun n2 : Nat => (sjsuHD.uIdx 2 n2 0).isEmpty || sjsuHD.uOk 2 n2 0 (uPrmOf (
  sjsuUp 2 0) n2)) 4 = true := by
  decide +kernel

theorem vu_2_0_5 : (fun n2 : Nat => (sjsuHD.uIdx 2 n2 0).isEmpty || sjsuHD.uOk 2 n2 0 (uPrmOf (
  sjsuUp 2 0) n2)) 5 = true := by
  decide +kernel

theorem vu_2_0_6 : (fun n2 : Nat => (sjsuHD.uIdx 2 n2 0).isEmpty || sjsuHD.uOk 2 n2 0 (uPrmOf (
  sjsuUp 2 0) n2)) 6 = true := by
  decide +kernel

theorem vu_2_0_7 : (fun n2 : Nat => (sjsuHD.uIdx 2 n2 0).isEmpty || sjsuHD.uOk 2 n2 0 (uPrmOf (
  sjsuUp 2 0) n2)) 7 = true := by
  decide +kernel

theorem vu_2_0_8 : (fun n2 : Nat => (sjsuHD.uIdx 2 n2 0).isEmpty || sjsuHD.uOk 2 n2 0 (uPrmOf (
  sjsuUp 2 0) n2)) 8 = true := by
  decide +kernel


end KAM.EffectiveStability.SJSU

end
