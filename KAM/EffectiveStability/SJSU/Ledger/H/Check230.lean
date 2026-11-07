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

theorem vu_1_0_10 : (fun n2 : Nat => (sjsuHD.uIdx 1 n2 0).isEmpty || sjsuHD.uOk 1 n2 0 (uPrmOf (
  sjsuUp 1 0) n2)) 10 = true := by
  decide +kernel

theorem vu_1_0_11 : (fun n2 : Nat => (sjsuHD.uIdx 1 n2 0).isEmpty || sjsuHD.uOk 1 n2 0 (uPrmOf (
  sjsuUp 1 0) n2)) 11 = true := by
  decide +kernel

theorem vu_1_0_12 : (fun n2 : Nat => (sjsuHD.uIdx 1 n2 0).isEmpty || sjsuHD.uOk 1 n2 0 (uPrmOf (
  sjsuUp 1 0) n2)) 12 = true := by
  decide +kernel

theorem vu_1_0_13 : (fun n2 : Nat => (sjsuHD.uIdx 1 n2 0).isEmpty || sjsuHD.uOk 1 n2 0 (uPrmOf (
  sjsuUp 1 0) n2)) 13 = true := by
  decide +kernel

theorem vu_1_0_14 : (fun n2 : Nat => (sjsuHD.uIdx 1 n2 0).isEmpty || sjsuHD.uOk 1 n2 0 (uPrmOf (
  sjsuUp 1 0) n2)) 14 = true := by
  decide +kernel

theorem vu_1_0_15 : (fun n2 : Nat => (sjsuHD.uIdx 1 n2 0).isEmpty || sjsuHD.uOk 1 n2 0 (uPrmOf (
  sjsuUp 1 0) n2)) 15 = true := by
  decide +kernel

theorem vu_1_0_16 : (fun n2 : Nat => (sjsuHD.uIdx 1 n2 0).isEmpty || sjsuHD.uOk 1 n2 0 (uPrmOf (
  sjsuUp 1 0) n2)) 16 = true := by
  decide +kernel

theorem vu_1_0_17 : (fun n2 : Nat => (sjsuHD.uIdx 1 n2 0).isEmpty || sjsuHD.uOk 1 n2 0 (uPrmOf (
  sjsuUp 1 0) n2)) 17 = true := by
  decide +kernel


end KAM.EffectiveStability.SJSU

end
