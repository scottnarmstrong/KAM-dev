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

theorem vu_1_2_8 : (fun n2 : Nat => (sjsuHD.uIdx 1 n2 2).isEmpty || sjsuHD.uOk 1 n2 2 (uPrmOf (
  sjsuUp 1 2) n2)) 8 = true := by
  decide +kernel

theorem vu_1_2_9 : (fun n2 : Nat => (sjsuHD.uIdx 1 n2 2).isEmpty || sjsuHD.uOk 1 n2 2 (uPrmOf (
  sjsuUp 1 2) n2)) 9 = true := by
  decide +kernel

theorem vu_1_2_10 : (fun n2 : Nat => (sjsuHD.uIdx 1 n2 2).isEmpty || sjsuHD.uOk 1 n2 2 (uPrmOf (
  sjsuUp 1 2) n2)) 10 = true := by
  decide +kernel

theorem vu_1_2_11 : (fun n2 : Nat => (sjsuHD.uIdx 1 n2 2).isEmpty || sjsuHD.uOk 1 n2 2 (uPrmOf (
  sjsuUp 1 2) n2)) 11 = true := by
  decide +kernel

theorem vu_1_2_12 : (fun n2 : Nat => (sjsuHD.uIdx 1 n2 2).isEmpty || sjsuHD.uOk 1 n2 2 (uPrmOf (
  sjsuUp 1 2) n2)) 12 = true := by
  decide +kernel

theorem vu_1_2_13 : (fun n2 : Nat => (sjsuHD.uIdx 1 n2 2).isEmpty || sjsuHD.uOk 1 n2 2 (uPrmOf (
  sjsuUp 1 2) n2)) 13 = true := by
  decide +kernel

theorem vu_1_2_14 : (fun n2 : Nat => (sjsuHD.uIdx 1 n2 2).isEmpty || sjsuHD.uOk 1 n2 2 (uPrmOf (
  sjsuUp 1 2) n2)) 14 = true := by
  decide +kernel

theorem vu_1_2_15 : (fun n2 : Nat => (sjsuHD.uIdx 1 n2 2).isEmpty || sjsuHD.uOk 1 n2 2 (uPrmOf (
  sjsuUp 1 2) n2)) 15 = true := by
  decide +kernel

theorem vu_1_2_16 : (fun n2 : Nat => (sjsuHD.uIdx 1 n2 2).isEmpty || sjsuHD.uOk 1 n2 2 (uPrmOf (
  sjsuUp 1 2) n2)) 16 = true := by
  decide +kernel

theorem vu_1_2_17 : (fun n2 : Nat => (sjsuHD.uIdx 1 n2 2).isEmpty || sjsuHD.uOk 1 n2 2 (uPrmOf (
  sjsuUp 1 2) n2)) 17 = true := by
  decide +kernel


end KAM.EffectiveStability.SJSU

end
