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

theorem vu_5_5_2 : (fun n2 : Nat => (sjsuHD.uIdx 5 n2 5).isEmpty || sjsuHD.uOk 5 n2 5 (uPrmOf (
  sjsuUp 5 5) n2)) 2 = true := by
  decide +kernel

theorem vu_5_5_3 : (fun n2 : Nat => (sjsuHD.uIdx 5 n2 5).isEmpty || sjsuHD.uOk 5 n2 5 (uPrmOf (
  sjsuUp 5 5) n2)) 3 = true := by
  decide +kernel

theorem vu_5_5_4 : (fun n2 : Nat => (sjsuHD.uIdx 5 n2 5).isEmpty || sjsuHD.uOk 5 n2 5 (uPrmOf (
  sjsuUp 5 5) n2)) 4 = true := by
  decide +kernel

theorem vu_5_5_5 : (fun n2 : Nat => (sjsuHD.uIdx 5 n2 5).isEmpty || sjsuHD.uOk 5 n2 5 (uPrmOf (
  sjsuUp 5 5) n2)) 5 = true := by
  decide +kernel

theorem vu_5_5_6 : (fun n2 : Nat => (sjsuHD.uIdx 5 n2 5).isEmpty || sjsuHD.uOk 5 n2 5 (uPrmOf (
  sjsuUp 5 5) n2)) 6 = true := by
  decide +kernel

theorem vu_5_5_7 : (fun n2 : Nat => (sjsuHD.uIdx 5 n2 5).isEmpty || sjsuHD.uOk 5 n2 5 (uPrmOf (
  sjsuUp 5 5) n2)) 7 = true := by
  decide +kernel

theorem vu_5_5_8 : (fun n2 : Nat => (sjsuHD.uIdx 5 n2 5).isEmpty || sjsuHD.uOk 5 n2 5 (uPrmOf (
  sjsuUp 5 5) n2)) 8 = true := by
  decide +kernel

theorem vu_5_5_9 : (fun n2 : Nat => (sjsuHD.uIdx 5 n2 5).isEmpty || sjsuHD.uOk 5 n2 5 (uPrmOf (
  sjsuUp 5 5) n2)) 9 = true := by
  decide +kernel

theorem vu_5_5_10 : (fun n2 : Nat => (sjsuHD.uIdx 5 n2 5).isEmpty || sjsuHD.uOk 5 n2 5 (uPrmOf (
  sjsuUp 5 5) n2)) 10 = true := by
  decide +kernel

theorem vu_5_5_11 : (fun n2 : Nat => (sjsuHD.uIdx 5 n2 5).isEmpty || sjsuHD.uOk 5 n2 5 (uPrmOf (
  sjsuUp 5 5) n2)) 11 = true := by
  decide +kernel

theorem vu_5_5_12 : (fun n2 : Nat => (sjsuHD.uIdx 5 n2 5).isEmpty || sjsuHD.uOk 5 n2 5 (uPrmOf (
  sjsuUp 5 5) n2)) 12 = true := by
  decide +kernel

theorem vu_5_5_13 : (fun n2 : Nat => (sjsuHD.uIdx 5 n2 5).isEmpty || sjsuHD.uOk 5 n2 5 (uPrmOf (
  sjsuUp 5 5) n2)) 13 = true := by
  decide +kernel


end KAM.EffectiveStability.SJSU

end
