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

theorem vu_5_4_0 : (fun n2 : Nat => (sjsuHD.uIdx 5 n2 4).isEmpty || sjsuHD.uOk 5 n2 4 (uPrmOf (
  sjsuUp 5 4) n2)) 0 = true := by
  decide +kernel

theorem vu_5_4_1 : (fun n2 : Nat => (sjsuHD.uIdx 5 n2 4).isEmpty || sjsuHD.uOk 5 n2 4 (uPrmOf (
  sjsuUp 5 4) n2)) 1 = true := by
  decide +kernel

theorem vu_5_4_2 : (fun n2 : Nat => (sjsuHD.uIdx 5 n2 4).isEmpty || sjsuHD.uOk 5 n2 4 (uPrmOf (
  sjsuUp 5 4) n2)) 2 = true := by
  decide +kernel

theorem vu_5_4_3 : (fun n2 : Nat => (sjsuHD.uIdx 5 n2 4).isEmpty || sjsuHD.uOk 5 n2 4 (uPrmOf (
  sjsuUp 5 4) n2)) 3 = true := by
  decide +kernel

theorem vu_5_4_4 : (fun n2 : Nat => (sjsuHD.uIdx 5 n2 4).isEmpty || sjsuHD.uOk 5 n2 4 (uPrmOf (
  sjsuUp 5 4) n2)) 4 = true := by
  decide +kernel

theorem vu_5_4_5 : (fun n2 : Nat => (sjsuHD.uIdx 5 n2 4).isEmpty || sjsuHD.uOk 5 n2 4 (uPrmOf (
  sjsuUp 5 4) n2)) 5 = true := by
  decide +kernel

theorem vu_5_4_6 : (fun n2 : Nat => (sjsuHD.uIdx 5 n2 4).isEmpty || sjsuHD.uOk 5 n2 4 (uPrmOf (
  sjsuUp 5 4) n2)) 6 = true := by
  decide +kernel

theorem vu_5_4_7 : (fun n2 : Nat => (sjsuHD.uIdx 5 n2 4).isEmpty || sjsuHD.uOk 5 n2 4 (uPrmOf (
  sjsuUp 5 4) n2)) 7 = true := by
  decide +kernel

theorem vu_5_4_8 : (fun n2 : Nat => (sjsuHD.uIdx 5 n2 4).isEmpty || sjsuHD.uOk 5 n2 4 (uPrmOf (
  sjsuUp 5 4) n2)) 8 = true := by
  decide +kernel

theorem vu_5_4_9 : (fun n2 : Nat => (sjsuHD.uIdx 5 n2 4).isEmpty || sjsuHD.uOk 5 n2 4 (uPrmOf (
  sjsuUp 5 4) n2)) 9 = true := by
  decide +kernel


end KAM.EffectiveStability.SJSU

end
