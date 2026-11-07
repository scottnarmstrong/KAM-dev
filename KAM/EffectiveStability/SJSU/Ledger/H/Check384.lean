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

theorem vu_6_3_2 : (fun n2 : Nat => (sjsuHD.uIdx 6 n2 3).isEmpty || sjsuHD.uOk 6 n2 3 (uPrmOf (
  sjsuUp 6 3) n2)) 2 = true := by
  decide +kernel

theorem vu_6_3_3 : (fun n2 : Nat => (sjsuHD.uIdx 6 n2 3).isEmpty || sjsuHD.uOk 6 n2 3 (uPrmOf (
  sjsuUp 6 3) n2)) 3 = true := by
  decide +kernel

theorem vu_6_3_4 : (fun n2 : Nat => (sjsuHD.uIdx 6 n2 3).isEmpty || sjsuHD.uOk 6 n2 3 (uPrmOf (
  sjsuUp 6 3) n2)) 4 = true := by
  decide +kernel

theorem vu_6_3_5 : (fun n2 : Nat => (sjsuHD.uIdx 6 n2 3).isEmpty || sjsuHD.uOk 6 n2 3 (uPrmOf (
  sjsuUp 6 3) n2)) 5 = true := by
  decide +kernel

theorem vu_6_3_6 : (fun n2 : Nat => (sjsuHD.uIdx 6 n2 3).isEmpty || sjsuHD.uOk 6 n2 3 (uPrmOf (
  sjsuUp 6 3) n2)) 6 = true := by
  decide +kernel

theorem vu_6_3_7 : (fun n2 : Nat => (sjsuHD.uIdx 6 n2 3).isEmpty || sjsuHD.uOk 6 n2 3 (uPrmOf (
  sjsuUp 6 3) n2)) 7 = true := by
  decide +kernel

theorem vu_6_3_8 : (fun n2 : Nat => (sjsuHD.uIdx 6 n2 3).isEmpty || sjsuHD.uOk 6 n2 3 (uPrmOf (
  sjsuUp 6 3) n2)) 8 = true := by
  decide +kernel

theorem vu_6_3_9 : (fun n2 : Nat => (sjsuHD.uIdx 6 n2 3).isEmpty || sjsuHD.uOk 6 n2 3 (uPrmOf (
  sjsuUp 6 3) n2)) 9 = true := by
  decide +kernel

theorem vu_6_3_10 : (fun n2 : Nat => (sjsuHD.uIdx 6 n2 3).isEmpty || sjsuHD.uOk 6 n2 3 (uPrmOf (
  sjsuUp 6 3) n2)) 10 = true := by
  decide +kernel

theorem vu_6_3_11 : (fun n2 : Nat => (sjsuHD.uIdx 6 n2 3).isEmpty || sjsuHD.uOk 6 n2 3 (uPrmOf (
  sjsuUp 6 3) n2)) 11 = true := by
  decide +kernel

theorem vu_6_3_12 : (fun n2 : Nat => (sjsuHD.uIdx 6 n2 3).isEmpty || sjsuHD.uOk 6 n2 3 (uPrmOf (
  sjsuUp 6 3) n2)) 12 = true := by
  decide +kernel


end KAM.EffectiveStability.SJSU

end
