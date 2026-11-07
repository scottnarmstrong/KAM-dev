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

theorem vu_6_4_2 : (fun n2 : Nat => (sjsuHD.uIdx 6 n2 4).isEmpty || sjsuHD.uOk 6 n2 4 (uPrmOf (
  sjsuUp 6 4) n2)) 2 = true := by
  decide +kernel

theorem vu_6_4_3 : (fun n2 : Nat => (sjsuHD.uIdx 6 n2 4).isEmpty || sjsuHD.uOk 6 n2 4 (uPrmOf (
  sjsuUp 6 4) n2)) 3 = true := by
  decide +kernel

theorem vu_6_4_4 : (fun n2 : Nat => (sjsuHD.uIdx 6 n2 4).isEmpty || sjsuHD.uOk 6 n2 4 (uPrmOf (
  sjsuUp 6 4) n2)) 4 = true := by
  decide +kernel

theorem vu_6_4_5 : (fun n2 : Nat => (sjsuHD.uIdx 6 n2 4).isEmpty || sjsuHD.uOk 6 n2 4 (uPrmOf (
  sjsuUp 6 4) n2)) 5 = true := by
  decide +kernel

theorem vu_6_4_6 : (fun n2 : Nat => (sjsuHD.uIdx 6 n2 4).isEmpty || sjsuHD.uOk 6 n2 4 (uPrmOf (
  sjsuUp 6 4) n2)) 6 = true := by
  decide +kernel

theorem vu_6_4_7 : (fun n2 : Nat => (sjsuHD.uIdx 6 n2 4).isEmpty || sjsuHD.uOk 6 n2 4 (uPrmOf (
  sjsuUp 6 4) n2)) 7 = true := by
  decide +kernel

theorem vu_6_4_8 : (fun n2 : Nat => (sjsuHD.uIdx 6 n2 4).isEmpty || sjsuHD.uOk 6 n2 4 (uPrmOf (
  sjsuUp 6 4) n2)) 8 = true := by
  decide +kernel

theorem vu_6_4_9 : (fun n2 : Nat => (sjsuHD.uIdx 6 n2 4).isEmpty || sjsuHD.uOk 6 n2 4 (uPrmOf (
  sjsuUp 6 4) n2)) 9 = true := by
  decide +kernel

theorem vu_6_4_10 : (fun n2 : Nat => (sjsuHD.uIdx 6 n2 4).isEmpty || sjsuHD.uOk 6 n2 4 (uPrmOf (
  sjsuUp 6 4) n2)) 10 = true := by
  decide +kernel

theorem vu_6_4_11 : (fun n2 : Nat => (sjsuHD.uIdx 6 n2 4).isEmpty || sjsuHD.uOk 6 n2 4 (uPrmOf (
  sjsuUp 6 4) n2)) 11 = true := by
  decide +kernel

theorem vu_6_4_12 : (fun n2 : Nat => (sjsuHD.uIdx 6 n2 4).isEmpty || sjsuHD.uOk 6 n2 4 (uPrmOf (
  sjsuUp 6 4) n2)) 12 = true := by
  decide +kernel


end KAM.EffectiveStability.SJSU

end
