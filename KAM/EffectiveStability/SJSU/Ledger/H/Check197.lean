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

theorem vu_0_0_6 : (fun n2 : Nat => (sjsuHD.uIdx 0 n2 0).isEmpty || sjsuHD.uOk 0 n2 0 (uPrmOf (
  sjsuUp 0 0) n2)) 6 = true := by
  decide +kernel

theorem vu_0_0_7 : (fun n2 : Nat => (sjsuHD.uIdx 0 n2 0).isEmpty || sjsuHD.uOk 0 n2 0 (uPrmOf (
  sjsuUp 0 0) n2)) 7 = true := by
  decide +kernel

theorem vu_0_0_8 : (fun n2 : Nat => (sjsuHD.uIdx 0 n2 0).isEmpty || sjsuHD.uOk 0 n2 0 (uPrmOf (
  sjsuUp 0 0) n2)) 8 = true := by
  decide +kernel

theorem vu_0_0_9 : (fun n2 : Nat => (sjsuHD.uIdx 0 n2 0).isEmpty || sjsuHD.uOk 0 n2 0 (uPrmOf (
  sjsuUp 0 0) n2)) 9 = true := by
  decide +kernel

theorem vu_0_0_10 : (fun n2 : Nat => (sjsuHD.uIdx 0 n2 0).isEmpty || sjsuHD.uOk 0 n2 0 (uPrmOf (
  sjsuUp 0 0) n2)) 10 = true := by
  decide +kernel

theorem vu_0_0_11 : (fun n2 : Nat => (sjsuHD.uIdx 0 n2 0).isEmpty || sjsuHD.uOk 0 n2 0 (uPrmOf (
  sjsuUp 0 0) n2)) 11 = true := by
  decide +kernel

theorem vu_0_0_12 : (fun n2 : Nat => (sjsuHD.uIdx 0 n2 0).isEmpty || sjsuHD.uOk 0 n2 0 (uPrmOf (
  sjsuUp 0 0) n2)) 12 = true := by
  decide +kernel

theorem vu_0_0_13 : (fun n2 : Nat => (sjsuHD.uIdx 0 n2 0).isEmpty || sjsuHD.uOk 0 n2 0 (uPrmOf (
  sjsuUp 0 0) n2)) 13 = true := by
  decide +kernel


end KAM.EffectiveStability.SJSU

end
