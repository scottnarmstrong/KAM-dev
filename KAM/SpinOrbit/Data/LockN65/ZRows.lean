/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.SpinOrbit.Data.LockN65.Format
public import KAM.SpinOrbit.Data.LockN65.ZCode

/-!
# Compact term rows of the lock's generated data (LOCK-DATA, B3 lever (a))

A list of Fourier terms written as the flat integer list `k₀, k₁, re, im, …` (in the compact `zdecs`
form of `ZCode`), read back four entries at a time by `tmsOf` into the rows `tm k₀ k₁ re im`. The data
stay untrusted: a checker checks whatever `tmsOf` denotes.
-/

@[expose] public section

namespace KAM.SpinOrbit.Data.LockN65

open KAM.Certificate

/-- The term rows of a flat list `k₀, k₁, re, im, …` (a trailing incomplete row is dropped). -/
def tmsOf : List ℤ → List (CertKey × CC LockBackend)
  | k₀ :: k₁ :: re :: im :: t => tm k₀ k₁ re im :: tmsOf t
  | _ => []

theorem tmsOf_test :
    (tmsOf (zdecs [(8, 0x0706050403020100)])).map (fun t => (t.1, t.2.re.m, t.2.im.m)) =
      [([0, -1], 1, -2), ([2, -3], 3, -4)] := by
  decide +kernel

end KAM.SpinOrbit.Data.LockN65
