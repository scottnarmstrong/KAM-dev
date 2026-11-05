/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.Packed.Bridge

/-!
# Small kernel tests of the packed product (default build, cheap)

Each check is a `decide +kernel` on a few slots: advice-free rounding (`gmpRound`), the load check
(`loadOk`, positive and negative), balanced unpacking, literal joining, and one complete packed
product of 2-D Fourier data with its read-back terms (`gmpRealProduct`), against hand-computed
values. The LG00-sized gate is in `kernel-tests/Packed/` (opt-in).
-/

@[expose] public section

namespace KAM.CertificateSharp.Packed.Tests

open KAM KAM.Certificate KAM.CertificateSharp.Packed

/-- Three slots `[5, -6, 3]` at width 8. -/
def z3 : ℤ := packSum 8 [5, -6, 3]

-- rounding to multiples of `2^2` (to nearest, ties up): `[1, -1, 1]`
example : gmpRound 8 3 4 2 z3 = packSum 8 [1, -1, 1] := by decide +kernel
-- the load check: slots within `[-2^3, 2^3)`, not within `[-2^2, 2^2)`
example : loadOk 8 3 3 z3 = true := by decide +kernel
example : loadOk 8 3 2 z3 = false := by decide +kernel
-- unpacking
example : unpackSlots 8 3 z3 = [5, -6, 3] := by decide +kernel
example : unpackSlots 8 40 (packSum 8 ((List.range 40).map fun i => (i : ℤ) - 20)) =
    (List.range 40).map fun i => (i : ℤ) - 20 := by decide +kernel
-- literal joining
example : natJoin 8 3 2 = 3 + 2 * 256 := by decide +kernel
example : natRamp 8 3 = 1 + 2 * 256 + 3 * 65536 := by decide +kernel
example : (natJoin 288 5 7 ^^^ natRamp 288 2) ^^^ natRamp 288 2 = natJoin 288 5 7 := natUnmask _ _

/-- A 2-D layout: box `[0, 2) × [0, 2)`, strides `[3, 1]`, width 16. -/
def lay : PackLayout := ⟨[0, 0], [2, 2], [3, 1], 16, 1⟩

/-- `3 - 2 χ_(0,1) + 5 χ_(1,1)`. -/
def tx : List (CertKey × ℤ) := [([0, 0], 3), ([0, 1], -2), ([1, 1], 5)]

/-- `1 + 4 χ_(1,0)`. -/
def ty : List (CertKey × ℤ) := [([0, 0], 1), ([1, 0], 4)]

/-- Loads `5` and `4`, offset `2^7 ≥ 5 · 5 · 4`, rounding shift `1`. -/
def gs : GmpSpec := ⟨lay, lay, 5, 4, 7, 1⟩

def wt : CertWeight := ⟨1 / 10, 2⟩

example : gs.guard = true := by decide +kernel
-- the exact product is `3 - 2 χ_(0,1) + 12 χ_(1,0) - 3 χ_(1,1) + 20 χ_(2,1)`; halved to nearest:
example : (gmpRealProduct gs wt 4 tx ty).map Prod.fst =
    some [([0, 0], 2), ([0, 1], -1), ([1, 0], 6), ([1, 1], -1), ([2, 1], 10)] := by decide +kernel
-- an out-of-box key fails closed
example : gmpRealProduct gs wt 4 [([2, 0], 1)] ty = none := by decide +kernel

end KAM.CertificateSharp.Packed.Tests
