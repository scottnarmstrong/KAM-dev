/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.SpinOrbit.Data.LockN65.ZCode

/-!
# Compact `(slot, value)` lists (LOCK-DATA)

`pairsOf` reads a flat integer list `s₀, v₀, s₁, v₁, …` (a `zdecs` literal) as the pairs
`(s₀.toNat, v₀), …`: the operand slot terms of a packed product, stated once as a literal so the
shard checks do not recompute them. Nothing is assumed about the data.
-/

@[expose] public section

namespace KAM.SpinOrbit.Data.LockN65

/-- The `(slot, value)` pairs of a flat list `s, v, …` (a trailing incomplete pair is dropped). -/
def pairsOf : List ℤ → List (ℕ × ℤ)
  | s :: v :: t => (s.toNat, v) :: pairsOf t
  | _ => []

theorem pairsOf_test : pairsOf (zdecs [(4, 0x07040300)]) = [(0, -2), (2, -4)] := by
  decide +kernel

end KAM.SpinOrbit.Data.LockN65
