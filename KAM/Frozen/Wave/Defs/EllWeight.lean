/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.PNat.Basic

/-!
# Frozen definition `KAM.Wave.ellWeight`

Blueprint-W Definition `bpW:w0:ellap`; P96-W p. 277 (the source's `s` is our `p`).

Owner-approved on 2026-10-30 (decision D41; docs/tracks/W/W-STATEMENTS.md revision 1, commit
ffcbdb93). This file is frozen: it is hashed in `manifest/frozen-anchors.json`; any change needs an
owner-approved versioned successor.
-/

@[expose] public noncomputable section

namespace KAM.Wave

/-- The weight `j ^ p * e ^ (a j)` of `ℓ^{a,p}`: `‖w‖_{a,p}² = Σ_{j ≥ 1} (ellWeight a p j * |w_j|)²`
(P96-W p. 277). It is strictly positive. -/
def ellWeight (a p : ℝ) (j : ℕ+) : ℝ :=
  (j : ℝ) ^ p * Real.exp (a * j)

end KAM.Wave

end
