/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Data.PNat.Basic

/-!
# Frozen definition `KAM.Wave.sineMode`

Blueprint-W Definition `bpW:w0:basis`; P96-W p. 277.

Owner-approved on 2026-10-30 (decision D41; docs/tracks/W/W-STATEMENTS.md revision 1, commit
ffcbdb93). This file is frozen: it is hashed in `manifest/frozen-anchors.json`; any change needs an
owner-approved versioned successor.
-/

@[expose] public noncomputable section

namespace KAM.Wave

/-- The normalized Dirichlet eigenfunction `φ_j(x) = √(2/π) sin(j x)`, `j ≥ 1`, defined for all
real `x` (P96-W p. 277). -/
def sineMode (j : ℕ+) (x : ℝ) : ℝ :=
  Real.sqrt (2 / Real.pi) * Real.sin ((j : ℝ) * x)

end KAM.Wave

end
