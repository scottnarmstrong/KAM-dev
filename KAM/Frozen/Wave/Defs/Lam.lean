/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Data.PNat.Basic

/-!
# Frozen definition `KAM.Wave.lam`

Blueprint-W Definition `bpW:w0:basis`; P96-W p. 277.

Owner-approved on 2026-10-30 (decision D41; docs/tracks/W/W-STATEMENTS.md revision 1, commit
ffcbdb93). This file is frozen: it is hashed in `manifest/frozen-anchors.json`; any change needs an
owner-approved versioned successor.
-/

@[expose] public noncomputable section

namespace KAM.Wave

/-- The linear frequency `λ_j = √(j² + m)` of the Dirichlet mode `j ≥ 1` of
`u_tt = u_xx - m u` on `[0, π]` (P96-W p. 277). The standing convention `0 < m` is part of the
carrier (W-ST2). -/
def lam (m : ℝ) (_hm : 0 < m) (j : ℕ+) : ℝ :=
  Real.sqrt ((j : ℝ) ^ 2 + m)

end KAM.Wave

end
