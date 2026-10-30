/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.Analysis.Normed.Lp.lpSpace
public import KAM.Frozen.Wave.Defs.EllWeight

/-!
# Frozen definition `KAM.Wave.coeff`

Blueprint-W Definition `bpW:w0:ellap`, Convention `bpW:w0:weights`. Reads the `ℓ^{1,1}` coefficient
sequence off a weighted coordinate (see `KAM.Wave.WaveSpace`).

Owner-approved on 2026-10-30 (decision D41; docs/tracks/W/W-STATEMENTS.md revision 1, commit
ffcbdb93). This file is frozen: it is hashed in `manifest/frozen-anchors.json`; any change needs an
owner-approved versioned successor.
-/

@[expose] public noncomputable section

namespace KAM.Wave

/-- The `ℓ^{1,1}` coefficient sequence `q_j = y_j / (j e^j)` represented by `y ∈ ℓ²(ℕ+)`. -/
def coeff (y : lp (fun _ : ℕ+ => ℝ) 2) (j : ℕ+) : ℝ :=
  y j / ellWeight 1 1 j

end KAM.Wave

end
