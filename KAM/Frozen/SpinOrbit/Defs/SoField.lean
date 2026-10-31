/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import KAM.Frozen.SpinOrbit.Defs.SoV

/-!
# Frozen definition `KAM.SpinOrbit.soField`

Owner-approved on 2026-10-31 (decision D40, docs/tracks/SO/FREEZE-PROPOSAL-2.md; literals D46 and
D48). This file is frozen: it is hashed in `manifest/frozen-anchors.json`; any change needs an
owner-approved versioned successor.
-/

@[expose] public noncomputable section

namespace KAM.SpinOrbit

/-- The physical spin–orbit vector field on `(q, p, φ)`: `q̇ = p`, `ṗ = -∂_q V`, `φ̇ = 1`.
Time is measured in orbital periods and `p` is the spin rate divided by the orbital mean motion. -/
def soField (x : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (x.2.1, -deriv (fun s => soV s x.2.2) x.1, 1)

end KAM.SpinOrbit

end
