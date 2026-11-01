/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Frozen.Planetary.Defs.Phase
public import KAM.Frozen.Planetary.Spatial.Defs.SpatialKeplerEnergy

/-!
# Frozen definition `KAM.Planetary.Spatial.spatialKeplerAxis`

Track LP, `LP:MAIN §1 (2) (31–37), d = 3` (MAIN as amended by AMENDMENTS). Owner-approved on
2026-11-01 (decision D62; docs/tracks/LP/FREEZE-PROPOSAL.md draft 7, under the rulings
of D59). This file is frozen: it is hashed in `manifest/frozen-anchors.json`; any change needs an
owner-approved versioned successor.

Freeze role (D59, OD-11 (b)): an internal total helper in the definition closure. It is certified as
the source object only on its carrier, through the source-facing definitions and predicates that use
it; its values off that carrier carry no source meaning.
-/

@[expose] public noncomputable section

namespace KAM.Planetary.Spatial

/-- Canonical semi-major axis `a_i = −ν_i/(2 ν_i E_i) = −1/(2 E_i)`. -/
def spatialKeplerAxis {n : ℕ} (ν : Fin n → ℝ) (z : Phase (n * 3)) (i : Fin n) : ℝ :=
  -ν i / (2 * spatialKeplerEnergy ν z i)

end KAM.Planetary.Spatial

end
