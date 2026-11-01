/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.Analysis.Real.Sqrt
public import KAM.Frozen.Planetary.Spatial.Defs.SpaceSq

/-!
# Frozen definition `KAM.Planetary.Spatial.spaceLength`

Track LP, `LP:MAIN §1 (5–9), d = 3` (MAIN as amended by AMENDMENTS). Owner-approved on
2026-11-01 (decision D62; docs/tracks/LP/FREEZE-PROPOSAL.md draft 7, under the rulings
of D59). This file is frozen: it is hashed in `manifest/frozen-anchors.json`; any change needs an
owner-approved versioned successor.

Freeze role (D59, OD-11 (b)): a literal formula or predicate of the source, faithful on its whole
carrier.
-/

@[expose] public noncomputable section

namespace KAM.Planetary.Spatial

/-- Euclidean length on `Fin 3 → ℝ`, independent of the ambient Pi sup norm. -/
def spaceLength (v : Fin 3 → ℝ) : ℝ := Real.sqrt (spaceSq v)

end KAM.Planetary.Spatial

end
