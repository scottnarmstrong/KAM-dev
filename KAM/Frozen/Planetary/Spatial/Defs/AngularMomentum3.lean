/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Frozen.Planetary.Defs.Phase
public import KAM.Frozen.Planetary.Spatial.Defs.BodyVector3
public import KAM.Frozen.Planetary.Spatial.Defs.SpaceCross

/-!
# Frozen definition `KAM.Planetary.Spatial.angularMomentum3`

Track LP, `LP:MAIN §1 (2) (31–33), d = 3` (MAIN as amended by AMENDMENTS). Owner-approved on
2026-11-01 (decision D62; docs/tracks/LP/FREEZE-PROPOSAL.md draft 7, under the rulings
of D59). This file is frozen: it is hashed in `manifest/frozen-anchors.json`; any change needs an
owner-approved versioned successor.

Freeze role (D59, OD-11 (b)): a literal formula or predicate of the source, faithful on its whole
carrier.
-/

@[expose] public noncomputable section

namespace KAM.Planetary.Spatial

/-- Total angular momentum `L = Σ_i q_i × p_i`. -/
def angularMomentum3 {n : ℕ} (z : Phase (n * 3)) : Fin 3 → ℝ :=
  ∑ i, spaceCross (bodyVector3 z.1 i) (bodyVector3 z.2 i)

end KAM.Planetary.Spatial

end
