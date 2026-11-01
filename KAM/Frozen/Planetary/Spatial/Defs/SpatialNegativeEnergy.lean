/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Frozen.Planetary.Defs.Phase
public import KAM.Frozen.Planetary.Spatial.Defs.BodyVector3
public import KAM.Frozen.Planetary.Spatial.Defs.SpaceLength
public import KAM.Frozen.Planetary.Spatial.Defs.SpatialKeplerEnergy

/-!
# Frozen definition `KAM.Planetary.Spatial.SpatialNegativeEnergy`

Track LP, `LP:MAIN §1 (2) (31–37), d = 3` (MAIN as amended by AMENDMENTS). Owner-approved on
2026-11-01 (decision D62; docs/tracks/LP/FREEZE-PROPOSAL.md draft 7, under the rulings
of D59). This file is frozen: it is hashed in `manifest/frozen-anchors.json`; any change needs an
owner-approved versioned successor.

Freeze role (D59, OD-11 (b)): a source carrier (subtype or carrier predicate).
-/

@[expose] public noncomputable section

namespace KAM.Planetary.Spatial

/-- The source carrier of the Kepler elements: positive masses, no planet at the star, negative
energy of every planet. -/
def SpatialNegativeEnergy {n : ℕ} (ν : Fin n → ℝ) (z : Phase (n * 3)) : Prop :=
  ∀ i, 0 < ν i ∧ 0 < spaceLength (bodyVector3 z.1 i) ∧ spatialKeplerEnergy ν z i < 0

end KAM.Planetary.Spatial

end
