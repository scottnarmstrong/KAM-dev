/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import KAM.Frozen.Planetary.Spatial.Defs.BodyVector3
public import KAM.Frozen.Planetary.Spatial.Defs.SpaceLength
public import KAM.Frozen.Planetary.Spatial.Defs.SpatialSourceCanonicalPhase
public import KAM.Frozen.Planetary.Spatial.Defs.SpatialSourceKeplerApo
import KAM.Provider.Planetary.Spatial.SpatialSourceKeplerApoGeLength

/-!
# Frozen theorem `KAM.Planetary.Spatial.spatialSourceKeplerApo_ge_length`

Track LP characterization theorem of `spatialSourceKeplerApo` (`LP:MAIN L2 (110–128)`), frozen with
its definition as one semantic unit (D59, OD-11 (b)). Owner-approved on 2026-11-01 (decision
D62; docs/tracks/LP/FREEZE-PROPOSAL.md draft 7, under the rulings of D59). This file is
frozen: it is hashed in `manifest/frozen-anchors.json`; any change needs an owner-approved versioned
successor. Only the proof body between the markers may change, and only to `by exact
KAM.Provider.Planetary.Spatial.spatialSourceKeplerApo_ge_length z i` when the provider
`KAM.Provider.Planetary.Spatial.SpatialSourceKeplerApoGeLength` is complete (sealing).
-/

@[expose] public section

namespace KAM.Planetary.Spatial

/-- Radial incidence on the canonical carrier: `|q_i| ≤ a_i (1 + e_i)` (`LP:MAIN L2 (110–128)`). -/
theorem spatialSourceKeplerApo_ge_length {n : ℕ} {ν : Fin n → ℝ}
    (z : SpatialSourceCanonicalPhase n ν)
    (i : Fin n) : spaceLength (bodyVector3 z.1.1 i) ≤ spatialSourceKeplerApo z i :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact KAM.Provider.Planetary.Spatial.spatialSourceKeplerApo_ge_length z i
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end KAM.Planetary.Spatial

end
-- FROZEN_ANCHOR_SUFFIX_END
