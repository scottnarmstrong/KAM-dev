/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Frozen.Planetary.Spatial.Defs.SpatialElliptic
public import KAM.Frozen.Planetary.Spatial.Defs.SpatialKeplerPeri

/-!
# Frozen definition `KAM.Planetary.Spatial.spatialSourceKeplerPeri`

Track LP, `LP:MAIN §1 (9) (89–91), L2, d = 3` (MAIN as amended by AMENDMENTS). Owner-approved on
2026-11-01 (decision D62; docs/tracks/LP/FREEZE-PROPOSAL.md draft 7, under the rulings
of D59). This file is frozen: it is hashed in `manifest/frozen-anchors.json`; any change needs an
owner-approved versioned successor.

Freeze role (D59, OD-11 (b)): a source-facing definition on its carrier, frozen as one semantic unit
with its characterization theorems (draft 7, §4).
-/

@[expose] public noncomputable section

namespace KAM.Planetary.Spatial

/-- `a (1 - e)` on the canonical negative-energy carrier. -/
def spatialSourceKeplerPeri {n : ℕ} {ν : Fin n → ℝ} (z : SpatialElliptic ν) (i : Fin n) : ℝ :=
  spatialKeplerPeri ν z.1 i

end KAM.Planetary.Spatial

end
