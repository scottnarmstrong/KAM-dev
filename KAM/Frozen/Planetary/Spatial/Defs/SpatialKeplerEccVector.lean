/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Frozen.Planetary.Defs.Phase
public import KAM.Frozen.Planetary.Spatial.Defs.BodyVector3
public import KAM.Frozen.Planetary.Spatial.Defs.SpaceDot
public import KAM.Frozen.Planetary.Spatial.Defs.SpaceLength
public import KAM.Frozen.Planetary.Spatial.Defs.SpaceSq

/-!
# Frozen definition `KAM.Planetary.Spatial.spatialKeplerEccVector`

Track LP, `LP:MAIN §1 (26–29), d = 3` (MAIN as amended by AMENDMENTS). Owner-approved on
2026-11-01 (decision D62; docs/tracks/LP/FREEZE-PROPOSAL.md draft 7, under the rulings
of D59). This file is frozen: it is hashed in `manifest/frozen-anchors.json`; any change needs an
owner-approved versioned successor.

Freeze role (D59, OD-11 (b)): an internal total helper in the definition closure. It is certified as
the source object only on its carrier, through the source-facing definitions and predicates that use
it; its values off that carrier carry no source meaning.
-/

@[expose] public noncomputable section

namespace KAM.Planetary.Spatial

/-- Eccentricity vector `𝐞_i = (|v|² − 1/|q|) q − (q·v) v` with `v = p/ν`. -/
def spatialKeplerEccVector {n : ℕ} (ν : Fin n → ℝ) (z : Phase (n * 3)) (i : Fin n) : Fin 3 → ℝ :=
  let q := bodyVector3 z.1 i
  let p := bodyVector3 z.2 i
  (spaceSq p / ν i ^ 2 - 1 / spaceLength q) • q - (spaceDot q p / ν i ^ 2) • p

end KAM.Planetary.Spatial

end
