/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Frozen.Planetary.Defs.Phase
public import KAM.Frozen.Planetary.Spatial.Defs.BodyVector3
public import KAM.Frozen.Planetary.Spatial.Defs.SpaceLength
public import KAM.Frozen.Planetary.Spatial.Defs.SpatialOscEcc
public import KAM.Frozen.Planetary.Spatial.Defs.SpatialOscEnergy

/-!
# Frozen definition `KAM.Planetary.Spatial.SpatialOscPhase`

Track LP, `LP:MAIN L16 (508–525), d = 3` (MAIN as amended by AMENDMENTS). Owner-approved on
2026-11-01 (decision D62; docs/tracks/LP/FREEZE-PROPOSAL.md draft 7, under the rulings
of D59). This file is frozen: it is hashed in `manifest/frozen-anchors.json`; any change needs an
owner-approved versioned successor.

Freeze role (D59, OD-11 (b)): a source carrier (subtype or carrier predicate).
-/

@[expose] public noncomputable section

namespace KAM.Planetary.Spatial

/-- Valid actual-velocity osculating states (`LP:MAIN L16`, nondegenerate ellipses): positive
masses,
`μ > 0`, and for every planet `|q_i| > 0`, `E_i^osc < 0`, `e_i^osc < 1`. -/
abbrev SpatialOscPhase (n : ℕ) (ν : Fin n → ℝ) (μ : ℝ) :=
  {z : Phase (n * 3) // (∀ i, 0 < ν i) ∧ 0 < μ ∧
    ∀ i, 0 < spaceLength (bodyVector3 z.1 i) ∧ spatialOscEnergy ν μ z i < 0 ∧
      spatialOscEcc ν μ z i < 1}

end KAM.Planetary.Spatial

end
