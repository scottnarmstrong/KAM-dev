/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Spatial.Vector
public import KAM.Frozen.Planetary.Spatial.Defs.AngularMomentum3
public import KAM.Frozen.Planetary.Spatial.Defs.PlanetAngularMomentum3
public import KAM.Frozen.Planetary.Spatial.Defs.SpatialElliptic
public import KAM.Frozen.Planetary.Spatial.Defs.SpatialKeplerAction
public import KAM.Frozen.Planetary.Spatial.Defs.SpatialKeplerAxis
public import KAM.Frozen.Planetary.Spatial.Defs.SpatialKeplerEccVector
public import KAM.Frozen.Planetary.Spatial.Defs.SpatialKeplerEnergy
public import KAM.Frozen.Planetary.Spatial.Defs.SpatialNegativeEnergy

/-!
# Kepler elements, angular momentum and strong AMD in dimension three

Package LP-SP-MODEL, `LP:MAIN §1 (2) (26–45)` with `d = 3`; track LP, non-frozen; the statement
surface is proposed in docs/tracks/LP/FREEZE-PROPOSAL.md.

The total (uncarried) definitions follow the planar frozen convention (mass argument `ν`, total
Kepler energy `ν_i E_i`); they carry meaning only on the negative-energy carrier
`SpatialNegativeEnergy ν z`.  Per OD-11 (b) the carrier is explicit: `SpatialNegativeEnergy`, the
subtype `SpatialElliptic ν`, and `spatialStrongAMDOn` on it with its characterization.
-/

@[expose] public noncomputable section

namespace KAM.Planetary.Spatial

open KAM.Planetary

variable {n : ℕ}

/-- The strong AMD `C = Σ_i Λ_i − |L|` (`LP:MAIN §1 (2)`), `|L|` the Euclidean length. -/
def spatialStrongAMD (ν : Fin n → ℝ) (z : Phase (n * 3)) : ℝ :=
  (∑ i, spatialKeplerAction ν z i) - spaceLength (angularMomentum3 z)

/-- The strong AMD on its carrier. -/
def spatialStrongAMDOn (ν : Fin n → ℝ) (z : SpatialElliptic ν) : ℝ := spatialStrongAMD ν z.1

/-- Characterization: on the carrier, the strong AMD is the total one. -/
theorem spatialStrongAMDOn_eq (ν : Fin n → ℝ) (z : SpatialElliptic ν) :
    spatialStrongAMDOn ν z = spatialStrongAMD ν z.1 := rfl

theorem angularMomentum3_eq_sum (z : Phase (n * 3)) :
    angularMomentum3 z = ∑ i, planetAngularMomentum3 z i := rfl

end KAM.Planetary.Spatial

end
