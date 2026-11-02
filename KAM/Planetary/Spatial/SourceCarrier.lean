/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Spatial.Orbital
public import KAM.Planetary.Spatial.Momentum
public import KAM.Planetary.Spatial.Osculating.Basic
public import KAM.Frozen.Planetary.Spatial.Defs.SpatialSourceAngularMomentum
public import KAM.Frozen.Planetary.Spatial.Defs.SpatialSourceCanonicalPhase
public import KAM.Frozen.Planetary.Spatial.Defs.SpatialSourceKeplerAction
public import KAM.Frozen.Planetary.Spatial.Defs.SpatialSourceKeplerAxis
public import KAM.Frozen.Planetary.Spatial.Defs.SpatialSourceKeplerEcc
public import KAM.Frozen.Planetary.Spatial.Defs.SpatialSourceKeplerEccVector
public import KAM.Frozen.Planetary.Spatial.Defs.SpatialSourceOsculatingPhase
public import KAM.Frozen.Planetary.Spatial.Defs.SpatialSourcePlanetAngularMomentum
public import KAM.Frozen.Planetary.Spatial.Defs.SpatialSourceStrongAMD

/-!
# Spatial source carriers and source-facing physical quantities (OD-11 (b))

Source: `LP:MAIN §1 (2) (26–45)`, `L2 (110–128)`, `L3 (130–139)`, `L16 (508–529)` with
`d = 3`; track LP, non-frozen.

Remark: the unrestricted total helpers `spatialKeplerAxis`,
`spatialKeplerAction`, … stay internal and are not frozen as physical quantities.  Every physical
quantity is exposed through a source subtype.

* `SpatialSourceCanonicalPhase n ν` is the canonical carrier: it is `SpatialElliptic ν`, i.e. the
  subtype of `SpatialNegativeEnergy ν` (positive masses, `0 < |q_i|`, negative energy of every
  planet).
* `SpatialSourceOsculatingPhase n ν μ` is SP-OSC's `SpatialOscPhase n ν μ` (positive masses,
  `0 < μ`, `0 < |q_i|`, `E_i^osc < 0`, `e_i^osc < 1`).  Its source quantities are SP-OSC's
  `spatialSourceOsc*` (reused, not duplicated), as are `spatialSourceKeplerPeri/Apo` on the
  canonical carrier.
* The canonical source definitions `spatialSourceKeplerAxis`, `…Action`, `…EccVector`, `…Ecc`,
  `…PlanetAngularMomentum`, `…AngularMomentum`, `spatialSourceStrongAMD` each carry a `_def`
  equation proved by `rfl`.
* The characterizations (the semantic unit) are the facts of `spatial_orbital_identities` and
  Lemma 3, restated on the carrier.
-/

@[expose] public noncomputable section

namespace KAM.Planetary.Spatial

open KAM.Planetary

variable {n : ℕ}

/-! ### Carriers -/

/-! ### Canonical source definitions -/

/-! ### Defining equations (`rfl`) -/

/-! ### Characterizations of the canonical source quantities (`LP:MAIN L2`, `L3`) -/

/-! ### Characterizations of the osculating source quantities (`LP:MAIN L16`) -/

end KAM.Planetary.Spatial

end
