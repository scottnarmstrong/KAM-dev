/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.Spatial.SourceCarrier

/-!
# Provider for `KAM.Planetary.Spatial.spatialSourcePlanetAngularMomentum_length_le`

Provider for the frozen theorem
`KAM.Planetary.Spatial.spatialSourcePlanetAngularMomentum_length_le`,
characterization theorem of `spatialSourcePlanetAngularMomentum`; track LP (`LP:MAIN L2 (110–128)`).

The theorem `KAM.Provider.Planetary.Spatial.spatialSourcePlanetAngularMomentum_length_le` states the
anchor's exact type text (its draft file under `docs/tracks/LP/freeze/draft7/`). Its proof is the
proof of the former implementation lemma
`KAM.Planetary.Spatial.spatialSourcePlanetAngularMomentum_length_le`
(`KAM.Planetary.Spatial.SourceCarrier`), moved verbatim at the freeze (D62). No module other than the anchor imports this module (AGENTS rule 9).
-/

@[expose] public section

namespace KAM.Provider.Planetary.Spatial

open KAM.Planetary KAM.Planetary.StrongAMD KAM.Planetary.Spatial

theorem spatialSourcePlanetAngularMomentum_length_le {n : ℕ} {ν : Fin n → ℝ}
    (z : SpatialSourceCanonicalPhase n ν) (i : Fin n) :
    spaceLength (spatialSourcePlanetAngularMomentum z i) ≤ spatialSourceKeplerAction z i :=
  (spatial_orbital_identities i (z.2 i)).2.2.2.2.2.2.1

end KAM.Provider.Planetary.Spatial

end
