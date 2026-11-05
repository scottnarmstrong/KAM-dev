/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.Spatial.SourceCarrier

/-!
# Provider for `KAM.Planetary.Spatial.spatialSourceKeplerAxis_pos`

Provider for the frozen theorem `KAM.Planetary.Spatial.spatialSourceKeplerAxis_pos`,
characterization theorem of `spatialSourceKeplerAxis`;
track LP (`LP:MAIN L2 (110–128)`).

The theorem `KAM.Provider.Planetary.Spatial.spatialSourceKeplerAxis_pos` states the anchor's exact
type text (its draft file under `docs/tracks/LP/freeze/draft7/`). Its proof is the proof of the
former implementation lemma `KAM.Planetary.Spatial.spatialSourceKeplerAxis_pos`
(`KAM.Planetary.Spatial.SourceCarrier`), moved verbatim at the freeze (D62). No module other than
the anchor imports this module (AGENTS rule 9).
-/

@[expose] public section

namespace KAM.Provider.Planetary.Spatial

open KAM.Planetary KAM.Planetary.StrongAMD KAM.Planetary.Spatial

theorem spatialSourceKeplerAxis_pos {n : ℕ} {ν : Fin n → ℝ} (z : SpatialSourceCanonicalPhase n ν)
    (i : Fin n) : 0 < spatialSourceKeplerAxis z i :=
  (spatial_orbital_identities i (z.2 i)).1

end KAM.Provider.Planetary.Spatial

end
