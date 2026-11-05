/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.Spatial.SourceCarrier

/-!
# Provider for `KAM.Planetary.Spatial.spatialSourceOscPeri_le_length`

Provider for the frozen theorem `KAM.Planetary.Spatial.spatialSourceOscPeri_le_length`,
characterization theorem of `spatialSourceOscPeri`;
track LP (`LP:MAIN L16 (527–528)`).

The theorem `KAM.Provider.Planetary.Spatial.spatialSourceOscPeri_le_length` states the anchor's
exact type text (its draft file under `docs/tracks/LP/freeze/draft7/`). Its proof is the proof of
the former implementation lemma `KAM.Planetary.Spatial.spatialSourceOscPeri_le_length`
(`KAM.Planetary.Spatial.SourceCarrier`), moved verbatim at the freeze (D62). No module other than
the anchor imports this module (AGENTS rule 9).
-/

@[expose] public section

namespace KAM.Provider.Planetary.Spatial

open KAM.Planetary KAM.Planetary.StrongAMD KAM.Planetary.Spatial

theorem spatialSourceOscPeri_le_length {n : ℕ} {ν : Fin n → ℝ} {μ : ℝ}
    (z : SpatialSourceOsculatingPhase n ν μ) (i : Fin n) :
    spatialSourceOscPeri z i ≤ spaceLength (bodyVector3 z.1.1 i) :=
  (spatialOscPhase_ellipse z i).2.2.1

end KAM.Provider.Planetary.Spatial

end
