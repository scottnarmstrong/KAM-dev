/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.Spatial.SourceCarrier

/-!
# Provider for `KAM.Planetary.Spatial.spatialSourceKeplerPeri_le_length`

Provider for the frozen theorem `KAM.Planetary.Spatial.spatialSourceKeplerPeri_le_length`, draft-7
revision-1 characterization theorem of `spatialSourceKeplerPeri`; track LP, package LP-FREEZE7R
(`LP:MAIN L2 (110–128)`). The statement surface is proposed in docs/tracks/LP/FREEZE-PROPOSAL.md.

The theorem `KAM.Provider.Planetary.Spatial.spatialSourceKeplerPeri_le_length` states the anchor's
exact type text (its draft file under `docs/tracks/LP/freeze/draft7/`). Its proof is the proof of
the former implementation lemma `KAM.Planetary.Spatial.spatialSourceKeplerPeri_le_length`
(`KAM.Planetary.Spatial.SourceCarrier`), moved verbatim at the freeze (D62; FREEZE-PROPOSAL §7 point
3). No module other than the anchor imports this module (AGENTS rule 9).
-/

@[expose] public section

namespace KAM.Provider.Planetary.Spatial

open KAM.Planetary KAM.Planetary.StrongAMD KAM.Planetary.Spatial

theorem spatialSourceKeplerPeri_le_length {n : ℕ} {ν : Fin n → ℝ}
    (z : SpatialSourceCanonicalPhase n ν)
    (i : Fin n) : spatialSourceKeplerPeri z i ≤ spaceLength (bodyVector3 z.1.1 i) :=
  (spatial_orbital_identities i (z.2 i)).2.2.2.2.2.2.2.1

end KAM.Provider.Planetary.Spatial

end
