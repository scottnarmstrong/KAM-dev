/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.Spatial.SourceCarrier

/-!
# Provider for `KAM.Planetary.Spatial.spatialSourceAction_mul_eccDeficit_le`

Provider for the frozen theorem `KAM.Planetary.Spatial.spatialSourceAction_mul_eccDeficit_le`,
characterization theorem of `spatialSourceStrongAMD`;
track LP (`LP:MAIN L3 (130–139)`).

The theorem `KAM.Provider.Planetary.Spatial.spatialSourceAction_mul_eccDeficit_le` states the
anchor's exact type text (its draft file under `docs/tracks/LP/freeze/draft7/`). Its proof is the
proof of the former implementation lemma
`KAM.Planetary.Spatial.spatialSourceAction_mul_eccDeficit_le`
(`KAM.Planetary.Spatial.SourceCarrier`), moved verbatim at the freeze (D62). No module other than
the anchor imports this module (AGENTS rule 9).
-/

@[expose] public section

namespace KAM.Provider.Planetary.Spatial

open KAM.Planetary KAM.Planetary.StrongAMD KAM.Planetary.Spatial

theorem spatialSourceAction_mul_eccDeficit_le {n : ℕ} {ν : Fin n → ℝ}
    (z : SpatialSourceCanonicalPhase n ν) :
    ∑ i, spatialSourceKeplerAction z i * (1 - Real.sqrt (1 - spatialSourceKeplerEcc z i ^ 2)) ≤
      spatialSourceStrongAMD z :=
  sum_action_mul_eccDeficit_le_spatialStrongAMD z.2

end KAM.Provider.Planetary.Spatial

end
