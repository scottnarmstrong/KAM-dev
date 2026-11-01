/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.Spatial.SourceCarrier

/-!
# Provider for `KAM.Planetary.Spatial.spatialSourceStrongAMD_nonneg`

Provider for the frozen theorem `KAM.Planetary.Spatial.spatialSourceStrongAMD_nonneg`, draft-7
revision-1 characterization theorem of `spatialSourceStrongAMD`; track LP, package LP-FREEZE7R
(`LP:MAIN L3 (130–139)`). The statement surface is proposed in docs/tracks/LP/FREEZE-PROPOSAL.md.

The theorem `KAM.Provider.Planetary.Spatial.spatialSourceStrongAMD_nonneg` states the anchor's exact
type text (its draft file under `docs/tracks/LP/freeze/draft7/`). Its proof is the proof of the
former implementation lemma `KAM.Planetary.Spatial.spatialSourceStrongAMD_nonneg`
(`KAM.Planetary.Spatial.SourceCarrier`), moved verbatim at the freeze (D62; FREEZE-PROPOSAL §7 point
3). No module other than the anchor imports this module (AGENTS rule 9).
-/

@[expose] public section

namespace KAM.Provider.Planetary.Spatial

open KAM.Planetary KAM.Planetary.StrongAMD KAM.Planetary.Spatial

theorem spatialSourceStrongAMD_nonneg {n : ℕ} {ν : Fin n → ℝ}
    (z : SpatialSourceCanonicalPhase n ν) : 0 ≤ spatialSourceStrongAMD z :=
  spatialStrongAMD_nonneg z.2

end KAM.Provider.Planetary.Spatial

end
