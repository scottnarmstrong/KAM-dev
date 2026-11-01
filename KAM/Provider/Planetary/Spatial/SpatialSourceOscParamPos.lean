/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.Spatial.SourceCarrier

/-!
# Provider for `KAM.Planetary.Spatial.spatialSourceOscParam_pos`

Provider for the frozen theorem `KAM.Planetary.Spatial.spatialSourceOscParam_pos`, draft-7
revision-1 characterization theorem of `spatialSourceOscParam`; track LP, package LP-FREEZE7R
(`LP:MAIN L16 (508–525)`). The statement surface is proposed in docs/tracks/LP/FREEZE-PROPOSAL.md.

The theorem `KAM.Provider.Planetary.Spatial.spatialSourceOscParam_pos` states the anchor's exact
type text (its draft file under `docs/tracks/LP/freeze/draft7/`). Its proof is the proof of the
former implementation lemma `KAM.Planetary.Spatial.spatialSourceOscParam_pos`
(`KAM.Planetary.Spatial.SourceCarrier`), moved verbatim at the freeze (D62; FREEZE-PROPOSAL §7 point
3). No module other than the anchor imports this module (AGENTS rule 9).
-/

@[expose] public section

namespace KAM.Provider.Planetary.Spatial

open KAM.Planetary KAM.Planetary.StrongAMD KAM.Planetary.Spatial

theorem spatialSourceOscParam_pos {n : ℕ} {ν : Fin n → ℝ} {μ : ℝ}
    (z : SpatialSourceOsculatingPhase n ν μ) (i : Fin n) : 0 < spatialSourceOscParam z i := by
  obtain ⟨hν, hμ, -⟩ := z.2
  unfold spatialSourceOscParam spatialOscParam
  nlinarith [mul_pos hμ (hν i)]

end KAM.Provider.Planetary.Spatial

end
