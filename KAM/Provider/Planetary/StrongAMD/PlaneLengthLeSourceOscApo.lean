/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.StrongAMD.SourceCarrier

/-!
# Provider for `KAM.Planetary.StrongAMD.planeLength_le_sourceOscApo`

Provider for the frozen theorem `KAM.Planetary.StrongAMD.planeLength_le_sourceOscApo`,
characterization theorem of `sourceOscApo`;
track LP (`LP:MAIN L16 (527–528)`).

The theorem `KAM.Provider.Planetary.StrongAMD.planeLength_le_sourceOscApo` states the anchor's exact
type text (its draft file under `docs/tracks/LP/freeze/draft7/`). Its proof is the proof of the
former implementation lemma `KAM.Planetary.StrongAMD.planeLength_le_sourceOscApo`
(`KAM.Planetary.StrongAMD.SourceCarrier`), moved verbatim at the freeze (D62). No module other than
the anchor imports this module (AGENTS rule 9).
-/

@[expose] public section

namespace KAM.Provider.Planetary.StrongAMD

open KAM.Planetary KAM.Planetary.StrongAMD

theorem planeLength_le_sourceOscApo {n : ℕ} {ν : Fin n → ℝ} {μ : ℝ}
    (z : SourceOsculatingPhase n ν μ)
    (i : Fin n) : planeLength (bodyVector z.1.1 i) ≤ sourceOscApo z i :=
  (osc_tangency ν z.2.2.1.le (z.2.1 i) (z.2.2.2 i).1 (z.2.2.2 i).2.1).2.2

end KAM.Provider.Planetary.StrongAMD

end
