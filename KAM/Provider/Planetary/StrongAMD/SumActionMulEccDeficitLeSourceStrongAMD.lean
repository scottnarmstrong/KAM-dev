/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.StrongAMD.SourceCarrier

/-!
# Provider for `KAM.Planetary.StrongAMD.sum_action_mul_eccDeficit_le_sourceStrongAMD`

Provider for the frozen theorem
`KAM.Planetary.StrongAMD.sum_action_mul_eccDeficit_le_sourceStrongAMD`,
characterization theorem of `sourceStrongAMD`;
track LP (`LP:MAIN L3
(130–139)`).

The theorem `KAM.Provider.Planetary.StrongAMD.sum_action_mul_eccDeficit_le_sourceStrongAMD` states
the anchor's exact type text (its draft file under `docs/tracks/LP/freeze/draft7/`). Its proof is
the proof of the former implementation lemma
`KAM.Planetary.StrongAMD.sum_action_mul_eccDeficit_le_sourceStrongAMD`
(`KAM.Planetary.StrongAMD.SourceCarrier`), moved verbatim at the freeze (D62). No module other than
the anchor imports this module (AGENTS rule 9).
-/

@[expose] public section

namespace KAM.Provider.Planetary.StrongAMD

open KAM.Planetary KAM.Planetary.StrongAMD

theorem sum_action_mul_eccDeficit_le_sourceStrongAMD {n : ℕ} {ν : Fin n → ℝ}
    (z : SourceCanonicalPhase n ν) :
    ∑ i, keplerAction ν z.1 i * eccDeficit (planeLength (keplerEccVector ν z.1 i)) ≤
      sourceStrongAMD z :=
  sum_action_mul_eccDeficit_le_strongAMD z.hz

end KAM.Provider.Planetary.StrongAMD

end
