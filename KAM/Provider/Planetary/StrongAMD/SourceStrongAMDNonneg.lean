/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.StrongAMD.SourceCarrier

/-!
# Provider for `KAM.Planetary.StrongAMD.sourceStrongAMD_nonneg`

Provider for the frozen theorem `KAM.Planetary.StrongAMD.sourceStrongAMD_nonneg`, draft-7 revision-1
characterization theorem of `sourceStrongAMD`; track LP, package LP-FREEZE7R (`LP:MAIN L3
(130–139)`). The statement surface is proposed in docs/tracks/LP/FREEZE-PROPOSAL.md.

The theorem `KAM.Provider.Planetary.StrongAMD.sourceStrongAMD_nonneg` states the anchor's exact type
text (its draft file under `docs/tracks/LP/freeze/draft7/`). Its proof is the proof of the former
implementation lemma `KAM.Planetary.StrongAMD.sourceStrongAMD_nonneg`
(`KAM.Planetary.StrongAMD.SourceCarrier`), moved verbatim at the freeze (D62; FREEZE-PROPOSAL §7
point 3). No module other than the anchor imports this module (AGENTS rule 9).
-/

@[expose] public section

namespace KAM.Provider.Planetary.StrongAMD

open KAM.Planetary KAM.Planetary.StrongAMD

theorem sourceStrongAMD_nonneg {n : ℕ} {ν : Fin n → ℝ} (z : SourceCanonicalPhase n ν) :
    0 ≤ sourceStrongAMD z := strongAMD_nonneg z.hz

end KAM.Provider.Planetary.StrongAMD

end
