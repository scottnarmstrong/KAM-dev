/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.StrongAMD.SourceCarrier

/-!
# Provider for `KAM.Planetary.StrongAMD.sourceOscPeri_le_planeLength`

Provider for the frozen theorem `KAM.Planetary.StrongAMD.sourceOscPeri_le_planeLength`, draft-7
revision-1 characterization theorem of `sourceOscPeri`; track LP, package LP-FREEZE7R (`LP:MAIN L16
(527–528)`). The statement surface is proposed in docs/tracks/LP/FREEZE-PROPOSAL.md.

The theorem `KAM.Provider.Planetary.StrongAMD.sourceOscPeri_le_planeLength` states the anchor's
exact type text (its draft file under `docs/tracks/LP/freeze/draft7/`). Its proof is the proof of
the former implementation lemma `KAM.Planetary.StrongAMD.sourceOscPeri_le_planeLength`
(`KAM.Planetary.StrongAMD.SourceCarrier`), moved verbatim at the freeze (D62; FREEZE-PROPOSAL §7
point 3). No module other than the anchor imports this module (AGENTS rule 9).
-/

@[expose] public section

namespace KAM.Provider.Planetary.StrongAMD

open KAM.Planetary KAM.Planetary.StrongAMD

theorem sourceOscPeri_le_planeLength {n : ℕ} {ν : Fin n → ℝ} {μ : ℝ}
    (z : SourceOsculatingPhase n ν μ)
    (i : Fin n) : sourceOscPeri z i ≤ planeLength (bodyVector z.1.1 i) :=
  (osc_tangency ν z.2.2.1.le (z.2.1 i) (z.2.2.2 i).1 (z.2.2.2 i).2.1).2.1

end KAM.Provider.Planetary.StrongAMD

end
