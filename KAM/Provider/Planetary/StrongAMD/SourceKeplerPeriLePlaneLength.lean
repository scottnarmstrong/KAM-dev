/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.StrongAMD.SourceCarrier

/-!
# Provider for `KAM.Planetary.StrongAMD.sourceKeplerPeri_le_planeLength`

Provider for the frozen theorem `KAM.Planetary.StrongAMD.sourceKeplerPeri_le_planeLength`, characterization theorem of `sourceKeplerPeri`; track LP (`LP:MAIN
L2 (110–128)`).

The theorem `KAM.Provider.Planetary.StrongAMD.sourceKeplerPeri_le_planeLength` states the anchor's
exact type text (its draft file under `docs/tracks/LP/freeze/draft7/`). Its proof is the proof of
the former implementation lemma `KAM.Planetary.StrongAMD.sourceKeplerPeri_le_planeLength`
(`KAM.Planetary.StrongAMD.SourceCarrier`), moved verbatim at the freeze (D62). No module other than the anchor imports this module (AGENTS rule 9).
-/

@[expose] public section

namespace KAM.Provider.Planetary.StrongAMD

open KAM.Planetary KAM.Planetary.StrongAMD

theorem sourceKeplerPeri_le_planeLength {n : ℕ} {ν : Fin n → ℝ} (z : SourceCanonicalPhase n ν)
    (i : Fin n) : sourceKeplerPeri z i ≤ planeLength (bodyVector z.1.1 i) :=
  (orbital_identities i (z.hz i)).2.2.2.2.2.2.2.1

end KAM.Provider.Planetary.StrongAMD

end
