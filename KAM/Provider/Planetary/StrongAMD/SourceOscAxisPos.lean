/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.StrongAMD.SourceCarrier

/-!
# Provider for `KAM.Planetary.StrongAMD.sourceOscAxis_pos`

Provider for the frozen theorem `KAM.Planetary.StrongAMD.sourceOscAxis_pos`,
characterization theorem of `sourceOscAxis`; track LP (`LP:MAIN L16
(527–528)`).

The theorem `KAM.Provider.Planetary.StrongAMD.sourceOscAxis_pos` states the anchor's exact type text
(its draft file under `docs/tracks/LP/freeze/draft7/`). Its proof is the proof of the former
implementation lemma `KAM.Planetary.StrongAMD.sourceOscAxis_pos`
(`KAM.Planetary.StrongAMD.SourceCarrier`), moved verbatim at the freeze (D62). No module other than the anchor imports this module (AGENTS rule 9).
-/

@[expose] public section

namespace KAM.Provider.Planetary.StrongAMD

open KAM.Planetary KAM.Planetary.StrongAMD

theorem sourceOscAxis_pos {n : ℕ} {ν : Fin n → ℝ} {μ : ℝ} (z : SourceOsculatingPhase n ν μ)
    (i : Fin n) : 0 < sourceOscAxis z i :=
  (osc_tangency ν z.2.2.1.le (z.2.1 i) (z.2.2.2 i).1 (z.2.2.2 i).2.1).1

end KAM.Provider.Planetary.StrongAMD

end
