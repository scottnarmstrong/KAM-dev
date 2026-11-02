/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.StrongAMD.Threshold.Pair

/-!
# Provider for `KAM.Planetary.StrongAMD.orderedPairThreshold_isLeast`

Provider for the frozen theorem `KAM.Planetary.StrongAMD.orderedPairThreshold_isLeast`,
characterization theorem of `orderedPairThreshold`, `pairThreshold`;
track LP (`LP:MAIN §1 (3) (47–55), L4 (141–160)`).

The theorem `KAM.Provider.Planetary.StrongAMD.orderedPairThreshold_isLeast` states the anchor's
exact type text (its draft file under `docs/tracks/LP/freeze/draft7/`). Its proof is the proof of
the former implementation lemma `KAM.Planetary.StrongAMD.orderedPairThreshold_isLeast`
(`KAM.Planetary.StrongAMD.Threshold.Pair`), moved verbatim at the freeze (D62). No module other
than the anchor imports this module (AGENTS rule 9).
-/

@[expose] public section

namespace KAM.Provider.Planetary.StrongAMD

open KAM.Planetary KAM.Planetary.StrongAMD

theorem orderedPairThreshold_isLeast {n : ℕ} {ν : Fin n → ℝ} (I : OrderedActions ν) (i j : Fin n)
    (hij : i < j) :
    IsLeast (pairObjective I.1 i j '' pairFeasible ν I.1 i j) (orderedPairThreshold I i j hij) :=
  pairThreshold_isLeast ν I.1 i j

end KAM.Provider.Planetary.StrongAMD

end
