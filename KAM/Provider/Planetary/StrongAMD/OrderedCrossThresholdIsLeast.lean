/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.StrongAMD.Threshold.Strong

/-!
# Provider for `KAM.Planetary.StrongAMD.orderedCrossThreshold_isLeast`

Provider for the frozen theorem `KAM.Planetary.StrongAMD.orderedCrossThreshold_isLeast`, draft-7
revision-1 characterization theorem of `orderedCrossThreshold`; track LP, package LP-FREEZE7R
(`LP:MAIN §1 (3) (47–55)`). The statement surface is proposed in docs/tracks/LP/FREEZE-PROPOSAL.md.

The theorem `KAM.Provider.Planetary.StrongAMD.orderedCrossThreshold_isLeast` states the anchor's
exact type text (its draft file under `docs/tracks/LP/freeze/draft7/`). Its proof is the proof of
the former implementation lemma `KAM.Planetary.StrongAMD.orderedCrossThreshold_isLeast`
(`KAM.Planetary.StrongAMD.PlanarSafety.SourceThreshold`), moved verbatim at the freeze (D62;
FREEZE-PROPOSAL §7 point 3). No module other than the anchor imports this module (AGENTS rule 9).
-/

@[expose] public section

namespace KAM.Provider.Planetary.StrongAMD

open KAM.Planetary KAM.Planetary.StrongAMD

theorem orderedCrossThreshold_isLeast {n : ℕ} {ν : Fin n → ℝ} (hn : 2 ≤ n) (I : OrderedActions ν) :
    IsLeast {b | ∃ (i j : Fin n) (hij : i < j), (j : ℕ) = i + 1 ∧
        b = orderedPairThreshold I i j hij}
      (orderedCrossThreshold hn I) := by
  have := nonempty_adjIdx hn
  refine ⟨?_, ?_⟩
  · obtain ⟨a, ha⟩ := exists_iInf_eq_of_finite
      (fun a : AdjIdx n => orderedPairThreshold I a.1 a.upperIdx a.lt_upperIdx)
    exact ⟨a.1, a.upperIdx, a.lt_upperIdx, rfl, ha⟩
  · rintro b ⟨i, j, hij, hj, rfl⟩
    have hi : i.val + 1 < n := hj ▸ j.isLt
    obtain rfl : j = ⟨i.val + 1, hi⟩ := Fin.ext hj
    exact iInf_le_of_finite
      (fun a : AdjIdx n => orderedPairThreshold I a.1 a.upperIdx a.lt_upperIdx) ⟨i, hi⟩

end KAM.Provider.Planetary.StrongAMD

end
