/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.StrongAMD.Threshold.Strong

/-!
# Provider for `KAM.Planetary.StrongAMD.orderedStrongThreshold_isLeast`

Provider for the frozen theorem `KAM.Planetary.StrongAMD.orderedStrongThreshold_isLeast`,
characterization theorem of `orderedStrongThreshold`;
track LP (`LP:MAIN §1 (3) (47–55)`).

The theorem `KAM.Provider.Planetary.StrongAMD.orderedStrongThreshold_isLeast` states the anchor's
exact type text (its draft file under `docs/tracks/LP/freeze/draft7/`). Its proof is the proof of
the former implementation lemma `KAM.Planetary.StrongAMD.orderedStrongThreshold_isLeast`
(`KAM.Planetary.StrongAMD.PlanarSafety.SourceThreshold`), moved verbatim at the freeze (D62); the
sibling `orderedCrossThreshold_isLeast` it uses is inlined verbatim
as a private theorem. No module other than the anchor imports this module (AGENTS rule 9).
-/

@[expose] public section

namespace KAM.Provider.Planetary.StrongAMD

open KAM.Planetary KAM.Planetary.StrongAMD

/-- The sibling characterization, inlined verbatim. -/
private theorem orderedCrossThreshold_isLeast {n : ℕ} {ν : Fin n → ℝ} (hn : 2 ≤ n)
    (I : OrderedActions ν) : IsLeast {b | ∃ (i j : Fin n) (hij : i < j), (j : ℕ) = i + 1 ∧
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

theorem orderedStrongThreshold_isLeast {n : ℕ} {ν : Fin n → ℝ} (hn : 2 ≤ n) (I : OrderedActions ν) :
    IsLeast ({b | ∃ (i j : Fin n) (hij : i < j), (j : ℕ) = i + 1 ∧
        b = orderedPairThreshold I i j hij} ∪ Set.range I.1)
      (orderedStrongThreshold hn I) := by
  obtain ⟨hcm, hcl⟩ := orderedCrossThreshold_isLeast hn I
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  obtain ⟨k, hk⟩ := exists_iInf_eq_of_finite I.1
  show IsLeast _ (min (orderedCrossThreshold hn I) (⨅ i : Fin n, I.1 i))
  refine ⟨?_, ?_⟩
  · rcases min_choice (orderedCrossThreshold hn I) (⨅ i : Fin n, I.1 i) with h | h
    · rw [h]
      exact Or.inl hcm
    · rw [h, hk]
      exact Or.inr ⟨k, rfl⟩
  · rintro b (hb | ⟨i, rfl⟩)
    · exact (min_le_left _ _).trans (hcl hb)
    · exact (min_le_right _ _).trans (iInf_le_of_finite I.1 i)

end KAM.Provider.Planetary.StrongAMD

end
