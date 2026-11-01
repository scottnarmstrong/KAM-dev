/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.StrongAMD.Threshold.Strong

/-!
# Attained-minimum characterizations of the carrier cross and strong thresholds

Package LP-FREEZE7 (`LP:MAIN §1 (3) (47–55)`, `L4 (141–160)`), track LP, non-frozen.
The statement surface is proposed in docs/tracks/LP/FREEZE-PROPOSAL.md.

MAIN (3) defines `B_cross(I) = min_{i<n} B_{i,i+1}(I)` and `B(I) = min (B_cross(I), min_i I_i)` as
genuine minima on the chamber. The carrier definitions `orderedCrossThreshold hn I` and
`orderedStrongThreshold hn I` are literal finite infima (`⨅`) over `AdjIdx n` and `Fin n`; with
`2 ≤ n` both index types are nonempty, so these infima are attained minima. The two theorems below
state this as `IsLeast` of the explicit finite sets of MAIN (3), so that each carrier threshold is
one semantic unit with its characterization (OD-2 under OD-11 (b), D59):

* `orderedCrossThreshold_isLeast`: `B_cross(I)` is the least of the adjacent pair thresholds
  `B_{i,j}(I)`, `j = i + 1`;
* `orderedStrongThreshold_isLeast`: `B(I)` is the least of those pair thresholds and the actions
  `I_i`.
-/

@[expose] public noncomputable section

namespace KAM.Planetary.StrongAMD

variable {n : ℕ}

/-- **`B_cross` is an attained minimum** (`LP:MAIN §1 (3) (47–55)`): on the carrier, for `2 ≤ n`,
`orderedCrossThreshold hn I` is the least element of the set of adjacent pair thresholds
`B_{i,i+1}(I)`. -/
theorem orderedCrossThreshold_isLeast {ν : Fin n → ℝ} (hn : 2 ≤ n) (I : OrderedActions ν) :
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

/-- **`B` is an attained minimum** (`LP:MAIN §1 (3) (47–55)`): on the carrier, for `2 ≤ n`,
`orderedStrongThreshold hn I = min (B_cross(I), min_i I_i)` is the least element of the set of
adjacent pair thresholds `B_{i,i+1}(I)` together with the actions `I_i`. -/
theorem orderedStrongThreshold_isLeast {ν : Fin n → ℝ} (hn : 2 ≤ n) (I : OrderedActions ν) :
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

end KAM.Planetary.StrongAMD
