/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.StrongAMD.Threshold.Continuity

/-!
# Strong AMD thresholds: cross, star and strong minima

Source: `LP:MAIN L4 (141–160)`, (3) and (14). Track LP, non-frozen.

Finite minima over `Fin`-indexed families are literal `⨅`; each comes with "`≤` every member" and
"equals some member" lemmas (nonemptiness of the index, `1 ≤ n` resp. `2 ≤ n`, is an explicit
hypothesis). Continuity and positivity on the chamber, `B ≤ B_{i,i+1}`, `B ≤ I_i`, and
`B = min (B_cross, I_1)`. The carrier versions (`OrderedActions`) transfer by the one-line
equalities of `Defs`.
-/

@[expose] public noncomputable section

namespace KAM.Planetary.StrongAMD

variable {n : ℕ}

theorem exists_iInf_eq_of_finite {ι : Type*} [Finite ι] [Nonempty ι] (f : ι → ℝ) :
    ∃ i, ⨅ k, f k = f i := by
  have := (Set.range_nonempty f).csInf_mem (Set.finite_range f)
  obtain ⟨i, hi⟩ := this
  exact ⟨i, by rw [hi]; rfl⟩

theorem iInf_le_of_finite {ι : Type*} [Finite ι] (f : ι → ℝ) (i : ι) : ⨅ k, f k ≤ f i :=
  ciInf_le (Set.finite_range f).bddBelow i

theorem continuousOn_iInf_of_finite {X ι : Type*} [TopologicalSpace X] [Fintype ι] [Nonempty ι]
    {s : Set X} {f : ι → X → ℝ} (hf : ∀ i, ContinuousOn (f i) s) :
    ContinuousOn (fun x => ⨅ i, f i x) s := by
  have h : (fun x => ⨅ i, f i x) = fun x => Finset.univ.inf' Finset.univ_nonempty
      (fun i => f i x) := by
    funext x
    refine le_antisymm (Finset.le_inf' _ _ fun i _ => iInf_le_of_finite _ i) ?_
    obtain ⟨i, hi⟩ := exists_iInf_eq_of_finite fun i => f i x
    rw [hi]; exact Finset.inf'_le _ (Finset.mem_univ i)
  rw [h]
  exact ContinuousOn.finset_inf'_apply Finset.univ_nonempty fun i _ => hf i

theorem starThreshold_le (I : Fin n → ℝ) (i : Fin n) : starThreshold I ≤ I i :=
  iInf_le_of_finite _ i

theorem crossThreshold_le (ν I : Fin n → ℝ) (a : AdjIdx n) :
    crossThreshold ν I ≤ pairThreshold ν I a.1 a.upperIdx :=
  iInf_le_of_finite (fun a : AdjIdx n => pairThreshold ν I a.1 a.upperIdx) a

theorem nonempty_adjIdx (hn : 2 ≤ n) : Nonempty (AdjIdx n) :=
  ⟨⟨⟨0, by omega⟩, by show 0 + 1 < n; omega⟩⟩

theorem strongThreshold_le_cross (ν I : Fin n → ℝ) :
    strongThreshold ν I ≤ crossThreshold ν I := min_le_left _ _

theorem strongThreshold_le_star (ν I : Fin n → ℝ) :
    strongThreshold ν I ≤ starThreshold I := min_le_right _ _

theorem strongThreshold_le_pair (ν I : Fin n → ℝ) (a : AdjIdx n) :
    strongThreshold ν I ≤ pairThreshold ν I a.1 a.upperIdx :=
  (strongThreshold_le_cross ν I).trans (crossThreshold_le ν I a)

theorem strongThreshold_le_action (ν I : Fin n → ℝ) (i : Fin n) :
    strongThreshold ν I ≤ I i :=
  (strongThreshold_le_star ν I).trans (starThreshold_le I i)

theorem continuousOn_crossThreshold {ν : Fin n → ℝ} (hν : ∀ i, 0 < ν i) (hn : 2 ≤ n) :
    ContinuousOn (crossThreshold ν) (chamber ν) := by
  have := nonempty_adjIdx hn
  exact continuousOn_iInf_of_finite (f := fun (a : AdjIdx n) I => pairThreshold ν I a.1 a.upperIdx)
    fun a => continuousOn_pairThreshold hν a.lt_upperIdx

theorem continuousOn_starThreshold (hn : 1 ≤ n) :
    ContinuousOn (starThreshold (n := n)) Set.univ := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact continuousOn_iInf_of_finite (f := fun (i : Fin n) (I : Fin n → ℝ) => I i)
    fun i => (continuous_apply i).continuousOn

theorem continuousOn_strongThreshold {ν : Fin n → ℝ} (hν : ∀ i, 0 < ν i) (hn : 2 ≤ n) :
    ContinuousOn (strongThreshold ν) (chamber ν) :=
  (continuousOn_crossThreshold hν hn).inf
    ((continuousOn_starThreshold (by omega)).mono (Set.subset_univ _))

/-! ### Carrier versions -/

end KAM.Planetary.StrongAMD
