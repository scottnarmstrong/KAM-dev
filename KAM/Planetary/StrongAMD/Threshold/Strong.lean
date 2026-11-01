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

Package LP-THR, `LP:MAIN L4 (141–160)`, (3) and (14). Track LP, non-frozen; the statement surface is
proposed in docs/tracks/LP/FREEZE-PROPOSAL.md.

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

theorem exists_starThreshold_eq (hn : 1 ≤ n) (I : Fin n → ℝ) : ∃ i, starThreshold I = I i := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact exists_iInf_eq_of_finite _

theorem crossThreshold_le (ν I : Fin n → ℝ) (a : AdjIdx n) :
    crossThreshold ν I ≤ pairThreshold ν I a.1 a.upperIdx :=
  iInf_le_of_finite (fun a : AdjIdx n => pairThreshold ν I a.1 a.upperIdx) a

theorem nonempty_adjIdx (hn : 2 ≤ n) : Nonempty (AdjIdx n) :=
  ⟨⟨⟨0, by omega⟩, by show 0 + 1 < n; omega⟩⟩

theorem exists_crossThreshold_eq (hn : 2 ≤ n) (ν I : Fin n → ℝ) :
    ∃ a : AdjIdx n, crossThreshold ν I = pairThreshold ν I a.1 a.upperIdx := by
  have := nonempty_adjIdx hn
  exact exists_iInf_eq_of_finite (fun a : AdjIdx n => pairThreshold ν I a.1 a.upperIdx)

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

/-- The strong threshold equals one of its members. -/
theorem strongThreshold_eq_member (hn : 2 ≤ n) (ν I : Fin n → ℝ) :
    (∃ a : AdjIdx n, strongThreshold ν I = pairThreshold ν I a.1 a.upperIdx) ∨
      ∃ i : Fin n, strongThreshold ν I = I i := by
  rcases min_choice (crossThreshold ν I) (starThreshold I) with h | h
  · obtain ⟨a, ha⟩ := exists_crossThreshold_eq hn ν I
    exact Or.inl ⟨a, by unfold strongThreshold; rw [h, ha]⟩
  · obtain ⟨i, hi⟩ := exists_starThreshold_eq (by omega) I
    exact Or.inr ⟨i, by unfold strongThreshold; rw [h, hi]⟩

theorem crossThreshold_pos {ν I : Fin n → ℝ} (hν : ∀ i, 0 < ν i) (hI : I ∈ chamber ν)
    (hn : 2 ≤ n) : 0 < crossThreshold ν I := by
  obtain ⟨a, ha⟩ := exists_crossThreshold_eq hn ν I
  rw [ha]; exact pairThreshold_pos hν hI a.lt_upperIdx

theorem starThreshold_pos {ν I : Fin n → ℝ} (hI : I ∈ chamber ν) (hn : 1 ≤ n) :
    0 < starThreshold I := by
  obtain ⟨i, hi⟩ := exists_starThreshold_eq hn I
  rw [hi]; exact hI.1 i

theorem strongThreshold_pos {ν I : Fin n → ℝ} (hν : ∀ i, 0 < ν i) (hI : I ∈ chamber ν)
    (hn : 2 ≤ n) : 0 < strongThreshold ν I :=
  lt_min (crossThreshold_pos hν hI hn) (starThreshold_pos hI (by omega))

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

/-- `B(I) = min (B_cross(I), I_1)` (`LP:MAIN (14)`); `I_1` is the first action. -/
theorem strongThreshold_eq_min_first {ν I : Fin n → ℝ} (hν : ∀ i, 0 < ν i) (hI : I ∈ chamber ν)
    (hn : 2 ≤ n) :
    strongThreshold ν I = min (crossThreshold ν I) (I ⟨0, by omega⟩) := by
  unfold strongThreshold
  apply le_antisymm
  · exact min_le_min le_rfl (starThreshold_le I _)
  · refine le_min (min_le_left _ _) ?_
    have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
    refine le_ciInf fun i => ?_
    by_cases h0 : i.val = 0
    · have : i = ⟨0, by omega⟩ := Fin.ext h0
      rw [this]; exact min_le_right _ _
    · let a : AdjIdx n := ⟨⟨i.val - 1, by omega⟩, by show i.val - 1 + 1 < n; omega⟩
      have hs : a.upperIdx = i := Fin.ext (by show i.val - 1 + 1 = i.val; omega)
      have h1 := pairThreshold_lt hν hI a.lt_upperIdx
      rw [hs] at h1
      have h2 := crossThreshold_le ν I a
      rw [hs] at h2
      exact (min_le_left _ _).trans (h2.trans h1.le)

/-! ### Carrier versions -/

theorem orderedPairThreshold_pos {ν : Fin n → ℝ} (hν : ∀ i, 0 < ν i) (I : OrderedActions ν)
    {i j : Fin n} (hij : i < j) : 0 < orderedPairThreshold I i j hij :=
  pairThreshold_pos hν I.2 hij

theorem orderedPairThreshold_lt {ν : Fin n → ℝ} (hν : ∀ i, 0 < ν i) (I : OrderedActions ν)
    {i j : Fin n} (hij : i < j) : orderedPairThreshold I i j hij < I.1 j :=
  pairThreshold_lt hν I.2 hij

theorem continuous_orderedPairThreshold {ν : Fin n → ℝ} (hν : ∀ i, 0 < ν i) {i j : Fin n}
    (hij : i < j) : Continuous fun I : OrderedActions ν => orderedPairThreshold I i j hij :=
  (continuousOn_iff_continuous_domRestrict.1 (continuousOn_pairThreshold hν hij))

theorem orderedStrongThreshold_pos {ν : Fin n → ℝ} (hν : ∀ i, 0 < ν i) (hn : 2 ≤ n)
    (I : OrderedActions ν) : 0 < orderedStrongThreshold hn I :=
  strongThreshold_pos hν I.2 hn

theorem continuous_orderedStrongThreshold {ν : Fin n → ℝ} (hν : ∀ i, 0 < ν i) (hn : 2 ≤ n) :
    Continuous fun I : OrderedActions ν => orderedStrongThreshold hn I :=
  continuousOn_iff_continuous_domRestrict.1 (continuousOn_strongThreshold hν hn)

theorem orderedStrongThreshold_eq_min_first {ν : Fin n → ℝ} (hν : ∀ i, 0 < ν i) (hn : 2 ≤ n)
    (I : OrderedActions ν) :
    orderedStrongThreshold hn I = min (orderedCrossThreshold hn I) (I.1 ⟨0, by omega⟩) :=
  strongThreshold_eq_min_first hν I.2 hn

end KAM.Planetary.StrongAMD
