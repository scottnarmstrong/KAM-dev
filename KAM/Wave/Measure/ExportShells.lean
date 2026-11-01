/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Measure.Shells

/-!
# W7: the shell partition and the shell geometry as single statements
(blueprint `bpW:w7:shell-geom`, step `stepW:w7:partition`)

Off-frontier, source-faithful infrastructure (W-GRAPH-CLOSE); the dependency graph is still being
built.

* `shellSet_partition` (step `stepW:w7:partition`): every `I ∈ (0, t_k)²` lies in exactly one shell
  `R_l` with `l ≥ k`, namely the one with `t_{l+1} ≤ max_i I_i < t_l`; `Leb(R_l) = t_l² - t_{l+1}²`.
* `iUnion_shellSet_eq_box`: `⋃_{l ≥ k} R_l = (0, t_k)²`, both inclusions (the reverse inclusion is
  the one used inline in `volume_box_diff_le`, `Density.lean:89-93`).
* `shellGeom` (Lemma `bpW:w7:shell-geom`): (i) the shells `R_l`, `l ≥ k`, are pairwise disjoint
  Borel sets with union `(0, t_k)²` and `Leb(R_l) = (1 - q²) t_l²`; (ii) for `0 < a ≤ t_k`,
  `Leb(R_k ∖ U_{-a} R_k) ≤ 7 a t_k`; (iii) `R_k ⊆ {|I|_∞ ≥ t_{k+1}}` and `diam_∞ R_k ≤ t_k`.

The standing data of Definition `bpW:w7:shells` are `q ∈ (0,1)` and `t₀ ∈ (0, 1/2]`; the statements
below use only `t₀ > 0` (the bound `t₀ ≤ 1/2` is not needed), so they contain the blueprint's case.
-/

@[expose] public section

open MeasureTheory Set

namespace KAM.Wave

variable {q t0 : ℝ}

/-- `I ∈ R_l` iff `I ∈ (0, t_l)²` and `max_i I_i ≥ t_{l+1}` (for `I` with positive entries the
second condition is `I ∉ (0, t_{l+1})²`). -/
theorem mem_shellSet_iff_max {l : ℕ} {I : Fin 2 → ℝ} :
    I ∈ shellSet q t0 l ↔
      I ∈ boxIoo 0 (shellT q t0 l) ∧ shellT q t0 (l + 1) ≤ max (I 0) (I 1) := by
  unfold shellSet boxIoo
  simp only [mem_sdiff, Set.mem_pi, mem_univ, forall_const, mem_Ioo, Fin.forall_fin_two,
    not_and_or, not_lt, le_max_iff]
  constructor
  · rintro ⟨h, h'⟩
    refine ⟨h, ?_⟩
    rcases h' with (h0 | h0) | (h1 | h1)
    · exact absurd h.1.1 (not_lt.2 h0)
    · exact Or.inl h0
    · exact absurd h.2.1 (not_lt.2 h1)
    · exact Or.inr h1
  · rintro ⟨h, h'⟩
    exact ⟨h, h'.elim (fun h0 => Or.inl (Or.inr h0)) fun h1 => Or.inr (Or.inr h1)⟩

/-- `⋃_{l ≥ k} R_l ⊆ (0, t_k)²` (the reverse inclusion of `bpW:w7:shell-geom` (i)). -/
theorem iUnion_shellSet_subset_box (hq : 0 < q) (hq1 : q < 1) (ht : 0 < t0) (k : ℕ) :
    (⋃ (l : ℕ) (_ : k ≤ l), shellSet q t0 l) ⊆ boxIoo 0 (shellT q t0 k) :=
  iUnion₂_subset fun _ hl => sdiff_subset.trans
    (boxIoo_subset le_rfl ((shellT_antitone hq hq1 ht).antitone hl))

/-- **`⋃_{l ≥ k} R_l = (0, t_k)²`** (blueprint `bpW:w7:shell-geom` (i), both inclusions). -/
theorem iUnion_shellSet_eq_box (hq : 0 < q) (hq1 : q < 1) (ht : 0 < t0) (k : ℕ) :
    (⋃ (l : ℕ) (_ : k ≤ l), shellSet q t0 l) = boxIoo 0 (shellT q t0 k) := by
  refine (iUnion_shellSet_subset_box hq hq1 ht k).antisymm fun I hI => ?_
  obtain ⟨n, hn⟩ := mem_iUnion.1 (boxIoo_subset_iUnion_shell hq hq1 ht k hI)
  exact mem_iUnion₂.2 ⟨k + n, Nat.le_add_right k n, hn⟩

/-- The shells are pairwise disjoint. -/
theorem shellSet_pairwise_disjoint (hq : 0 < q) (hq1 : q < 1) (ht : 0 < t0) :
    Pairwise (Function.onFun Disjoint (shellSet q t0)) := by
  intro i j hij
  rcases lt_or_gt_of_ne hij with h | h
  · exact shellSet_disjoint hq hq1 ht h
  · exact (shellSet_disjoint hq hq1 ht h).symm

/-- **Partition** (blueprint step `stepW:w7:partition`): for `I ∈ (0, t_k)²` there is exactly one
`l ≥ k` with `I ∈ R_l`, and it is characterized by `t_{l+1} ≤ max_i I_i < t_l`; moreover
`Leb(R_l) = t_l² - t_{l+1}²` for every `l`. -/
theorem shellSet_partition (hq : 0 < q) (hq1 : q < 1) (ht : 0 < t0) (k : ℕ) :
    (∀ I ∈ boxIoo 0 (shellT q t0 k), ∃! l, k ≤ l ∧ I ∈ shellSet q t0 l) ∧
    (∀ I ∈ boxIoo 0 (shellT q t0 k), ∀ l, k ≤ l →
      (I ∈ shellSet q t0 l ↔
        shellT q t0 (l + 1) ≤ max (I 0) (I 1) ∧ max (I 0) (I 1) < shellT q t0 l)) ∧
    (∀ l, volume (shellSet q t0 l) = ENNReal.ofReal (shellT q t0 l ^ 2 - shellT q t0 (l + 1) ^ 2))
  := by
  refine ⟨fun I hI => ?_, fun I hI l hl => ?_, fun l => ?_⟩
  · rw [← iUnion_shellSet_eq_box hq hq1 ht k] at hI
    obtain ⟨l, hl, hIl⟩ := mem_iUnion₂.1 hI
    refine ⟨l, ⟨hl, hIl⟩, fun l' ⟨_, hIl'⟩ => ?_⟩
    by_contra hne
    exact (shellSet_pairwise_disjoint hq hq1 ht hne).ne_of_mem hIl' hIl rfl
  · have hbox : I ∈ boxIoo 0 (shellT q t0 l) ↔ max (I 0) (I 1) < shellT q t0 l := by
      have hpos : ∀ i, 0 < I i := fun i => (hI i (mem_univ i)).1
      unfold boxIoo
      simp only [Set.mem_pi, mem_univ, forall_const, mem_Ioo, Fin.forall_fin_two, max_lt_iff]
      exact ⟨fun h => ⟨h.1.2, h.2.2⟩, fun h => ⟨⟨hpos 0, h.1⟩, ⟨hpos 1, h.2⟩⟩⟩
    rw [mem_shellSet_iff_max, hbox]
    exact and_comm
  · rw [volume_shellSet hq hq1 ht l, shellT_succ]
    congr 1; ring

/-- **Shell geometry** (blueprint Lemma `bpW:w7:shell-geom`). Let `q ∈ (0,1)`, `t₀ > 0`,
`t_k = q^k t₀`, `R_k = (0,t_k)² ∖ (0,t_{k+1})²` and `U_{-a} R_k` the inner shell.
(i) The shells `R_l`, `l ≥ k`, are pairwise disjoint Borel sets with union `(0, t_k)²`, and
`Leb(R_l) = (1 - q²) t_l²`. (ii) For `0 < a ≤ t_k`, `Leb(R_k ∖ U_{-a} R_k) ≤ 7 a t_k`.
(iii) `R_k ⊆ {I : |I|_∞ ≥ t_{k+1}}` and `diam_∞ R_k ≤ t_k`. -/
theorem shellGeom (hq : 0 < q) (hq1 : q < 1) (ht : 0 < t0) (k : ℕ) :
    -- (i)
    (∀ l l', k ≤ l → k ≤ l' → l ≠ l' → Disjoint (shellSet q t0 l) (shellSet q t0 l')) ∧
    (∀ l, MeasurableSet (shellSet q t0 l)) ∧
    (⋃ (l : ℕ) (_ : k ≤ l), shellSet q t0 l) = boxIoo 0 (shellT q t0 k) ∧
    (∀ l, volume (shellSet q t0 l) = ENNReal.ofReal ((1 - q ^ 2) * shellT q t0 l ^ 2)) ∧
    -- (ii)
    (∀ a : ℝ, 0 < a → a ≤ shellT q t0 k →
      volume (shellSet q t0 k \ shellInner q t0 k a) ≤ ENNReal.ofReal (7 * a * shellT q t0 k)) ∧
    -- (iii)
    shellSet q t0 k ⊆ {I | shellT q t0 (k + 1) ≤ ‖I‖} ∧
    Metric.diam (shellSet q t0 k) ≤ shellT q t0 k := by
  have hk := (shellT_pos hq ht k).le
  refine ⟨fun l l' _ _ hne => shellSet_pairwise_disjoint hq hq1 ht hne,
    measurableSet_shellSet q t0, iUnion_shellSet_eq_box hq hq1 ht k,
    volume_shellSet hq hq1 ht, fun a ha hak => volume_shell_diff_inner_le hq hq1 ht k ha hak,
    fun I hI => shellSet_norm_ge hI,
    Metric.diam_le_of_forall_dist_le hk fun I hI J hJ => shellSet_dist_le hI hJ hk⟩

end KAM.Wave
