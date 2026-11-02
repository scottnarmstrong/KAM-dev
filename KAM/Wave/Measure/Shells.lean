/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Pi
public import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# W7: action shells and their geometry (blueprint `bpW:w7:shells`, `bpW:w7:shell-geom`)

`t_k = q^k t₀`, the shell `R_k = (0, t_k)² ∖ (0, t_{k+1})²` and the inner shell
`U_{-a} R_k = {I ∈ R_k : dist_∞ (I, ℝ² ∖ R_k) > a}`, where `dist_∞ (I, ℝ² ∖ R_k)` is
`Metric.infDist I (R_k)ᶜ` for the sup-norm metric of `Fin 2 → ℝ`. We prove (i) the shells are
pairwise disjoint Borel sets covering `(0, t_k)²` with `volume R_l = (1 - q²) t_l²`, (ii) the
boundary-layer estimate `volume (R_k ∖ U_{-a} R_k) ≤ 7 a t_k`, (iii) `R_k ⊆ {|I|_∞ ≥ t_{k+1}}` of
diameter `≤ t_k`.
-/

@[expose] public section

open MeasureTheory Set

namespace KAM.Wave

/-- `t_k = q^k t₀`. -/
def shellT (q t0 : ℝ) (k : ℕ) : ℝ := q ^ k * t0

/-- The box `(a, b)²` in `Fin 2 → ℝ`. -/
def boxIoo (a b : ℝ) : Set (Fin 2 → ℝ) := Set.pi Set.univ fun _ => Set.Ioo a b

/-- The shell `R_k = (0, t_k)² ∖ (0, t_{k+1})²` (blueprint `bpW:w7:shells`). -/
def shellSet (q t0 : ℝ) (k : ℕ) : Set (Fin 2 → ℝ) :=
  boxIoo 0 (shellT q t0 k) \ boxIoo 0 (shellT q t0 (k + 1))

/-- The inner shell `U_{-a} R_k = {I ∈ R_k : dist_∞ (I, ℝ² ∖ R_k) > a}` (blueprint
`bpW:w7:shells`): the distance to the complement is the infimum `Metric.infDist` for the
sup-norm metric of `Fin 2 → ℝ`. -/
def shellInner (q t0 : ℝ) (k : ℕ) (a : ℝ) : Set (Fin 2 → ℝ) :=
  {I | I ∈ shellSet q t0 k ∧ a < Metric.infDist I (shellSet q t0 k)ᶜ}

/-- Equivalent uniform-margin form of the inner shell: `I ∈ R_k` and some `b > a` bounds the
distance from `I` to every point of the complement from below. -/
theorem mem_shellInner_iff {q t0 : ℝ} {k : ℕ} {a : ℝ} {I : Fin 2 → ℝ} :
    I ∈ shellInner q t0 k a ↔
      I ∈ shellSet q t0 k ∧ ∃ b, a < b ∧ ∀ J, J ∉ shellSet q t0 k → b ≤ dist I J := by
  have hne : (shellSet q t0 k)ᶜ.Nonempty := ⟨0, fun h => lt_irrefl (0 : ℝ) (h.1 0 (mem_univ 0)).1⟩
  constructor
  · rintro ⟨hI, hd⟩
    exact ⟨hI, _, hd, fun J hJ => Metric.infDist_le_dist_of_mem hJ⟩
  · rintro ⟨hI, b, hab, hb⟩
    exact ⟨hI, lt_of_lt_of_le hab ((Metric.le_infDist hne).2 fun J hJ => hb J hJ)⟩

theorem measurableSet_boxIoo (a b : ℝ) : MeasurableSet (boxIoo a b) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ioo

theorem volume_boxIoo (a b : ℝ) :
    volume (boxIoo a b) = ENNReal.ofReal (b - a) * ENNReal.ofReal (b - a) := by
  unfold boxIoo
  rw [Real.volume_pi_Ioo, Fin.prod_univ_two]

theorem volume_boxIoo_of_nonneg {a b : ℝ} (h : a ≤ b) :
    volume (boxIoo a b) = ENNReal.ofReal ((b - a) ^ 2) := by
  rw [volume_boxIoo, ← ENNReal.ofReal_mul (sub_nonneg.2 h)]; congr 1; ring

theorem boxIoo_subset {a b c d : ℝ} (h1 : c ≤ a) (h2 : b ≤ d) : boxIoo a b ⊆ boxIoo c d := by
  intro x hx i _
  exact ⟨lt_of_le_of_lt h1 (hx i (mem_univ i)).1, lt_of_lt_of_le (hx i (mem_univ i)).2 h2⟩

theorem shellT_pos {q t0 : ℝ} (hq : 0 < q) (ht : 0 < t0) (k : ℕ) : 0 < shellT q t0 k := by
  unfold shellT; positivity

theorem shellT_succ (q t0 : ℝ) (k : ℕ) : shellT q t0 (k + 1) = q * shellT q t0 k := by
  unfold shellT; ring

theorem shellT_antitone {q t0 : ℝ} (hq : 0 < q) (hq1 : q < 1) (ht : 0 < t0) :
    StrictAnti (shellT q t0) := by
  refine strictAnti_nat_of_succ_lt fun k => ?_
  have := shellT_pos hq ht k
  rw [shellT_succ]; nlinarith

theorem shellT_tendsto {q t0 : ℝ} (hq : 0 < q) (hq1 : q < 1) :
    Filter.Tendsto (shellT q t0) Filter.atTop (nhds 0) := by
  have := (tendsto_pow_atTop_nhds_zero_of_lt_one hq.le hq1).mul_const t0
  rw [zero_mul] at this
  exact this

theorem measurableSet_shellSet (q t0 : ℝ) (k : ℕ) : MeasurableSet (shellSet q t0 k) :=
  (measurableSet_boxIoo _ _).diff (measurableSet_boxIoo _ _)

/-- (i): the volume of a shell. -/
theorem volume_shellSet {q t0 : ℝ} (hq : 0 < q) (hq1 : q < 1) (ht : 0 < t0) (k : ℕ) :
    volume (shellSet q t0 k) = ENNReal.ofReal ((1 - q ^ 2) * shellT q t0 k ^ 2) := by
  have hk := shellT_pos hq ht k
  have hk1 : shellT q t0 (k + 1) ≤ shellT q t0 k := (shellT_antitone hq hq1 ht (Nat.lt_succ_self
      k)).le
  have hsub : boxIoo 0 (shellT q t0 (k + 1)) ⊆ boxIoo 0 (shellT q t0 k) := boxIoo_subset le_rfl hk1
  unfold shellSet
  rw [measure_sdiff hsub (measurableSet_boxIoo _ _).nullMeasurableSet (by
    rw [volume_boxIoo]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)]
  rw [volume_boxIoo_of_nonneg hk.le, volume_boxIoo_of_nonneg (shellT_pos hq ht _).le,
    ← ENNReal.ofReal_sub _ (sq_nonneg _)]
  congr 1
  rw [shellT_succ]; simp only [sub_zero]; ring

/-- (i): the shells are pairwise disjoint. -/
theorem shellSet_disjoint {q t0 : ℝ} (hq : 0 < q) (hq1 : q < 1) (ht : 0 < t0) {k l : ℕ}
    (hkl : k < l) : Disjoint (shellSet q t0 k) (shellSet q t0 l) := by
  rw [Set.disjoint_left]
  intro I hI hI'
  have h1 : boxIoo 0 (shellT q t0 l) ⊆ boxIoo 0 (shellT q t0 (k + 1)) :=
    boxIoo_subset le_rfl ((shellT_antitone hq hq1 ht).antitone (Nat.succ_le_of_lt hkl))
  exact hI.2 (h1 hI'.1)

/-- (i): the shells with index `≥ k` cover `(0, t_k)²`. -/
theorem boxIoo_subset_iUnion_shell {q t0 : ℝ} (hq : 0 < q) (hq1 : q < 1) (ht : 0 < t0) (k : ℕ) :
    boxIoo 0 (shellT q t0 k) ⊆ ⋃ l : ℕ, shellSet q t0 (k + l) := by
  classical
  intro I hI
  have hex : ∃ n : ℕ, I ∉ boxIoo 0 (shellT q t0 (k + n + 1)) := by
    -- some coordinate is `> 0`
    have hpos : ∀ i, 0 < I i := fun i => (hI i (mem_univ i)).1
    obtain ⟨n, hn⟩ := (shellT_tendsto (q := q) (t0 := t0) hq hq1).eventually
      (gt_mem_nhds (hpos 0)) |>.exists
    refine ⟨n, fun h => ?_⟩
    have := (h 0 (mem_univ 0)).2
    have hmono := (shellT_antitone hq hq1 ht).antitone (show n ≤ k + n + 1 by omega)
    linarith
  set n := Nat.find hex with hn
  have hn1 : I ∉ boxIoo 0 (shellT q t0 (k + n + 1)) := Nat.find_spec hex
  refine mem_iUnion.2 ⟨n, ?_, hn1⟩
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · rw [h0]; simpa using hI
  · have := Nat.find_min hex (show n - 1 < n by omega)
    push Not at this
    have e : k + (n - 1) + 1 = k + n := by omega
    rw [e] at this
    exact this

/-- (iii): the shell lies in `{‖I‖ ≥ t_{k+1}}`. -/
theorem shellSet_norm_ge {q t0 : ℝ} {k : ℕ} {I : Fin 2 → ℝ} (hI : I ∈ shellSet q t0 k) :
    shellT q t0 (k + 1) ≤ ‖I‖ := by
  by_contra h
  push Not at h
  apply hI.2
  intro i _
  refine ⟨(hI.1 i (mem_univ i)).1, ?_⟩
  have := norm_le_pi_norm I i
  rw [Real.norm_eq_abs] at this
  exact lt_of_le_of_lt (le_abs_self _) (lt_of_le_of_lt this h)

/-- (iii): the diameter of a shell is at most `t_k`. -/
theorem shellSet_dist_le {q t0 : ℝ} {k : ℕ} {I J : Fin 2 → ℝ} (hI : I ∈ shellSet q t0 k)
    (hJ : J ∈ shellSet q t0 k) (hk : 0 ≤ shellT q t0 k) : dist I J ≤ shellT q t0 k := by
  rw [dist_pi_le_iff hk]
  intro i
  have h1 := hI.1 i (mem_univ i)
  have h2 := hJ.1 i (mem_univ i)
  rw [Real.dist_eq, abs_le]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-- (ii): the boundary layer of a shell. -/
theorem volume_shell_diff_inner_le {q t0 : ℝ} (hq : 0 < q) (hq1 : q < 1) (ht : 0 < t0) (k : ℕ)
    {a : ℝ} (ha : 0 < a) (hak : a ≤ shellT q t0 k) :
    volume (shellSet q t0 k \ shellInner q t0 k a) ≤ ENNReal.ofReal (7 * a * shellT q t0 k) := by
  set t := shellT q t0 k with htdef
  set s := shellT q t0 (k + 1) with hsdef
  have htpos : 0 < t := shellT_pos hq ht k
  have hst : s ≤ t := (shellT_antitone hq hq1 ht (Nat.lt_succ_self k)).le
  have hspos : 0 < s := shellT_pos hq ht _
  -- the two bad sets
  set A : Set (Fin 2 → ℝ) := boxIoo 0 t \ boxIoo a (t - a) with hA
  set B : Set (Fin 2 → ℝ) := Set.pi Set.univ (fun _ => Set.Ioc 0 (s + a)) \ boxIoo 0 s with hB
  have hsub : shellSet q t0 k \ shellInner q t0 k a ⊆ A ∪ B := by
    intro I ⟨hI, hnot⟩
    have hle : Metric.infDist I (shellSet q t0 k)ᶜ ≤ a := by
      by_contra hcon
      push Not at hcon
      exact hnot ⟨hI, hcon⟩
    -- a closed superset of the complement realizes the distance
    set C : Set (Fin 2 → ℝ) := (boxIoo 0 t)ᶜ ∪ Set.pi Set.univ (fun _ => Set.Icc 0 s) with hC
    have hCcl : IsClosed C :=
      (isOpen_set_pi Set.finite_univ fun _ _ => isOpen_Ioo).isClosed_compl.union
        (isClosed_set_pi fun _ _ => isClosed_Icc)
    have hne : (shellSet q t0 k)ᶜ.Nonempty :=
      ⟨0, fun h => lt_irrefl (0 : ℝ) (h.1 0 (mem_univ 0)).1⟩
    have hsubC : (shellSet q t0 k)ᶜ ⊆ C := by
      intro J hJ
      by_cases hJt : J ∈ boxIoo 0 t
      · right
        have hJs : J ∈ boxIoo 0 s := by
          by_contra h; exact hJ ⟨hJt, h⟩
        intro i _
        exact ⟨(hJs i (mem_univ i)).1.le, (hJs i (mem_univ i)).2.le⟩
      · left; exact hJt
    obtain ⟨J, hJC, hJd⟩ := hCcl.exists_infDist_eq_dist (hne.mono hsubC) I
    have hd : dist I J ≤ a := by
      rw [← hJd]
      exact (Metric.infDist_le_infDist_of_subset hsubC hne).trans hle
    have hcoord : ∀ i, |I i - J i| ≤ a := fun i => by
      have := dist_le_pi_dist I J i
      rw [Real.dist_eq] at this; linarith
    rcases hJC with hJt | hJs
    · left
      refine ⟨hI.1, fun hin => hJt ?_⟩
      intro i _
      have h1 := hcoord i
      have h2 := hin i (mem_univ i)
      rw [abs_le] at h1
      constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
    · right
      refine ⟨fun i _ => ⟨(hI.1 i (mem_univ i)).1, ?_⟩, hI.2⟩
      have h1 := hcoord i
      have h2 := (hJs i (mem_univ i)).2
      rw [abs_le] at h1; linarith [h1.1]
  have hAvol : volume A ≤ ENNReal.ofReal (4 * a * t) := by
    have hin : boxIoo a (t - a) ⊆ boxIoo 0 t := boxIoo_subset ha.le (by linarith)
    rw [hA, measure_sdiff hin (measurableSet_boxIoo _ _).nullMeasurableSet (by
      rw [volume_boxIoo]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)]
    rw [tsub_le_iff_right, volume_boxIoo, volume_boxIoo, sub_zero, ← ENNReal.ofReal_mul htpos.le]
    rcases le_or_gt (2 * a) t with h2 | h2
    · have e1 : t - a - a = t - 2 * a := by ring
      rw [e1, ← ENNReal.ofReal_mul (by linarith), ← ENNReal.ofReal_add (by positivity)
        (by nlinarith)]
      refine ENNReal.ofReal_le_ofReal ?_
      nlinarith
    · have : ENNReal.ofReal (t - a - a) = 0 := ENNReal.ofReal_of_nonpos (by linarith)
      rw [this, zero_mul, add_zero]
      refine ENNReal.ofReal_le_ofReal ?_
      nlinarith
  have hBvol : volume B ≤ ENNReal.ofReal (3 * a * t) := by
    have hin : boxIoo 0 s ⊆ Set.pi Set.univ (fun _ => Set.Ioc 0 (s + a)) := by
      intro x hx i _
      exact ⟨(hx i (mem_univ i)).1, by linarith [(hx i (mem_univ i)).2]⟩
    have hIoc : volume (Set.pi Set.univ (fun _ : Fin 2 => Set.Ioc (0 : ℝ) (s + a))) =
        ENNReal.ofReal ((s + a) ^ 2) := by
      rw [Real.volume_pi_Ioc (a := fun _ => (0 : ℝ)) (b := fun _ => s + a), Fin.prod_univ_two,
        ← ENNReal.ofReal_mul (by linarith)]
      congr 1; ring
    rw [hB, measure_sdiff hin (measurableSet_boxIoo _ _).nullMeasurableSet (by
      rw [volume_boxIoo]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)]
    rw [hIoc, volume_boxIoo_of_nonneg hspos.le, ← ENNReal.ofReal_sub _ (sq_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    nlinarith
  calc volume (shellSet q t0 k \ shellInner q t0 k a) ≤ volume (A ∪ B) := measure_mono hsub
    _ ≤ volume A + volume B := measure_union_le _ _
    _ ≤ ENNReal.ofReal (4 * a * t) + ENNReal.ofReal (3 * a * t) := add_le_add hAvol hBvol
    _ = ENNReal.ofReal (7 * a * t) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring

end KAM.Wave
