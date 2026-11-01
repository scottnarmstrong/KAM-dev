/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Assembly.Consts
public import KAM.Wave.Assembly.Ext

/-!
# W8: geometry of the trimmed shells (blueprint `bpW:w8:shell-data` (ii), `bpW:w8:boundaries`)

Off the frontier: source-faithful infrastructure used by several nodes. The dependency graph is
still being built. Blueprint labels `bpW:w8:shells`, `bpW:w8:boundaries`; the W5/W6-free part (ii)
of `bpW:w8:shell-data` (milestone W8).

For every `t₀ > 0`: the trimmed shell `Π_n` is open (`w8Pi_isOpen`), `Π_n ⊆ R_n ⊆ (0, t_n)²`,
every `ξ ∈ Π_n` has `α_n < ξ_i < t_n - α_n` (`w8Pi_coord`), points of `Π_n` are at distance
`> α_n` from `ℝ² ∖ R_n` (`w8Pi_sep`), trimmed shells of different index are disjoint and at
distance `> max(α_n, α_{n'})` (`w8Pi_sep_of_ne`), and the boundary layer `R_n ∖ Π_n` has measure
`≤ 7 α_n t_n` (`volume_w8Rn_diff_w8Pi_le`, Remark `bpW:w8:boundaries`).
-/

public section

open Set MeasureTheory Filter Topology

namespace KAM.Wave

variable {t0 : ℝ}

theorem w8tn_pos (ht : 0 < t0) (n : ℕ) : 0 < w8tn t0 n := shellT_pos (by norm_num) ht n

theorem w8tn_le (ht : 0 < t0) (n : ℕ) : w8tn t0 n ≤ t0 := by
  unfold w8tn shellT
  exact mul_le_of_le_one_left ht.le (pow_le_one₀ (by norm_num) (by norm_num))

theorem w8alpha_pos (ht : 0 < t0) (n : ℕ) : 0 < w8alpha t0 n :=
  Real.rpow_pos_of_pos (w8tn_pos ht n) _

/-- `α_n < t_n` when `t₀ < 1`. -/
theorem w8alpha_lt_tn (ht : 0 < t0) (ht1 : t0 < 1) (n : ℕ) : w8alpha t0 n < w8tn t0 n := by
  have h0 := w8tn_pos ht n
  have h1 : w8tn t0 n < 1 := lt_of_le_of_lt (w8tn_le ht n) ht1
  unfold w8alpha
  calc w8tn t0 n ^ (95 / 64 : ℝ) < w8tn t0 n ^ (1 : ℝ) :=
        Real.rpow_lt_rpow_of_exponent_gt h0 h1 (by norm_num)
    _ = w8tn t0 n := Real.rpow_one _

theorem w8Rn_subset_box (n : ℕ) : w8Rn t0 n ⊆ boxIoo 0 (w8tn t0 n) := fun _ h => h.1

/-- The box `(0, t)²` lies in `{|ξ| ≤ 1/2}` for `t ≤ 1/2`. -/
theorem boxIoo_subset_closedBall_half {t : ℝ} (h : t ≤ 1 / 2) :
    boxIoo 0 t ⊆ {ξ : Fin 2 → ℝ | ‖ξ‖ ≤ 1 / 2} := fun ξ hξ => by
  refine (pi_norm_le_iff_of_nonneg (by norm_num)).2 fun i => ?_
  have := hξ i (mem_univ i)
  rw [Real.norm_eq_abs, abs_of_pos this.1]
  linarith [this.2]

/-- `Π_n = {ξ : dist(ξ, ℝ² ∖ R_n) > α_n}`: the condition `ξ ∈ R_n` is implied. -/
theorem w8Pi_eq (ht : 0 < t0) (n : ℕ) :
    w8Pi t0 n = {ξ | w8alpha t0 n < Metric.infDist ξ (w8Rn t0 n)ᶜ} := by
  ext ξ
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  by_contra hξ
  have h0 := (w8ext_infDist (w8Rn t0 n)ᶜ 0).2.1 ξ hξ
  have h' : w8alpha t0 n < Metric.infDist ξ (w8Rn t0 n)ᶜ := h
  rw [h0] at h'
  exact absurd h' (not_lt.2 (w8alpha_pos ht n).le)

/-- (`bpW:w8:shell-data` (ii)) `Π_n` is open. -/
theorem w8Pi_isOpen (ht : 0 < t0) (n : ℕ) : IsOpen (w8Pi t0 n) := by
  rw [w8Pi_eq ht]; exact (w8ext_infDist _ _).1

/-- (`bpW:w8:shell-data` (ii)) `Π_n` is Borel. -/
theorem w8Pi_measurableSet (ht : 0 < t0) (n : ℕ) : MeasurableSet (w8Pi t0 n) :=
  (w8Pi_isOpen ht n).measurableSet

/-- (`bpW:w8:shell-data` (ii)) `Π_n ⊆ R_n`. -/
theorem w8Pi_subset_Rn (n : ℕ) : w8Pi t0 n ⊆ w8Rn t0 n := fun _ h => h.1

/-- (`bpW:w8:shell-data` (ii)) `Π_n ⊆ R_n ⊆ (0, t_n)² ⊆ {|ξ| ≤ 1/2}` for `t₀ ≤ 1/2`. -/
theorem w8Pi_subset_ball (ht : 0 < t0) (ht2 : t0 ≤ 1 / 2) (n : ℕ) :
    w8Pi t0 n ⊆ {ξ : Fin 2 → ℝ | ‖ξ‖ ≤ 1 / 2} :=
  ((w8Pi_subset_Rn n).trans (w8Rn_subset_box n)).trans
    (boxIoo_subset_closedBall_half ((w8tn_le ht n).trans ht2))

/-- (`bpW:w8:shell-data` (ii)) If `ξ ∈ Π_n` and `ξ' ∉ R_n`, then `|ξ - ξ'| > α_n`. -/
theorem w8Pi_sep {n : ℕ} {ξ ξ' : Fin 2 → ℝ} (hξ : ξ ∈ w8Pi t0 n) (hξ' : ξ' ∉ w8Rn t0 n) :
    w8alpha t0 n < dist ξ ξ' :=
  lt_of_lt_of_le hξ.2 ((w8ext_infDist _ 0).2.2 ξ ξ' hξ')

/-- (`bpW:w8:shell-data` (ii)) Every `ξ ∈ Π_n` has `α_n < ξ_i < t_n - α_n`. -/
theorem w8Pi_coord {n : ℕ} {ξ : Fin 2 → ℝ} (hξ : ξ ∈ w8Pi t0 n) (i : Fin 2) :
    w8alpha t0 n < ξ i ∧ ξ i < w8tn t0 n - w8alpha t0 n := by
  have hi : 0 < ξ i ∧ ξ i < w8tn t0 n := hξ.1.1 i (mem_univ i)
  constructor
  · have hJ : Function.update ξ i 0 ∉ w8Rn t0 n := fun h => by
      have := (h.1 i (mem_univ i)).1
      simp at this
    have hd : dist ξ (Function.update ξ i 0) ≤ ξ i := by
      rw [dist_pi_le_iff hi.1.le]
      intro j
      by_cases hj : j = i
      · subst hj; simp [abs_of_pos hi.1]
      · simp [Function.update_of_ne hj, hi.1.le]
    linarith [w8Pi_sep hξ hJ]
  · have hJ : Function.update ξ i (w8tn t0 n) ∉ w8Rn t0 n := fun h => by
      have := (h.1 i (mem_univ i)).2
      simp only [Function.update_self] at this
      exact lt_irrefl _ this
    have hd : dist ξ (Function.update ξ i (w8tn t0 n)) ≤ w8tn t0 n - ξ i := by
      rw [dist_pi_le_iff (by linarith [hi.2])]
      intro j
      by_cases hj : j = i
      · subst hj; simp only [Function.update_self, Real.dist_eq]
        rw [abs_of_neg (by linarith [hi.2])]; ring_nf; rfl
      · simp [Function.update_of_ne hj]; linarith [hi.2]
    linarith [w8Pi_sep hξ hJ]

/-- The shells `R_n` (`q = 1/2`) are pairwise disjoint (W7 `bpW:w7:shell-geom` (i)). -/
theorem w8Rn_disjoint (ht : 0 < t0) {n n' : ℕ} (h : n ≠ n') :
    Disjoint (w8Rn t0 n) (w8Rn t0 n') := by
  rcases lt_or_gt_of_ne h with h | h
  · exact shellSet_disjoint (by norm_num) (by norm_num) ht h
  · exact (shellSet_disjoint (by norm_num) (by norm_num) ht h).symm

/-- (`bpW:w8:shell-data` (ii), `bpW:w8:boundaries`) Trimmed shells of different index are
disjoint. -/
theorem w8Pi_disjoint (ht : 0 < t0) {n n' : ℕ} (h : n ≠ n') :
    Disjoint (w8Pi t0 n) (w8Pi t0 n') :=
  (w8Rn_disjoint ht h).mono (w8Pi_subset_Rn n) (w8Pi_subset_Rn n')

/-- (`bpW:w8:shell-data` (ii), `bpW:w8:boundaries`) Points of trimmed shells of different index
are at distance `> max(α_n, α_{n'})`. -/
theorem w8Pi_sep_of_ne (ht : 0 < t0) {n n' : ℕ} (h : n ≠ n') {ξ ξ' : Fin 2 → ℝ}
    (hξ : ξ ∈ w8Pi t0 n) (hξ' : ξ' ∈ w8Pi t0 n') :
    max (w8alpha t0 n) (w8alpha t0 n') < dist ξ ξ' := by
  have h1 : ξ' ∉ w8Rn t0 n := fun hm =>
    Set.disjoint_left.1 (w8Rn_disjoint ht h) hm (w8Pi_subset_Rn n' hξ')
  have h2 : ξ ∉ w8Rn t0 n' := fun hm =>
    Set.disjoint_left.1 (w8Rn_disjoint ht h) (w8Pi_subset_Rn n hξ) hm
  refine max_lt (w8Pi_sep hξ h1) ?_
  rw [dist_comm]; exact w8Pi_sep hξ' h2

/-- `Π_n` lies in W7's inner shell `U_{-α_n} R_n` (`shellInner`). -/
theorem w8Pi_subset_shellInner (n : ℕ) :
    w8Pi t0 n ⊆ shellInner (1 / 2) t0 n (w8alpha t0 n) :=
  fun _ hξ => ⟨hξ.1, hξ.2⟩

/-- For `a < b`, W7's inner shell `U_{-b} R_n` lies in `{dist(·, ℝ² ∖ R_n) > a}`. -/
theorem shellInner_subset_w8Pi_of_lt {n : ℕ} {b : ℝ}
    (hab : w8alpha t0 n < b) : shellInner (1 / 2) t0 n b ⊆ w8Pi t0 n := by
  intro ξ hξ
  exact ⟨hξ.1, hab.trans hξ.2⟩

/-- **Boundary layer** (Remark `bpW:w8:boundaries`; W7 `bpW:w7:shell-geom` (ii)):
`volume (R_n ∖ Π_n) ≤ 7 α_n t_n` for `0 < t₀ < 1`. -/
theorem volume_w8Rn_diff_w8Pi_le (ht : 0 < t0) (ht1 : t0 < 1) (n : ℕ) :
    volume (w8Rn t0 n \ w8Pi t0 n) ≤
      ENNReal.ofReal (7 * w8alpha t0 n * w8tn t0 n) := by
  set α := w8alpha t0 n
  set t := w8tn t0 n
  have hα := w8alpha_pos ht n
  have hαt : α < t := w8alpha_lt_tn ht ht1 n
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), volume (w8Rn t0 n \ w8Pi t0 n) ≤
      ENNReal.ofReal (7 * (α + ε) * t) := by
    have : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ∈ Ioo 0 (t - α) :=
      Ioo_mem_nhdsGT (by linarith)
    filter_upwards [this] with ε hε
    have hsub : w8Rn t0 n \ w8Pi t0 n ⊆ shellSet (1 / 2) t0 n \ shellInner (1 / 2) t0 n (α + ε) :=
      fun ξ hξ => ⟨hξ.1, fun hin => hξ.2 (shellInner_subset_w8Pi_of_lt (by linarith [hε.1])
        hin)⟩
    have htt : t = shellT (1 / 2) t0 n := rfl
    exact (measure_mono hsub).trans (volume_shell_diff_inner_le (by norm_num) (by norm_num) ht n
      (by linarith [hε.1]) (by linarith [hε.2]))
  have hlim : Tendsto (fun ε : ℝ => ENNReal.ofReal (7 * (α + ε) * t)) (𝓝[>] 0)
      (𝓝 (ENNReal.ofReal (7 * α * t))) := by
    have : Tendsto (fun ε : ℝ => 7 * (α + ε) * t) (𝓝 0) (𝓝 (7 * (α + 0) * t)) :=
      ((continuous_const.mul (continuous_const.add continuous_id)).mul
        continuous_const).tendsto 0
    rw [add_zero] at this
    exact (ENNReal.continuous_ofReal.tendsto _).comp (this.mono_left nhdsWithin_le_nhds)
  exact ge_of_tendsto hlim hev

end KAM.Wave

end
