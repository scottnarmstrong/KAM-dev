/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Measure.Shells

/-!
# W7: density one from shell estimates (blueprint `bpW:w7:density`)

Off the frontier: source-faithful infrastructure used by several nodes. The dependency graph is
still being built.

If `Γ ⊆ P = (0, ∞)²` is Borel and the relative shell defects
`ε_k = volume (R_k ∖ Γ) / volume R_k` tend to `0`, then
`volume (Γ ∩ B_h) / volume (P ∩ B_h) → 1` along `𝓝[>] 0`, in `ℝ≥0∞`: the exact form of clause (1)
of the frozen `KAM.Wave.nlw2`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace KAM.Wave

theorem posQuadrant_inter_ball {h : ℝ} (hh : 0 < h) :
    {I : Fin 2 → ℝ | ∀ i, 0 < I i} ∩ Metric.ball 0 h = boxIoo 0 h := by
  ext I
  simp only [mem_inter_iff, mem_ofPred_eq, boxIoo, Set.mem_pi, mem_univ, forall_const,
    mem_Ioo, mem_ball_zero_iff]
  rw [pi_norm_lt_iff hh]
  constructor
  · rintro ⟨h1, h2⟩ i
    refine ⟨h1 i, ?_⟩
    have := h2 i
    rwa [Real.norm_eq_abs, abs_of_pos (h1 i)] at this
  · intro h1
    refine ⟨fun i => (h1 i).1, fun i => ?_⟩
    rw [Real.norm_eq_abs, abs_of_pos (h1 i).1]
    exact (h1 i).2

theorem exists_shell_index {q t0 : ℝ} (hq : 0 < q) (hq1 : q < 1) (ht : 0 < t0) {h : ℝ} (hh : 0 < h)
    {k0 : ℕ} (hk0 : h ≤ shellT q t0 k0) :
    ∃ k, k0 ≤ k ∧ shellT q t0 (k + 1) < h ∧ h ≤ shellT q t0 k := by
  classical
  have hex : ∃ n, shellT q t0 n < h :=
    ((shellT_tendsto (t0 := t0) hq hq1).eventually (gt_mem_nhds hh)).exists
  set n := Nat.find hex with hn
  have hn1 : shellT q t0 n < h := Nat.find_spec hex
  have hnk : k0 < n := by
    by_contra hcon
    push Not at hcon
    have := (shellT_antitone hq hq1 ht).antitone hcon
    linarith
  refine ⟨n - 1, by omega, ?_, ?_⟩
  · have e : n - 1 + 1 = n := by omega
    rw [e]; exact hn1
  · have := Nat.find_min hex (show n - 1 < n by omega)
    push Not at this
    exact this

/-- The measure of the defect of a ball, from shell defects bounded by `ē` (blueprint
`bpW:w7:density`, step "Lower bound"). -/
theorem volume_box_diff_le {q t0 : ℝ} (hq : 0 < q) (hq1 : q < 1) (ht : 0 < t0)
    {Γ : Set (Fin 2 → ℝ)} {ē : ℝ} {k : ℕ}
    (hbd : ∀ l, k ≤ l → volume (shellSet q t0 l \ Γ) ≤
      ENNReal.ofReal ē * volume (shellSet q t0 l)) {s : ℝ} (hs : s ≤ shellT q t0 k) :
    volume (boxIoo 0 s \ Γ) ≤ ENNReal.ofReal ē * ENNReal.ofReal (shellT q t0 k ^ 2) := by
  have hcov : boxIoo 0 s \ Γ ⊆ ⋃ l : ℕ, (shellSet q t0 (k + l) \ Γ) := by
    intro I ⟨hI, hIΓ⟩
    have := boxIoo_subset_iUnion_shell hq hq1 ht k (boxIoo_subset le_rfl hs hI)
    obtain ⟨l, hl⟩ := mem_iUnion.1 this
    exact mem_iUnion.2 ⟨l, hl, hIΓ⟩
  calc volume (boxIoo 0 s \ Γ) ≤ volume (⋃ l : ℕ, (shellSet q t0 (k + l) \ Γ)) := measure_mono hcov
    _ ≤ ∑' l : ℕ, volume (shellSet q t0 (k + l) \ Γ) := measure_iUnion_le _
    _ ≤ ∑' l : ℕ, ENNReal.ofReal ē * volume (shellSet q t0 (k + l)) :=
        ENNReal.tsum_le_tsum fun l => hbd (k + l) (by omega)
    _ = ENNReal.ofReal ē * ∑' l : ℕ, volume (shellSet q t0 (k + l)) := by rw [ENNReal.tsum_mul_left]
    _ = ENNReal.ofReal ē * volume (⋃ l : ℕ, shellSet q t0 (k + l)) := by
        rw [measure_iUnion]
        · intro i j hij
          rcases lt_or_gt_of_ne hij with h | h
          · exact shellSet_disjoint hq hq1 ht (by omega)
          · exact (shellSet_disjoint hq hq1 ht (by omega)).symm
        · exact fun l => measurableSet_shellSet q t0 _
    _ ≤ ENNReal.ofReal ē * volume (boxIoo 0 (shellT q t0 k)) := by
        gcongr
        refine iUnion_subset fun l => ?_
        exact (sdiff_subset).trans (boxIoo_subset le_rfl
          ((shellT_antitone hq hq1 ht).antitone (Nat.le_add_right k l)))
    _ = _ := by
        rw [volume_boxIoo_of_nonneg (shellT_pos hq ht k).le, sub_zero]

/-- **Density one from shell estimates** (blueprint `bpW:w7:density`): the frozen clause (1) of
`KAM.Wave.nlw2`, in `ℝ≥0∞`. -/
theorem density_one_of_shells {q t0 : ℝ} (hq : 0 < q) (hq1 : q < 1) (ht : 0 < t0)
    {Γ : Set (Fin 2 → ℝ)} (hΓ : MeasurableSet Γ) (hΓP : Γ ⊆ {I | ∀ i, 0 < I i})
    (hε : Tendsto (fun k => volume (shellSet q t0 k \ Γ) / volume (shellSet q t0 k)) atTop (𝓝 0)) :
    Tendsto (fun h : ℝ => volume (Γ ∩ Metric.ball 0 h) /
      volume ({I : Fin 2 → ℝ | ∀ i, 0 < I i} ∩ Metric.ball 0 h)) (𝓝[>] 0) (𝓝 1) := by
  have hden : ∀ h : ℝ, 0 < h → volume ({I : Fin 2 → ℝ | ∀ i, 0 < I i} ∩ Metric.ball 0 h) =
      ENNReal.ofReal (h ^ 2) := fun h hh => by
    rw [posQuadrant_inter_ball hh, volume_boxIoo_of_nonneg hh.le, sub_zero]
  have hbox : ∀ h : ℝ, 0 < h → ENNReal.ofReal (h ^ 2) = volume (boxIoo 0 h) := fun h hh => by
    rw [volume_boxIoo_of_nonneg hh.le, sub_zero]
  have hnum : ∀ h : ℝ, 0 < h → Γ ∩ Metric.ball 0 h = Γ ∩ boxIoo 0 h := fun h hh => by
    rw [← posQuadrant_inter_ball hh]
    ext I
    simp only [mem_inter_iff]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, hΓP h1, h2⟩
    · rintro ⟨h1, _, h2⟩; exact ⟨h1, h2⟩
  have hup : ∀ h : ℝ, 0 < h → volume (Γ ∩ Metric.ball 0 h) /
      volume ({I : Fin 2 → ℝ | ∀ i, 0 < I i} ∩ Metric.ball 0 h) ≤ 1 := fun h hh => by
    rw [hden h hh, hnum h hh, hbox h hh]
    apply ENNReal.div_le_of_le_mul
    rw [one_mul]
    exact measure_mono inter_subset_right
  have hShellPos : ∀ l : ℕ, volume (shellSet q t0 l) ≠ 0 := fun l => by
    rw [volume_shellSet hq hq1 ht]
    refine (ENNReal.ofReal_pos.2 ?_).ne'
    have hq2 : q ^ 2 < 1 := by nlinarith
    exact mul_pos (sub_pos.2 hq2) (pow_pos (shellT_pos hq ht l) 2)
  have hShellTop : ∀ l : ℕ, volume (shellSet q t0 l) ≠ ⊤ := fun l => by
    rw [volume_shellSet hq hq1 ht]; exact ENNReal.ofReal_ne_top
  refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
  · have hatop : a ≠ ⊤ := ne_top_of_lt ha
    set a' := a.toReal with ha'
    have ha1 : a' < 1 := by
      have := (ENNReal.toReal_lt_toReal hatop ENNReal.one_ne_top).2 ha
      simpa using this
    have ha0 : 0 ≤ a' := ENNReal.toReal_nonneg
    set ε : ℝ := (1 - a') / 2 with hε0
    have hεpos : 0 < ε := by rw [hε0]; linarith
    have haε : a < ENNReal.ofReal (1 - ε) := by
      rw [← ENNReal.ofReal_toReal hatop]
      exact (ENNReal.ofReal_lt_ofReal_iff (by rw [hε0]; linarith)).2 (by rw [hε0]; linarith)
    have hpos : (0 : ℝ≥0∞) < ENNReal.ofReal (ε * q ^ 2) := ENNReal.ofReal_pos.2 (by positivity)
    obtain ⟨k0, hk0⟩ := (hε.eventually (gt_mem_nhds hpos)).exists_forall_of_atTop
    have hmem : Ioc 0 (shellT q t0 k0) ∈ 𝓝[>] (0 : ℝ) := Ioc_mem_nhdsGT (shellT_pos hq ht k0)
    filter_upwards [hmem] with h hh
    obtain ⟨k, hkk0, hk1, hk2⟩ := exists_shell_index hq hq1 ht hh.1 hh.2
    have hbd : ∀ l, k ≤ l → volume (shellSet q t0 l \ Γ) ≤
        ENNReal.ofReal (ε * q ^ 2) * volume (shellSet q t0 l) := fun l hl => by
      have h1 := hk0 l (hkk0.trans hl)
      have h2 : volume (shellSet q t0 l \ Γ) / volume (shellSet q t0 l) * volume (shellSet q t0 l) =
          volume (shellSet q t0 l \ Γ) := ENNReal.div_mul_cancel (hShellPos l) (hShellTop l)
      rw [← h2]
      exact mul_le_mul_of_nonneg_right h1.le (zero_le)
    have hdiffbox := volume_box_diff_le hq hq1 ht (ē := ε * q ^ 2) (k := k) hbd hk2
    have hqt : q ^ 2 * shellT q t0 k ^ 2 ≤ h ^ 2 := by
      have e := shellT_succ q t0 k
      have h1 := shellT_pos hq ht (k + 1)
      nlinarith
    have hdecomp := measure_inter_add_sdiff (boxIoo 0 h) hΓ
    have hh0 := hh.1
    have hV : ENNReal.ofReal (h ^ 2) ≤ volume (Γ ∩ Metric.ball 0 h) +
        ENNReal.ofReal (ε * h ^ 2) := by
      calc ENNReal.ofReal (h ^ 2) = volume (boxIoo 0 h) := by
            rw [volume_boxIoo_of_nonneg hh0.le, sub_zero]
        _ = volume (boxIoo 0 h ∩ Γ) + volume (boxIoo 0 h \ Γ) := hdecomp.symm
        _ ≤ volume (Γ ∩ Metric.ball 0 h) +
            ENNReal.ofReal (ε * q ^ 2) * ENNReal.ofReal (shellT q t0 k ^ 2) := by
            rw [hnum h hh0, inter_comm]
            gcongr
        _ = volume (Γ ∩ Metric.ball 0 h) + ENNReal.ofReal (ε * q ^ 2 * shellT q t0 k ^ 2) := by
            rw [← ENNReal.ofReal_mul (by positivity)]
        _ ≤ _ := by
            gcongr
            nlinarith [hqt, hεpos]
    refine lt_of_lt_of_le haε ?_
    rw [hden h hh0, ENNReal.le_div_iff_mul_le (Or.inl (ENNReal.ofReal_pos.2 (by positivity)).ne')
      (Or.inl ENNReal.ofReal_ne_top), ← ENNReal.ofReal_mul' (sq_nonneg h)]
    have e : (1 - ε) * h ^ 2 = h ^ 2 - ε * h ^ 2 := by ring
    rw [e, ENNReal.ofReal_sub _ (by positivity)]
    exact tsub_le_iff_right.2 hV
  · exact eventually_nhdsWithin_of_forall fun h hh => (hup h hh).trans_lt ha

end KAM.Wave
