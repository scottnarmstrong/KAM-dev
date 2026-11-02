/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.StrongAMD.Nek.Cover
public import KAM.Planetary.Spatial.AnalyticDomain.Containment
public import KAM.Planetary.Spatial.AnalyticDomain.Extension

/-!
# The spatial finite sharp cover of the action set

Source: `LP:MAIN L8 (244–271)`, `LP:MAIN L14 (468–500)` and
`LP:MAIN L18 (595–597)` as planned in `docs/tracks/LP/lp3/LP3-PLAN.md` §2.3, §2.5 (`k = n + n`
slow pairs, `Phase (n + (n + n))`), track LP, non-frozen.

The fast data are the planar ones verbatim and are reused, not duplicated, from
`KAM.Planetary.StrongAMD.Nek.Cover` (they involve only the action space `Fin n → ℝ`): the widths
`nekWidth`, `nekEta`, `nekRho`, the cells `nekCellInner` (`G_j`), `nekCellOuter` (`G′_j`), the level
`nekCellLevel`, the cover `IsNekCover`/`exists_isNekCover`, the collar `nekCell_collar`, the fast
erosion `IsNekCover.mem_innerCore` and the threshold bound `nekCell_threshold_bound`. New here:

* `spatialNekCellSlow`: `D_j = slowBall (n + n) (B(c_j) − 5δ/16)`, an open set of `Phase (n + n)`;
* `spatialNekCell_containment`: `partialComplexDomain G′_j D_j ρ ⊆
  complexTubeNM (spatialStrongCore) (R/2)`, the tube of `exists_spatialStrongTube`;
* `exists_spatialNekSlowGap`: the slow erosion gap for `2n` slow pairs, with constant
  `√(2 · (n + n))`, the hypothesis of `stopped_slow_erosion` at `n + n`.
-/

@[expose] public noncomputable section

namespace KAM.Planetary.Spatial

open KAM.Planetary KAM.Planetary.StrongAMD Set Metric

variable {n : ℕ}

/-! ### The slow cell `D_j` -/

/-- `D_j = {y ∈ Phase (n + n) : ∑_{k < 2n} (y₁² + y₂²)/2 < A_j}` with the local sharp slow level
`A_j = B(c_j) − 5δ/16` (`nekCellLevel`). -/
def spatialNekCellSlow (ν : Fin n → ℝ) (δ : ℝ) (c : Fin n → ℝ) : Set (Phase (n + n)) :=
  slowBall (n + n) (nekCellLevel ν δ c)

theorem isOpen_spatialNekCellSlow (ν : Fin n → ℝ) (δ : ℝ) (c : Fin n → ℝ) :
    IsOpen (spatialNekCellSlow ν δ c) :=
  isOpen_slowBall (n + n) _

/-! ### Containment -/

/-- The cell's complex domain lies in the `R/2`-tube of the spatial sharp core
(`spatialStrongCore_containment` with centre `c_j`, `s = b = η`). -/
theorem spatialNekCell_containment {ν : Fin n → ℝ} {L : Set (Fin n → ℝ)} {δ rg R : ℝ}
    (hrg : 0 < rg) (hR : 0 < R) (hδ : 0 < δ) {c : Fin n → ℝ} (hc : c ∈ strongLevelSet ν L δ) :
    KAM.Nekhoroshev.partialComplexDomain (nekCellOuter rg R c) (spatialNekCellSlow ν δ c)
        (nekRho rg R) ⊆ complexTubeNM (spatialStrongCore ν L δ rg) (R / 2) := by
  intro z hz
  obtain ⟨hf, hs, hz1, hz2⟩ := hz
  have hrs := nekWidth_pos hrg hR
  have h4 := four_mul_nekEta rg R
  have hρη := nekRho_le_eta hrg hR
  have hρpos := nekRho_pos hrg hR
  have hηpos := nekEta_pos hrg hR
  have hρ4 : nekRho rg R ≤ 4 * nekEta rg R := by linarith
  refine spatialStrongCore_containment (s := nekEta rg R) (b := nekEta rg R)
    (rs := nekWidth rg R) hrs (nekWidth_le_four_mul rg R) ?_ hc ?_ ?_ ?_
  · rw [h4, max_self, max_self]
    exact nekWidth_lt_half hR
  · rw [pi_norm_lt_iff hrs]
    intro i
    have hf' : ‖fast (fun j => (z.2 j).re) - c‖ < 2 * nekEta rg R := by
      have := hf
      rwa [nekCellOuter, mem_ball, dist_eq_norm] at this
    have h1 : |(z.2 (Fin.castAdd (n + n) i)).re - c i| < 2 * nekEta rg R := by
      have := norm_le_pi_norm (fast (fun j => (z.2 j).re) - c) i
      simp only [Pi.sub_apply, Real.norm_eq_abs, fast] at this
      exact lt_of_le_of_lt this hf'
    have h3 : |(z.2 (Fin.castAdd (n + n) i)).im| < nekRho rg R := hz2 _
    have h5 := Complex.norm_le_abs_re_add_abs_im (z.2 (Fin.castAdd (n + n) i) - ((c i : ℝ) : ℂ))
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im,
      sub_zero] at h5
    simp only [Pi.sub_apply]
    linarith
  · rw [h4, pi_norm_lt_iff hrs]
    intro i
    have h3 : |(z.1 (Fin.castAdd (n + n) i)).im| < nekRho rg R := hz1 _
    rw [Real.norm_eq_abs]
    linarith
  · refine ⟨(slow fun i => (z.1 i).re, slow fun i => (z.2 i).re), ?_, ?_, ?_⟩
    · have := hs
      simp only [spatialNekCellSlow, slowBall, mem_ofPred_eq] at this
      have hle := nekCell_level_le ν hδ c
      simp only [spatialSecularBall, mem_ofPred_eq]
      rw [← Finset.sum_div, Finset.sum_add_distrib] at this
      linarith
    · rw [h4, pi_norm_lt_iff hrs]
      intro i
      have h3 : |(z.1 (Fin.natAdd n i)).im| < nekRho rg R := hz1 _
      simp only [Pi.sub_apply, slow]
      rw [norm_sub_ofReal_re_eq]
      linarith
    · rw [h4, pi_norm_lt_iff hrs]
      intro i
      have h3 : |(z.2 (Fin.natAdd n i)).im| < nekRho rg R := hz2 _
      simp only [Pi.sub_apply, slow]
      rw [norm_sub_ofReal_re_eq]
      linarith

/-! ### The slow erosion gap (`2n` slow pairs) -/

/-- The per-cell gap `(√(2A_j) − √(2A′_j))/√(2·2n)` is positive (`A′_j = B(c_j) − 3δ/8`). -/
theorem spatialNekCell_slowGap_pos {ν : Fin n → ℝ} {L : Set (Fin n → ℝ)} {δ : ℝ}
    (hn : 2 ≤ n) (hδ : 0 < δ) {c : Fin n → ℝ} (hc : c ∈ strongLevelSet ν L δ) :
    0 < (Real.sqrt (2 * nekCellLevel ν δ c) - Real.sqrt (2 * (strongThreshold ν c - 3 * δ / 8))) /
      Real.sqrt (2 * ((n + n : ℕ) : ℝ)) := by
  have hB : δ ≤ strongThreshold ν c := hc.2
  have hn' : (0 : ℝ) < ((n + n : ℕ) : ℝ) := by
    have : 0 < n + n := by omega
    exact_mod_cast this
  refine div_pos (sub_pos.2 (Real.sqrt_lt_sqrt ?_ ?_)) (Real.sqrt_pos.2 (by positivity))
  · linarith
  · unfold nekCellLevel
    linarith

/-- `ε_D > 0`, uniform over a finite set of cells: for `ε < ε_D`,
`√(2A′_j) + √(2·2n) ε < √(2A_j)` for every centre `c_j ∈ s` (the hypothesis of
`stopped_slow_erosion` with `n + n` slow pairs). -/
theorem exists_spatialNekSlowGap {ν : Fin n → ℝ} {L : Set (Fin n → ℝ)} {δ : ℝ} (hn : 2 ≤ n)
    (hδ : 0 < δ) (s : Finset (Fin n → ℝ)) (hs : ∀ c ∈ s, c ∈ strongLevelSet ν L δ) :
    ∃ εD : ℝ, 0 < εD ∧ ∀ c ∈ s, ∀ ε : ℝ, 0 ≤ ε → ε < εD →
      Real.sqrt (2 * (strongThreshold ν c - 3 * δ / 8)) +
          Real.sqrt (2 * ((n + n : ℕ) : ℝ)) * ε <
        Real.sqrt (2 * nekCellLevel ν δ c) := by
  classical
  have hn' : (0 : ℝ) < ((n + n : ℕ) : ℝ) := by
    have : 0 < n + n := by omega
    exact_mod_cast this
  have hsq : 0 < Real.sqrt (2 * ((n + n : ℕ) : ℝ)) := Real.sqrt_pos.2 (by positivity)
  set f : (Fin n → ℝ) → ℝ := fun c =>
    (Real.sqrt (2 * nekCellLevel ν δ c) - Real.sqrt (2 * (strongThreshold ν c - 3 * δ / 8))) /
      Real.sqrt (2 * ((n + n : ℕ) : ℝ)) with hf
  have key : ∃ εD : ℝ, 0 < εD ∧ ∀ c ∈ s, εD ≤ f c := by
    rcases s.eq_empty_or_nonempty with h | h
    · exact ⟨1, one_pos, by simp [h]⟩
    · refine ⟨s.inf' h f,
        (Finset.lt_inf'_iff h).2 fun c hc => spatialNekCell_slowGap_pos hn hδ (hs c hc),
        fun c hc => Finset.inf'_le _ hc⟩
  obtain ⟨εD, hεD, hle⟩ := key
  refine ⟨εD, hεD, fun c hc ε hε0 hεlt => ?_⟩
  have h1 := hle c hc
  have h2 : ε < f c := lt_of_lt_of_le hεlt h1
  rw [hf] at h2
  simp only at h2
  rw [lt_div_iff₀ hsq] at h2
  linarith

end KAM.Planetary.Spatial

end
