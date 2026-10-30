/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.Topology.MetricSpace.Thickening
public import KAM.Frozen.Defs.FundamentalDomain

/-!
# Track R: the compact parameter set and the measure budget

`exists_compact_budget`: for a bounded open nonempty `B ⊆ ℝⁿ` and `0 ≤ θ < 1` there are a compact
`K ⊆ B`, a margin `m > 0` (every point within `m` of `K` lies in `B`) and a measure loss `ε* > 0`
with `ε* < meas K`, such that every set `G` with `meas K ≤ meas G + ε*` has `meas G ≥ θ meas B`.
This is the choice of `(K, ε*)` in track P's data `QuantitativeData` made inside R-HEAD's proof.
`volume_fundamentalDomain`: `meas([0,1)ⁿ × B) = meas B`.
-/

@[expose] public section

open MeasureTheory Set Metric

namespace KAM.Russmann

variable {n : ℕ}

theorem volume_fundamentalDomain (B : Set (Fin n → ℝ)) :
    volume (fundamentalDomain B) = volume B := by
  rw [fundamentalDomain, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_pi_Ico]
  simp

/-- **The compact parameter set.** For `B ⊆ ℝⁿ` open, bounded and nonempty and `0 ≤ θ < 1`, there
are a compact `K ⊆ B` with a margin `m > 0` inside `B` and a loss `ε* > 0` with `ε* < meas K`, such
that `meas K ≤ meas G + ε*` implies `θ · meas B ≤ meas G`. -/
theorem exists_compact_budget {B : Set (Fin n → ℝ)} (hB : IsOpen B)
    (hBb : Bornology.IsBounded B) (hBne : B.Nonempty) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) :
    ∃ K : Set (Fin n → ℝ), IsCompact K ∧ K ⊆ B ∧
      (∃ m : ℝ, 0 < m ∧ ∀ b ∈ K, ∀ y : Fin n → ℝ, ‖y - b‖ < m → y ∈ B) ∧
      ∃ εs : ℝ, 0 < εs ∧ ENNReal.ofReal εs < volume K ∧
        ∀ G : Set (Fin n → ℝ), volume K ≤ volume G + ENNReal.ofReal εs →
          ENNReal.ofReal (θ * (volume B).toReal) ≤ volume G := by
  have hfin : volume B ≠ ⊤ := hBb.measure_lt_top.ne
  have hpos : 0 < volume B := hB.measure_pos volume hBne
  set V := (volume B).toReal with hV
  have hV0 : 0 < V := ENNReal.toReal_pos hpos.ne' hfin
  have hVeq : volume B = ENNReal.ofReal V := (ENNReal.ofReal_toReal hfin).symm
  have ha : ENNReal.ofReal ((1 + θ) / 2 * V) < volume B := by
    rw [hVeq]
    exact (ENNReal.ofReal_lt_ofReal_iff hV0).2 (by nlinarith)
  obtain ⟨K, hKB, hK, hKa⟩ := hB.exists_lt_isCompact ha
  obtain ⟨m, hm, hthick⟩ := hK.exists_thickening_subset_open hB hKB
  refine ⟨K, hK, hKB, ⟨m, hm, fun b hb y hy => hthick ?_⟩, (1 - θ) * V / 4, by
    have : 0 < 1 - θ := by linarith
    positivity, ?_, fun G hG => ?_⟩
  · exact mem_thickening_iff.2 ⟨b, hb, by rwa [dist_eq_norm]⟩
  · refine lt_of_le_of_lt (ENNReal.ofReal_le_ofReal ?_) hKa
    nlinarith
  · have h1 : ENNReal.ofReal ((1 + θ) / 2 * V) - ENNReal.ofReal ((1 - θ) * V / 4) ≤ volume G :=
      tsub_le_iff_right.2 (hKa.le.trans hG)
    have hnn : 0 ≤ (1 - θ) * V / 4 := by
      have : 0 ≤ 1 - θ := by linarith
      positivity
    rw [← ENNReal.ofReal_sub _ hnn] at h1
    refine le_trans (ENNReal.ofReal_le_ofReal ?_) h1
    nlinarith

end KAM.Russmann

end
