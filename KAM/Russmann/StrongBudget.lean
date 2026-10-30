/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.Topology.MetricSpace.Thickening

/-!
# Track R: the measure budget of the strong form

* `exists_compact_open_budget`: for `B ⊆ ℝⁿ` open, bounded, nonempty and `η > 0`, a compact
  `K ⊆ B` with `meas K > (1 - η) meas B`, a margin `m > 0` inside `B`, an open `U` with
  `K ⊆ U ⊆ B` and `meas (U ∖ K) ≤ η meas B`, and a loss `0 < ε* ≤ η meas B` with `ε* < meas K`.
* `strong_volume_arith`: the closing inequality
  `meas B ≤ meas F + (3 + 2L) η meas B` from the near-full image estimate.
-/

@[expose] public section

open MeasureTheory Set Metric

namespace KAM.Russmann

variable {n : ℕ}

/-- **The compact and open parameter sets of the strong form.** -/
theorem exists_compact_open_budget {B : Set (Fin n → ℝ)} (hB : IsOpen B)
    (hBb : Bornology.IsBounded B) (hBne : B.Nonempty) {η : ℝ} (hη : 0 < η) :
    ∃ K : Set (Fin n → ℝ), IsCompact K ∧ K ⊆ B ∧
      ENNReal.ofReal ((1 - η) * (volume B).toReal) < volume K ∧
      (∃ m : ℝ, 0 < m ∧ ∀ b ∈ K, ∀ y : Fin n → ℝ, ‖y - b‖ < m → y ∈ B) ∧
      (∃ U : Set (Fin n → ℝ), IsOpen U ∧ K ⊆ U ∧ U ⊆ B ∧
        volume (U \ K) ≤ ENNReal.ofReal (η * (volume B).toReal)) ∧
      ∃ εs : ℝ, 0 < εs ∧ εs ≤ η * (volume B).toReal ∧ ENNReal.ofReal εs < volume K := by
  have hfin : volume B ≠ ⊤ := hBb.measure_lt_top.ne
  have hpos : 0 < volume B := hB.measure_pos volume hBne
  set V := (volume B).toReal with hV
  have hV0 : 0 < V := ENNReal.toReal_pos hpos.ne' hfin
  have ha : ENNReal.ofReal ((1 - η) * V) < volume B := by
    rw [← ENNReal.ofReal_toReal hfin]
    exact (ENNReal.ofReal_lt_ofReal_iff hV0).2 (by nlinarith)
  obtain ⟨K, hKB, hK, hKa⟩ := hB.exists_lt_isCompact ha
  have hKfin : volume K ≠ ⊤ := (measure_mono hKB).trans_lt hBb.measure_lt_top |>.ne
  have hKpos : 0 < volume K := lt_of_le_of_lt zero_le hKa
  obtain ⟨m, hm, hthick⟩ := hK.exists_thickening_subset_open hB hKB
  obtain ⟨U₀, hKU₀, hU₀, hU₀v⟩ := Set.exists_isOpen_lt_of_lt K
    (volume K + ENNReal.ofReal (η * V)) (ENNReal.lt_add_right hKfin
      (ENNReal.ofReal_pos.2 (by positivity)).ne')
  refine ⟨K, hK, hKB, hKa, ⟨m, hm, fun b hb y hy => hthick
    (mem_thickening_iff.2 ⟨b, hb, by rwa [dist_eq_norm]⟩)⟩,
    ⟨U₀ ∩ B, hU₀.inter hB, subset_inter hKU₀ hKB, inter_subset_right, ?_⟩, ?_⟩
  · calc volume ((U₀ ∩ B) \ K) ≤ volume (U₀ \ K) := measure_mono (sdiff_subset_sdiff_left
          inter_subset_left)
      _ = volume U₀ - volume K := measure_sdiff hKU₀ hK.measurableSet.nullMeasurableSet hKfin
      _ ≤ ENNReal.ofReal (η * V) := tsub_le_iff_left.2 hU₀v.le
  · set k := (volume K).toReal with hk
    have hk0 : 0 < k := ENNReal.toReal_pos hKpos.ne' hKfin
    refine ⟨min (η * V) (k / 2), lt_min (by positivity) (by positivity), min_le_left _ _, ?_⟩
    calc ENNReal.ofReal (min (η * V) (k / 2)) ≤ ENNReal.ofReal (k / 2) :=
          ENNReal.ofReal_le_ofReal (min_le_right _ _)
      _ < ENNReal.ofReal k := (ENNReal.ofReal_lt_ofReal_iff hk0).2 (by linarith)
      _ = volume K := ENNReal.ofReal_toReal hKfin

/-- **The closing inequality of the strong form.** If `ofReal((1 - 2η) V) ≤ X`,
`ofReal a · X ≤ Y + ofReal L · Z`, `Z ≤ ofReal (2ηV)`, `Y ≤ W`, with `a ≥ 1 - η`, `a ≥ 0`,
`L ≥ 0`, `V ≥ 0`, `η ≥ 0`, then `ofReal V ≤ W + ofReal ((3 + 2L) η V)`. -/
theorem strong_volume_arith {V η a L : ℝ} (hV : 0 ≤ V) (hη : 0 ≤ η) (ha0 : 0 ≤ a)
    (ha : 1 - η ≤ a) (hL : 0 ≤ L) {X Y Z W : ENNReal}
    (hX : ENNReal.ofReal ((1 - 2 * η) * V) ≤ X)
    (hmain : ENNReal.ofReal a * X ≤ Y + ENNReal.ofReal L * Z)
    (hZ : Z ≤ ENNReal.ofReal (2 * η * V)) (hY : Y ≤ W) :
    ENNReal.ofReal V ≤ W + ENNReal.ofReal ((3 + 2 * L) * η * V) := by
  have h1 : ENNReal.ofReal ((1 - 3 * η) * V) ≤ ENNReal.ofReal a * X := by
    by_cases h3 : 1 - 3 * η ≤ 0
    · rw [ENNReal.ofReal_of_nonpos (mul_nonpos_of_nonpos_of_nonneg h3 hV)]
      exact zero_le
    · replace h3 := not_le.1 h3
      refine le_trans ?_ (by gcongr : ENNReal.ofReal a * ENNReal.ofReal ((1 - 2 * η) * V) ≤
        ENNReal.ofReal a * X)
      rw [← ENNReal.ofReal_mul ha0]
      refine ENNReal.ofReal_le_ofReal ?_
      have h2 : 0 ≤ 1 - 2 * η := by linarith
      have : (1 - 3 * η) ≤ a * (1 - 2 * η) := by nlinarith
      nlinarith
  have h2 : ENNReal.ofReal L * Z ≤ ENNReal.ofReal (2 * L * η * V) := by
    calc ENNReal.ofReal L * Z ≤ ENNReal.ofReal L * ENNReal.ofReal (2 * η * V) := by gcongr
      _ = ENNReal.ofReal (2 * L * η * V) := by
        rw [← ENNReal.ofReal_mul hL]
        ring_nf
  calc ENNReal.ofReal V = ENNReal.ofReal ((1 - 3 * η) * V + 3 * η * V) := by ring_nf
    _ ≤ ENNReal.ofReal ((1 - 3 * η) * V) + ENNReal.ofReal (3 * η * V) := ENNReal.ofReal_add_le
    _ ≤ (W + ENNReal.ofReal (2 * L * η * V)) + ENNReal.ofReal (3 * η * V) := by
        gcongr
        exact h1.trans (hmain.trans (add_le_add hY h2))
    _ = W + (ENNReal.ofReal (2 * L * η * V) + ENNReal.ofReal (3 * η * V)) := by rw [add_assoc]
    _ = W + ENNReal.ofReal ((3 + 2 * L) * η * V) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        ring_nf

end KAM.Russmann

end
