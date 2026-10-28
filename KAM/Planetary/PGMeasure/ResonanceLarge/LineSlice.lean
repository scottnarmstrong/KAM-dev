/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import KAM.Planetary.PGMeasure.Tonelli

/-!
# P Part 4: sets with short sections along a coordinate line (`bpP:p4:ext-tonelli`, coordinate form)

`volume_le_of_line_diam`: a measurable subset `R` of a box in `ℝᴺ` all of whose lines in direction
`e_i` meet `R` in a set of diameter at most `δ` has volume at most `δ ∏_{l ≠ i} 2 ρ_l`. Tonelli
over the coordinate split `piFinSuccAbove`, with `section_measure_le_of_pairwise_dist` for the
sections. Design `docs/tracks/P/design/P45-LEAN-DESIGN.md`, package P4-RB.
-/

public section

open Set MeasureTheory

namespace KAM.Planetary

theorem volume_le_of_line_diam {N : ℕ} (i : Fin N) (rho : Fin N → ℝ) (hrho : ∀ l, 0 ≤ rho l)
    {R : Set (Fin N → ℝ)} (hR : MeasurableSet R) (hbox : ∀ x ∈ R, ∀ l, |x l| ≤ rho l)
    {delta : ℝ} (hd : 0 ≤ delta)
    (hline : ∀ x ∈ R, ∀ x' ∈ R, (∀ l, l ≠ i → x l = x' l) → |x i - x' i| ≤ delta) :
    volume R ≤ ENNReal.ofReal delta * ENNReal.ofReal (∏ l ∈ Finset.univ.erase i, 2 * rho l) := by
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by have := i.pos; omega⟩
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) i with he
  have hmp : MeasurePreserving e.symm :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) i).symm
  have hT : MeasurableSet (e.symm ⁻¹' R) := e.symm.measurable hR
  set P : Set (Fin m → ℝ) := Set.pi univ fun l => Icc (-rho (i.succAbove l)) (rho (i.succAbove l))
    with hP
  have hPm : MeasurableSet P := MeasurableSet.univ_pi fun _ => measurableSet_Icc
  have hprod : ∏ l ∈ Finset.univ.erase i, 2 * rho l = ∏ l : Fin m, 2 * rho (i.succAbove l) := by
    have h1 : Finset.univ.erase i = Finset.univ.image i.succAbove := by
      rw [Fin.image_succAbove_univ]; ext x; simp
    rw [h1, Finset.prod_image (fun x _ y _ h => i.succAbove_right_injective h)]
  have hPvol : volume P = ENNReal.ofReal (∏ l ∈ Finset.univ.erase i, 2 * rho l) := by
    rw [hP, Set.pi_univ_Icc, Real.volume_Icc_pi, hprod,
      ENNReal.ofReal_prod_of_nonneg (fun l _ => by linarith [hrho (i.succAbove l)])]
    refine Finset.prod_congr rfl fun l _ => ?_
    congr 1; ring
  have h1 : volume R = volume (e.symm ⁻¹' R) := (hmp.measure_preimage_equiv _).symm
  rw [h1, Measure.volume_eq_prod, Measure.prod_apply_symm hT]
  calc ∫⁻ y, volume ((fun x : ℝ => (x, y)) ⁻¹' (e.symm ⁻¹' R))
      ≤ ∫⁻ y, P.indicator (fun _ => ENNReal.ofReal delta) y := by
        refine lintegral_mono fun y => ?_
        by_cases hy : y ∈ P
        · rw [Set.indicator_of_mem hy]
          refine section_measure_le_of_pairwise_dist hd fun x hx x' hx' => ?_
          rw [Real.dist_eq]
          have key := hline _ hx _ hx' fun l hl => by
            obtain ⟨l', rfl⟩ := Fin.exists_succAbove_eq hl
            simp [he, MeasurableEquiv.piFinSuccAbove_symm_apply]
          simpa [he, MeasurableEquiv.piFinSuccAbove_symm_apply] using key
        · rw [Set.indicator_of_notMem hy]
          refine le_of_eq_of_le (measure_mono_null ?_ measure_empty) le_rfl
          intro x hx
          refine hy ?_
          intro j _
          have := hbox _ hx (i.succAbove j)
          have h2 : |y j| ≤ rho (i.succAbove j) := by
            simpa [he, MeasurableEquiv.piFinSuccAbove_symm_apply] using this
          obtain ⟨h3, h4⟩ := abs_le.mp h2
          exact ⟨h3, h4⟩
    _ = ENNReal.ofReal delta * volume P := by
        rw [lintegral_indicator hPm]; simp
    _ = _ := by rw [hPvol]

end KAM.Planetary
