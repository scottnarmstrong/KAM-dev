/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import KAM.Measure.Slab

/-!
# P Part 4: affine slabs with real normal and offset (`bpP:p4:affine-slab`)

`affine_slab`: for `ell ≠ 0` in `ℝⁿ`, the set of `x ∈ [-λ, λ]ⁿ` with `|ell · x + c| < ε` has
Lebesgue measure at most `2 ε (2λ)^(n-1) / ‖ell‖` (max norm). The proof takes a coordinate `i`
with `|ell i| = ‖ell‖`, splits `ℝⁿ = ℝ × ℝⁿ⁻¹` along `i` (Fubini) and bounds each section by
`KAM.Measure.volume_abs_affine_lt_le`. Design `docs/tracks/P/design/P45-LEAN-DESIGN.md`,
package P4-AF.
-/

public section

open Set Metric MeasureTheory

namespace KAM.Planetary

variable {n : ℕ}

/-- Fubini in a coordinate with nonzero normal entry. -/
theorem affine_slab_of_coord (ell : Fin (n + 1) → ℝ) (i : Fin (n + 1)) (hi : ell i ≠ 0)
    (c lambda eps : ℝ) :
    volume {x : Fin (n + 1) → ℝ | (∀ j, x j ∈ Icc (-lambda) lambda) ∧
        |∑ j, ell j * x j + c| < eps} ≤
      ENNReal.ofReal (2 * lambda) ^ n * ENNReal.ofReal (2 * eps / |ell i|) := by
  set S : Set (Fin (n + 1) → ℝ) := {x | (∀ j, x j ∈ Icc (-lambda) lambda) ∧
    |∑ j, ell j * x j + c| < eps} with hS
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i with he
  have hmp : MeasurePreserving e.symm :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i).symm
  have hSm : MeasurableSet S := by
    have hopen : IsOpen {x : Fin (n + 1) → ℝ | |∑ j, ell j * x j + c| < eps} :=
      isOpen_lt (by fun_prop) continuous_const
    have : MeasurableSet {x : Fin (n + 1) → ℝ | ∀ j, x j ∈ Icc (-lambda) lambda} := by
      have h := KAM.Measure.measurableSet_cube (n + 1) lambda
      convert h using 1
      ext x
      simp [KAM.Measure.cube, Pi.le_def, forall_and]
    exact this.inter hopen.measurableSet
  have hT : MeasurableSet (e.symm ⁻¹' S) := e.symm.measurable hSm
  have h1 : volume S = volume (e.symm ⁻¹' S) := (hmp.measure_preimage_equiv _).symm
  rw [h1, Measure.volume_eq_prod, Measure.prod_apply_symm hT]
  calc ∫⁻ y, volume ((fun x : ℝ => (x, y)) ⁻¹' (e.symm ⁻¹' S))
      ≤ ∫⁻ y, (KAM.Measure.cube n lambda).indicator
          (fun _ => ENNReal.ofReal (2 * eps / |ell i|)) y := by
        refine lintegral_mono fun y => ?_
        by_cases hy : y ∈ KAM.Measure.cube n lambda
        · rw [Set.indicator_of_mem hy]
          refine le_trans (measure_mono ?_)
            (KAM.Measure.volume_abs_affine_lt_le hi
              (∑ j, ell (i.succAbove j) * y j + c) eps)
          intro x hx
          have h2 : |∑ j, ell j * (Fin.insertNth i x y : Fin (n + 1) → ℝ) j + c| < eps := hx.2
          rw [Fin.sum_univ_succAbove _ i] at h2
          simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove] at h2
          show |ell i * x + (∑ j, ell (i.succAbove j) * y j + c)| < eps
          rw [show ell i * x + (∑ j, ell (i.succAbove j) * y j + c) =
            ell i * x + ∑ j, ell (i.succAbove j) * y j + c by ring]
          exact h2
        · rw [Set.indicator_of_notMem hy]
          refine le_of_eq_of_le (measure_mono_null ?_ measure_empty) le_rfl
          intro x hx
          refine hy ?_
          intro j _
          have := hx.1 (i.succAbove j)
          simpa [he, MeasurableEquiv.piFinSuccAbove_symm_apply] using this
    _ = ENNReal.ofReal (2 * eps / |ell i|) * volume (KAM.Measure.cube n lambda) :=
        lintegral_indicator_const (KAM.Measure.measurableSet_cube n lambda) _
    _ = ENNReal.ofReal (2 * lambda) ^ n * ENNReal.ofReal (2 * eps / |ell i|) := by
        rw [KAM.Measure.volume_cube, mul_comm]

/-- Real normals and arbitrary offset: the integer-normal K slab theorem alone is insufficient. -/
theorem affine_slab (hn : 0 < n) (ell : Fin n → ℝ) (hell : ell ≠ 0)
    (c lambda eps : ℝ) (hl : 0 < lambda) (he : 0 < eps) :
    volume {x : Fin n → ℝ | (∀ i, x i ∈ Icc (-lambda) lambda) ∧ |∑ i, ell i*x i+c| < eps} ≤
      ENNReal.ofReal (2*eps*(2*lambda)^(n-1)/‖ell‖) := by
  have _ := he
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ (fun j => ‖ell j‖)
    ⟨0, Finset.mem_univ _⟩
  have hnorm : ‖ell‖ = |ell i| := by
    refine le_antisymm ?_ ?_
    · refine (pi_norm_le_iff_of_nonneg (norm_nonneg (ell i))).mpr fun j => ?_
      exact hi j (Finset.mem_univ _)
    · exact norm_le_pi_norm ell i
  have hpos : 0 < ‖ell‖ := norm_pos_iff.mpr hell
  have hi0 : ell i ≠ 0 := by
    intro h; rw [hnorm, h] at hpos; simp at hpos
  refine le_trans (affine_slab_of_coord ell i hi0 c lambda eps) (le_of_eq ?_)
  rw [← ENNReal.ofReal_pow (by linarith), ← ENNReal.ofReal_mul (by positivity), hnorm]
  congr 1
  simp only [Nat.add_sub_cancel]
  ring

end KAM.Planetary
