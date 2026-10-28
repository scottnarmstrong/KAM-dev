/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.SecularForm.ParameterIntegral

/-!
# Cross jet: second derivative of a two-angle average in two slow parameters

Blueprint P, Part 8, `stepP:p8:qf-cross` (via `bpP:p8:e-diff`): a jointly `C²` integrand on an open
neighbourhood of `cell 2 × {0}` can be differentiated twice under the angle integral at `0`.
This is the generic instance of `e_diff` (`n = d = 2`, `k = 2`) used for the pair average.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter Real Function Metric
open scoped Topology ContDiff
namespace KAM.Planetary
namespace SecularForm

/-- Partial `y`-derivatives of a jointly smooth function on an open set, in the form consumed by
`e_diff`. -/
theorem iteratedFDeriv_slice {W : Set (Vec 2 × Vec 2)} (hW : IsOpen W) {F : Vec 2 × Vec 2 → ℝ}
    (hF : ContDiffOn ℝ 2 F W) {t y : Vec 2} (hty : (t, y) ∈ W) (j : ℕ) (hj : j ≤ 2) :
    iteratedFDeriv ℝ j (fun y' => F (t, y')) y =
      (iteratedFDeriv ℝ j F (t, y)).compContinuousLinearMap
        fun _ => (ContinuousLinearMap.inr ℝ (Vec 2) (Vec 2)) := by
  set ι := ContinuousLinearMap.inr ℝ (Vec 2) (Vec 2) with hι
  set a : Vec 2 × Vec 2 := (t, 0) with ha
  set S : Set (Vec 2 × Vec 2) := (fun z => a + z) ⁻¹' W with hS
  have hSo : IsOpen S := hW.preimage (continuous_const.add continuous_id)
  have hFa : ContDiffOn ℝ 2 (fun z => F (a + z)) S :=
    hF.comp (contDiff_const.add contDiff_id).contDiffOn (fun z hz => hz)
  have hy : ι y ∈ S := by simpa [hS, ha, hι] using hty
  have h1 := ι.iteratedFDerivWithin_comp_right (f := fun z => F (a + z)) hFa hSo.uniqueDiffOn
    ((hSo.preimage ι.continuous).uniqueDiffOn) hy (i := j) (by exact_mod_cast hj)
  rw [iteratedFDerivWithin_of_isOpen _ hSo hy,
    iteratedFDerivWithin_of_isOpen _ (hSo.preimage ι.continuous) (by exact hy)] at h1
  have hfun : (fun y' => F (t, y')) = (fun z => F (a + z)) ∘ ι := by
    funext y'; simp [ha, hι]
  rw [hfun, h1, iteratedFDeriv_comp_add_left]
  simp [ha, hι]

/-- `e_diff` for a jointly `C²` integrand on an open neighbourhood of `cell 2 × {0}`. -/
theorem e_diff_slice {W : Set (Vec 2 × Vec 2)} (hW : IsOpen W) {F : Vec 2 × Vec 2 → ℝ}
    (hF : ContDiffOn ℝ 2 F W) (hK : ∀ t ∈ cell 2, (t, (0 : Vec 2)) ∈ W) :
    ∃ δ : ℝ, 0 < δ ∧ (∀ t ∈ cell 2, ∀ y ∈ ball (0 : Vec 2) δ, (t, y) ∈ W) ∧
      ContinuousOn (fun t => iteratedFDeriv ℝ 2 (fun y => F (t, y)) 0) (cell 2) ∧
      iteratedFDeriv ℝ 2 (fun y : Vec 2 => ∫ t in cell 2, F (t, y)) 0 =
        ∫ t in cell 2, iteratedFDeriv ℝ 2 (fun y => F (t, y)) 0 := by
  have hKc : IsCompact (cell 2 ×ˢ ({0} : Set (Vec 2))) := isCompact_cell.prod isCompact_singleton
  have hKW : cell 2 ×ˢ ({0} : Set (Vec 2)) ⊆ W := by
    rintro ⟨t, y⟩ ⟨ht, hy⟩
    rw [mem_singleton_iff] at hy
    subst hy
    exact hK t ht
  obtain ⟨δ, hδ, hthick⟩ := hKc.exists_thickening_subset_open hW hKW
  have hmem : ∀ t ∈ cell 2, ∀ y ∈ ball (0 : Vec 2) δ, (t, y) ∈ W := by
    intro t ht y hy
    apply hthick
    rw [mem_thickening_iff]
    refine ⟨(t, 0), ⟨ht, rfl⟩, ?_⟩
    rw [Prod.dist_eq]
    simp only [dist_self, dist_zero_right]
    exact max_lt hδ (by simpa using hy)
  have hcontj : ∀ j : ℕ, j ≤ 2 → ContinuousOn
      (fun z : Vec 2 × Vec 2 => iteratedFDeriv ℝ j (fun y => F (z.1, y)) z.2)
      (cell 2 ×ˢ ball (0 : Vec 2) δ) := by
    intro j hj
    have hcont : ContinuousOn (fun z : Vec 2 × Vec 2 => iteratedFDeriv ℝ j F z) W := by
      have := hF.continuousOn_iteratedFDerivWithin (m := j) (by exact_mod_cast hj) hW.uniqueDiffOn
      exact this.congr fun z hz => (iteratedFDerivWithin_of_isOpen j hW hz).symm
    have hL := (ContinuousMultilinearMap.compContinuousLinearMapL (𝕜 := ℝ) (F := ℝ)
      (fun _ : Fin j => ContinuousLinearMap.inr ℝ (Vec 2) (Vec 2))).continuous
    refine (hL.comp_continuousOn hcont).mono ?_ |>.congr ?_
    · rintro ⟨t, y⟩ ⟨ht, hy⟩
      exact hmem t ht y hy
    · rintro ⟨t, y⟩ ⟨ht, hy⟩
      exact iteratedFDeriv_slice hW hF (hmem t ht y hy) j hj
  refine ⟨δ, hδ, hmem, ?_, ?_⟩
  · have h2 := (hcontj 2 le_rfl).comp (continuous_id.prodMk continuous_const).continuousOn
      (fun t ht => ⟨ht, mem_ball_self hδ⟩)
    exact h2
  · refine e_diff (n := 2) (d := 2) isOpen_ball (f := fun t y => F (t, y)) 2 hcontj ?_
      (mem_ball_self hδ)
    intro t ht
    exact hF.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun y hy => hmem t ht y hy)

end SecularForm
end KAM.Planetary
