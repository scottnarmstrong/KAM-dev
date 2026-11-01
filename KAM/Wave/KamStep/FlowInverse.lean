/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.KamStep.FlowVariational
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Invertibility of the flow derivative (`bpW:w5:flow-calc` (iii), step `c-inv`)

Off-frontier, source-faithful infrastructure (W5-STEP); the dependency graph is still being built.

From the variational equation, `‖Dφ^t(w) - I‖ ≤ |t| L e^L` with `L = M/δ`
(`norm_fderiv_holoFlow_sub_id_le`);
for `L ≤ 1/64` this is `< 1/8`, so `Dφ^t(w)` is a unit of `F →L F` by the Neumann series
(`isUnit_fderiv_holoFlow`).
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory intervalIntegral Filter Topology
open scoped Interval

namespace KAM.Wave

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  {X : F → F} {V U : Set F} {M δ : ℝ} (h : FlowHyp X V U M δ)
include h

theorem norm_fderiv_holoFlow_sub_id_le {w : F} (hw : w ∈ U) {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    ‖fderiv ℂ (holoFlow X t) w - ContinuousLinearMap.id ℂ F‖ ≤
      |t| * (M / δ * Real.exp (M / δ)) := by
  rw [fderiv_holoFlow_eq h hw ht, add_sub_cancel_left]
  have e : |t| = |t - 0| := by rw [sub_zero]
  rw [mul_comm, e]
  refine intervalIntegral.norm_integral_le_of_norm_le_const fun σ hσ => ?_
  exact norm_flowVarG_le h hw (uIcc_subset_Icc' ht (uIoc_subset_uIcc hσ))

/-- `Dφ^t(w)` is invertible when `M/δ ≤ 1/64` (`bpW:w5:flow-calc` (iii)). -/
theorem isUnit_fderiv_holoFlow (hL : M / δ ≤ 1 / 64) {w : F} (hw : w ∈ U) {t : ℝ}
    (ht : t ∈ Icc (-1 : ℝ) 1) : IsUnit (fderiv ℂ (holoFlow X t) w) := by
  have hL0 : 0 ≤ M / δ := div_nonneg h.M_pos.le h.delta_pos.le
  have h1 := norm_fderiv_holoFlow_sub_id_le h hw ht
  have ht1 : |t| ≤ 1 := abs_le.mpr ⟨ht.1, ht.2⟩
  have he : Real.exp (M / δ) ≤ 3 := (Real.exp_le_exp.mpr (by linarith : M / δ ≤ 1)).trans
    Real.exp_one_lt_three.le
  have hlt : ‖ContinuousLinearMap.id ℂ F - fderiv ℂ (holoFlow X t) w‖ < 1 := by
    rw [norm_sub_rev]
    refine h1.trans_lt ?_
    have : M / δ * Real.exp (M / δ) ≤ 3 / 64 := by nlinarith [Real.exp_pos (M / δ)]
    nlinarith [abs_nonneg t]
  have := (Units.oneSub _ hlt).isUnit
  have e : (1 : F →L[ℂ] F) - (ContinuousLinearMap.id ℂ F - fderiv ℂ (holoFlow X t) w) =
      fderiv ℂ (holoFlow X t) w := by
    rw [← ContinuousLinearMap.one_def]; abel
  rw [Units.val_oneSub, e] at this
  exact this

end KAM.Wave
