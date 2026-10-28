/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.WeakKAM.CutoffBump

/-! # P11B finite extension: Euclidean/max norm conversion

The ambient norm on `Fin n → ℝ` is the max norm; `selectionLength` is the explicit Euclidean
length. This file converts between the two by explicit inequalities (never through a Euclidean
space), reduces operator norms of multilinear maps to the unit ball, and packages the real
inclusion `Fin n → ℝ → Fin n → ℂ` as a linear isometry.
-/

@[expose] public noncomputable section
open Set Real MeasureTheory Filter Function
open scoped BigOperators Topology
namespace KAM.Planetary
open KAM KAM.Kepler
variable {n μ : ℕ} {t C₁ : ℝ}

theorem selectionLength_le_sqrt_mul_norm (x : SelectionR n) :
    selectionLength x ≤ Real.sqrt n * ‖x‖ := by
  unfold selectionLength
  rw [← Real.sqrt_sq (norm_nonneg x), ← Real.sqrt_mul (Nat.cast_nonneg n)]
  refine Real.sqrt_le_sqrt ?_
  calc ∑ i, x i ^ 2 ≤ ∑ _i : Fin n, ‖x‖ ^ 2 := Finset.sum_le_sum fun i _ => by
        rw [← sq_abs (x i)]
        exact pow_le_pow_left₀ (abs_nonneg _) (by simpa using norm_le_pi_norm x i) 2
    _ = n * ‖x‖ ^ 2 := by simp

theorem abs_le_selectionLength (x : SelectionR n) (i : Fin n) : |x i| ≤ selectionLength x := by
  unfold selectionLength
  refine Real.abs_le_sqrt ?_
  exact Finset.single_le_sum (f := fun i => x i ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ i)

theorem norm_le_selectionLength (x : SelectionR n) : ‖x‖ ≤ selectionLength x := by
  refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i => ?_
  rw [Real.norm_eq_abs]
  exact abs_le_selectionLength x i

theorem norm_le_one_of_selectionLength_eq_one {a : SelectionR n} (ha : selectionLength a = 1) :
    ‖a‖ ≤ 1 := ha ▸ norm_le_selectionLength a

theorem selectionOpNorm_le_of_unit {k : ℕ} {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : ContinuousMultilinearMap ℝ (fun _ : Fin k => E) F) {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ b : Fin k → E, (∀ i, ‖b i‖ ≤ 1) → ‖f b‖ ≤ B) : ‖f‖ ≤ B := by
  refine ContinuousMultilinearMap.opNorm_le_bound hB fun b => ?_
  by_cases h0 : ∃ i, b i = 0
  · obtain ⟨i, hi⟩ := h0
    rw [f.map_coord_zero i hi, norm_zero]
    exact mul_nonneg hB (Finset.prod_nonneg fun _ _ => norm_nonneg _)
  · push Not at h0
    have hpos : ∀ i, 0 < ‖b i‖ := fun i => norm_pos_iff.2 (h0 i)
    set b' : Fin k → E := fun i => (‖b i‖)⁻¹ • b i with hb'
    have hb1 : ∀ i, ‖b' i‖ ≤ 1 := fun i => by
      simp [hb', norm_smul, (hpos i).ne']
    have hbb : b = fun i => ‖b i‖ • b' i := by
      funext i; simp [hb', smul_smul, (hpos i).ne']
    have : f b = (∏ i, ‖b i‖) • f b' := by
      conv_lhs => rw [hbb]
      exact f.map_smul_univ _ _
    rw [this, norm_smul, Real.norm_of_nonneg (Finset.prod_nonneg fun _ _ => norm_nonneg _),
      mul_comm]
    exact mul_le_mul_of_nonneg_right (h b' hb1) (Finset.prod_nonneg fun _ _ => norm_nonneg _)

theorem norm_selectionReal (x : SelectionR n) : ‖selectionReal x‖ = ‖x‖ := by
  refine le_antisymm ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_)
    ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_)
  · simpa [selectionReal] using norm_le_pi_norm x i
  · have := norm_le_pi_norm (selectionReal x) i
    simpa [selectionReal] using this

/-- The real inclusion `ℝⁿ → ℂⁿ` as a linear isometry for the max norms. -/
def selectionRealLI (n : ℕ) : SelectionR n →ₗᵢ[ℝ] SelectionC n where
  toFun := selectionReal
  map_add' x y := by funext i; simp [selectionReal]
  map_smul' c x := by funext i; simp [selectionReal]
  norm_map' := norm_selectionReal

theorem selectionRealLI_apply (x : SelectionR n) : selectionRealLI n x = selectionReal x := rfl

theorem norm_selectionRealLI_clm_le (n : ℕ) :
    ‖(selectionRealLI n).toContinuousLinearMap‖ ≤ 1 :=
  (selectionRealLI n).norm_toContinuousLinearMap_le

end KAM.Planetary
