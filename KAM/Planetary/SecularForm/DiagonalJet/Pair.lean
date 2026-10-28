/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.SecularForm.DiagonalJet.Orbit

/-!
# Secular form: the pair average with a circular partner

Blueprint P, Part 8, `stepP:p8:qf-c0` and `stepP:p8:qf-diag`: the literal pair average
`pairSlowSecular D i j I J (u, 0)` with the second planet circular equals
`-G mᵢ mⱼ ⟨radialH aᵢ aⱼ (v·e(F))⟩_F`, the average over the eccentric longitude `F` of the
`radialH` function evaluated at `ε = v·e(F)`, where `v` is the regular eccentricity vector of the
first planet. At `u = 0` this is `-G mᵢ mⱼ Φ(aᵢ, aⱼ)` (`qf-c0`).
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter Real Function
open scoped BigOperators Topology
namespace KAM.Planetary
open KAM KAM.Kepler

namespace SecularForm

variable {n : ℕ}

private theorem planeDot_two' (v w : Fin 2 → ℝ) : planeDot v w = v 0 * w 0 + v 1 * w 1 := by
  simp [planeDot, Fin.sum_univ_two]

theorem continuous_keplerJac (v : Fin 2 → ℝ) : Continuous (keplerJac v) := by
  unfold keplerJac
  have : Continuous fun F : ℝ => planeDot v (orbitalUnit F) := by
    simp only [planeDot_two', orbitalUnit, Matrix.cons_val_zero, Matrix.cons_val_one]
    fun_prop
  exact continuous_const.sub this

theorem periodic_keplerJac (v : Fin 2 → ℝ) : Function.Periodic (keplerJac v) (2 * π) := fun F => by
  simp [keplerJac, planeDot_two', orbitalUnit]

theorem keplerJac_le {v : Fin 2 → ℝ} (F : ℝ) : keplerJac v F ≤ 1 + planeLength v := by
  have h := abs_planeDot_le v (orbitalUnit F)
  have h1 : planeLength (orbitalUnit F) = 1 := by
    simp [orbitalUnit, planeLength, planeSq, Fin.sum_univ_two, Real.cos_sq_add_sin_sq]
  rw [h1, mul_one] at h
  unfold keplerJac
  linarith [(abs_le.1 h).1]

/-- The regular eccentricity vector does not depend on the mean longitude. -/
theorem poincareV_congr_fst (s t : ℝ) (u Λ η : ℝ) :
    poincareV (![s, u], ![Λ, η]) = poincareV (![t, u], ![Λ, η]) := by
  simp [poincareV, poincareGamma]

theorem mem_poincareDom_congr_fst (s t : ℝ) (u Λ η : ℝ)
    (h : (![s, u], ![Λ, η]) ∈ poincareDom) : (![t, u], ![Λ, η]) ∈ poincareDom := by
  simpa [poincareDom, poincareGamma] using h

/-- `stepP:p8:qf-diag`, inner average: averaging over the circular partner's longitude gives
`-G mᵢ mⱼ Φ(|qᵢ|, b)`. -/
theorem pair_inner_average (D : Data n) (i j : Fin n) (J : ℝ) (q : Fin 2 → ℝ) :
    (2 * π)⁻¹ * ∫ t in (0:ℝ)..2 * π, -D.G * D.m i * D.m j / planeLength
      (q - (poincare (D.m j) (D.G * D.m0) (![t, (0 : Fin 2 → ℝ) 0], ![J, (0 : Fin 2 → ℝ) 1])).1) =
    -D.G * D.m i * D.m j *
      radialPhi (planeLength q) (J ^ 2 / (D.m j ^ 2 * (D.G * D.m0))) := by
  have h : ∀ t : ℝ, -D.G * D.m i * D.m j / planeLength
      (q - (poincare (D.m j) (D.G * D.m0) (![t, (0 : Fin 2 → ℝ) 0], ![J, (0 : Fin 2 → ℝ) 1])).1) =
      -D.G * D.m i * D.m j * (planeLength
        (q - (J ^ 2 / (D.m j ^ 2 * (D.G * D.m0))) • orbitalUnit t))⁻¹ := fun t => by
    simp only [Pi.zero_apply, poincare_circular_fst, div_eq_mul_inv]
  simp only [h]
  rw [intervalIntegral.integral_const_mul, ← circle_average q]
  ring

/-- `stepP:p8:qf-diag`: the literal pair average with a circular second planet is
`-G mᵢ mⱼ ⟨radialH aᵢ aⱼ (v·e(F))⟩_F`, where `v` is the regular eccentricity vector of the first
planet, provided the radii `aᵢ J(F)` of the first orbit avoid the radius `aⱼ` of the second. -/
theorem pairSlowSecular_circular_partner (D : Data n) (i j : Fin n) {I J : ℝ} (hJ : 0 < J)
    (u : Fin 2 → ℝ) (hw : (![0, u 0], ![I, u 1]) ∈ poincareDom)
    (hsep : I ^ 2 / (D.m i ^ 2 * (D.G * D.m0)) *
          (1 + planeLength (poincareV (![0, u 0], ![I, u 1]))) <
        J ^ 2 / (D.m j ^ 2 * (D.G * D.m0)) ∨
      J ^ 2 / (D.m j ^ 2 * (D.G * D.m0)) <
        I ^ 2 / (D.m i ^ 2 * (D.G * D.m0)) *
          (1 - planeLength (poincareV (![0, u 0], ![I, u 1])))) :
    pairSlowSecular D i j I J (u, 0) =
      -D.G * D.m i * D.m j * ((2 * π)⁻¹ * ∫ F in (0:ℝ)..2 * π,
        radialH (I ^ 2 / (D.m i ^ 2 * (D.G * D.m0))) (J ^ 2 / (D.m j ^ 2 * (D.G * D.m0)))
          (planeDot (poincareV (![0, u 0], ![I, u 1])) (orbitalUnit F))) := by
  set v := poincareV (![0, u 0], ![I, u 1]) with hv
  set a := I ^ 2 / (D.m i ^ 2 * (D.G * D.m0)) with ha
  set b := J ^ 2 / (D.m j ^ 2 * (D.G * D.m0)) with hb
  have hκ : 0 < D.G * D.m0 := mul_pos D.hG D.hm0
  have hI : 0 < I := hw.1
  have ha0 : 0 < a := div_pos (pow_pos hI 2) (mul_pos (pow_pos (D.hm i) 2) hκ)
  have hb0 : 0 < b := div_pos (pow_pos hJ 2) (mul_pos (pow_pos (D.hm j) 2) hκ)
  have hlt : planeLength v < 1 := (poincare_facts hw).2.2.2.2.2.1
  have hrad : ∀ s : ℝ, planeLength (poincare (D.m i) (D.G * D.m0) (![s, u 0], ![I, u 1])).1 =
      a * keplerJac v (keplerLong s v) := fun s => by
    have hws : (![s, u 0], ![I, u 1]) ∈ poincareDom := mem_poincareDom_congr_fst 0 s _ _ _ hw
    rw [planeLength_poincare_fst (D.hm i) hκ hws]
    have e1 : poincareV (![s, u 0], ![I, u 1]) = v := poincareV_congr_fst s 0 _ _ _
    have e2 : poincareF (![s, u 0], ![I, u 1]) = keplerLong s v := by
      unfold poincareF; rw [e1]; rfl
    simp only [e1, e2, Matrix.cons_val_zero]
    rfl
  unfold pairSlowSecular
  have hstep : ∀ s : ℝ, (2 * π)⁻¹ * ∫ t in (0:ℝ)..2 * π, -D.G * D.m i * D.m j / planeLength
      ((poincare (D.m i) (D.G * D.m0) (![s, (u, (0 : Fin 2 → ℝ)).1 0], ![I, (u, (0 : Fin 2 → ℝ)).1 1])).1 -
        (poincare (D.m j) (D.G * D.m0)
          (![t, (u, (0 : Fin 2 → ℝ)).2 0], ![J, (u, (0 : Fin 2 → ℝ)).2 1])).1) =
      -D.G * D.m i * D.m j * radialPhi (a * keplerJac v (keplerLong s v)) b := fun s => by
    rw [pair_inner_average D i j J, hrad s]
  simp only [hstep]
  rw [intervalIntegral.integral_const_mul]
  have hmem : ∀ F : ℝ, (a * keplerJac v F, b) ∈
      {p : ℝ × ℝ | 0 < p.1 ∧ 0 < p.2 ∧ p.1 ≠ p.2} := fun F => by
    have hJpos := keplerJac_pos hlt F
    refine ⟨mul_pos ha0 hJpos, hb0, ?_⟩
    rcases hsep with h | h
    · exact (lt_of_le_of_lt (mul_le_mul_of_nonneg_left (keplerJac_le F) ha0.le) h).ne
    · exact (lt_of_lt_of_le h (mul_le_mul_of_nonneg_left (keplerJac_ge F) ha0.le)).ne'
  have hcont : Continuous fun F : ℝ => radialPhi (a * keplerJac v F) b := by
    refine continuous_iff_continuousAt.2 fun F => ?_
    have h1 := (analyticOnNhd_radialPhi _ (hmem F)).continuousAt
    have h2 : Continuous fun F : ℝ => (a * keplerJac v F, b) :=
      (continuous_const.mul (continuous_keplerJac v)).prodMk continuous_const
    exact h1.comp (f := fun F : ℝ => (a * keplerJac v F, b)) h2.continuousAt
  have hper : Function.Periodic (fun F : ℝ => radialPhi (a * keplerJac v F) b) (2 * π) :=
    fun F => by simp only; rw [periodic_keplerJac v F]
  rw [integral_keplerLong_comp hlt hcont hper]
  have : ∀ F : ℝ, radialPhi (a * keplerJac v F) b * keplerJac v F =
      radialH a b (planeDot v (orbitalUnit F)) := fun F => by
    unfold radialH keplerJac; rfl
  simp only [this]
  ring

/-- `stepP:p8:qf-c0`: at `u = 0` both planets are circular and
`S_ij(0) = -G mᵢ mⱼ Φ(aᵢ, aⱼ)` (for distinct axes). -/
theorem pairSlowSecular_zero (D : Data n) (i j : Fin n) {I J : ℝ} (hI : 0 < I) (hJ : 0 < J)
    (hab : I ^ 2 / (D.m i ^ 2 * (D.G * D.m0)) ≠ J ^ 2 / (D.m j ^ 2 * (D.G * D.m0))) :
    pairSlowSecular D i j I J (0, 0) =
      -D.G * D.m i * D.m j * radialPhi (I ^ 2 / (D.m i ^ 2 * (D.G * D.m0)))
        (J ^ 2 / (D.m j ^ 2 * (D.G * D.m0))) := by
  have hw : (![0, (0 : Fin 2 → ℝ) 0], ![I, (0 : Fin 2 → ℝ) 1]) ∈ poincareDom := by
    simp [poincareDom, poincareGamma, hI]
  have hv : poincareV (![0, (0 : Fin 2 → ℝ) 0], ![I, (0 : Fin 2 → ℝ) 1]) = 0 := by
    simp [poincareV]
  have hsep := hab
  rw [pairSlowSecular_circular_partner D i j hJ 0 hw (by
    rw [hv]
    simp only [planeLength, planeSq, Fin.sum_univ_two, Pi.zero_apply]
    simp only [ne_eq] at hsep
    rcases lt_or_gt_of_ne hab with h | h
    · left; simpa using h
    · right; simpa using h)]
  rw [hv]
  have : ∀ F : ℝ, planeDot (0 : Fin 2 → ℝ) (orbitalUnit F) = 0 := fun F => by
    simp [planeDot]
  simp only [this]
  have hrh : radialH (I ^ 2 / (D.m i ^ 2 * (D.G * D.m0))) (J ^ 2 / (D.m j ^ 2 * (D.G * D.m0))) 0 =
      radialPhi (I ^ 2 / (D.m i ^ 2 * (D.G * D.m0))) (J ^ 2 / (D.m j ^ 2 * (D.G * D.m0))) := by
    simp [radialH]
  rw [hrh, intervalIntegral.integral_const]
  have hπ : (2 * π) ≠ 0 := by positivity
  simp only [sub_zero, smul_eq_mul]
  field_simp

end SecularForm
end KAM.Planetary
end
