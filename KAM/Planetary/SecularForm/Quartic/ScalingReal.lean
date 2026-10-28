/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.SecularForm.Quartic.Defs
public import KAM.Planetary.SecularForm.Quartic.PairAverage
public import KAM.Planetary.SecularForm.DiagonalJet.Orbit
public import KAM.Planetary.SecularForm.DiagonalJet.Pair

/-!
# Secular form: the dimensionless pair average in the eccentric longitude

Blueprint P, Part 8, `stepP:p8:q4-a`, real part: the change of variables from the mean to the
eccentric longitudes turns `dimensionlessPair` into the cell average of an explicit integrand.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter Real Function
open scoped BigOperators Topology Matrix.Norms.Elementwise
namespace KAM.Planetary
open KAM KAM.Kepler

namespace SecularForm

/-- The regular orbit vector as a function of the eccentric longitude. -/
def qscU (v : Fin 2 → ℝ) (F : ℝ) : Fin 2 → ℝ :=
  √(1 - planeSq v) • orbitalUnit F - v +
    (planeDot v (orbitalUnit F) / (1 + √(1 - planeSq v))) • v

theorem qsc_unitPosition (t : ℝ) (v : Fin 2 → ℝ) : unitPosition t v = qscU v (keplerLong t v) :=
  rfl

theorem qsc_planeSq_two (v : Fin 2 → ℝ) : planeSq v = v 0 ^ 2 + v 1 ^ 2 := by
  simp [planeSq, Fin.sum_univ_two]

theorem qsc_planeDot_two (v w : Fin 2 → ℝ) : planeDot v w = v 0 * w 0 + v 1 * w 1 := by
  simp [planeDot, Fin.sum_univ_two]

theorem qsc_continuous_planeLength : Continuous planeLength := by
  have : planeLength = fun v : Fin 2 → ℝ => √(v 0 ^ 2 + v 1 ^ 2) := by
    funext v; rw [planeLength, qsc_planeSq_two]
  rw [this]; fun_prop

theorem qsc_continuous_qscU (v : Fin 2 → ℝ) : Continuous (qscU v) := by
  refine continuous_pi fun i => ?_
  fin_cases i <;>
  · simp only [qscU, qsc_planeDot_two, orbitalUnit, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.zero_eta, Fin.mk_one]
    fun_prop

theorem qsc_periodic_qscU (v : Fin 2 → ℝ) : Function.Periodic (qscU v) (2 * π) := fun F => by
  simp [qscU, qsc_planeDot_two, orbitalUnit]

theorem qsc_planeLength_qscU {v : Fin 2 → ℝ} (hv : planeLength v < 1) (F : ℝ) :
    planeLength (qscU v F) = keplerJac v F := by
  have hsq : planeSq v < 1 := by
    have := planeLength_sq v
    nlinarith [planeLength_nonneg v]
  have hK : 0 < √(1 - planeSq v) := Real.sqrt_pos.2 (by linarith)
  have hv' : planeSq v = 1 - (√(1 - planeSq v)) ^ 2 := by
    rw [Real.sq_sqrt (by linarith)]; ring
  have h := planeSq_orbit_vec (K := √(1 - planeSq v)) (v := v) F hv' hK
  unfold qscU planeLength
  rw [h]
  unfold keplerJac at *
  exact Real.sqrt_sq (keplerJac_pos hv F).le

theorem qsc_sep_lower {α : ℝ} {v₁ v₂ : Fin 2 → ℝ} (hα : 0 < α) (F₁ F₂ : ℝ) :
    planeLength (qscU v₂ F₂) - α * planeLength (qscU v₁ F₁) ≤
      planeLength (α • qscU v₁ F₁ - qscU v₂ F₂) := by
  have h := abs_planeLength_sub_le (qscU v₂ F₂) (α • qscU v₁ F₁)
  rw [planeLength_smul, abs_of_pos hα, planeLength_sub_comm] at h
  exact (le_abs_self _).trans h

theorem qsc_sep_pos {z : ℝ × (Fin 2 → ℝ) × (Fin 2 → ℝ)} (hz : z ∈ separatedDomain)
    (F₁ F₂ : ℝ) : 0 < planeLength (z.1 • qscU z.2.1 F₁ - qscU z.2.2 F₂) := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := hz
  have e1 : planeLength z.2.1 < 1 := by linarith
  have e2 : planeLength z.2.2 < 1 := by linarith
  have := qsc_sep_lower (α := z.1) (v₁ := z.2.1) (v₂ := z.2.2) h0 F₁ F₂
  rw [qsc_planeLength_qscU e1, qsc_planeLength_qscU e2] at this
  have a1 := keplerJac_le (v := z.2.1) F₁
  have a2 := keplerJac_ge (v := z.2.2) F₂
  nlinarith

/-- The integrand in the eccentric longitudes. -/
def qscG (z : ℝ × (Fin 2 → ℝ) × (Fin 2 → ℝ)) (s t : ℝ) : ℝ :=
  (planeLength (z.1 • qscU z.2.1 s - qscU z.2.2 t))⁻¹ * keplerJac z.2.1 s * keplerJac z.2.2 t

theorem qsc_continuous_sep (z : ℝ × (Fin 2 → ℝ) × (Fin 2 → ℝ)) :
    Continuous fun p : ℝ × ℝ => planeLength (z.1 • qscU z.2.1 p.1 - qscU z.2.2 p.2) := by
  have h1 := qsc_continuous_qscU z.2.1
  have h2 := qsc_continuous_qscU z.2.2
  have := qsc_continuous_planeLength
  fun_prop

theorem qsc_continuous_G {z : ℝ × (Fin 2 → ℝ) × (Fin 2 → ℝ)} (hz : z ∈ separatedDomain) :
    Continuous fun p : ℝ × ℝ => qscG z p.1 p.2 := by
  have hs := qsc_continuous_sep z
  have hj1 := (continuous_keplerJac z.2.1).comp continuous_fst (X := ℝ × ℝ)
  have hj2 := (continuous_keplerJac z.2.2).comp continuous_snd (X := ℝ × ℝ)
  exact ((hs.inv₀ fun p => (qsc_sep_pos hz _ _).ne').mul hj1).mul hj2

theorem qsc_dimensionlessPair {z : ℝ × (Fin 2 → ℝ) × (Fin 2 → ℝ)} (hz : z ∈ separatedDomain) :
    dimensionlessPair z = avg (fun t : Vec 2 => qscG z (t 0) (t 1)) := by
  have hz' := hz
  obtain ⟨h0, h1, h2, h3, h4⟩ := hz'
  have e1 : planeLength z.2.1 < 1 := by linarith
  have e2 : planeLength z.2.2 < 1 := by linarith
  rw [avg_pair (j := 0) (k := 1) (by decide)
    ((qsc_continuous_G hz).continuousOn)]
  unfold dimensionlessPair
  congr 1
  set Φ : ℝ → ℝ := fun F₁ => ∫ F₂ in (0:ℝ)..2 * π,
    (planeLength (z.1 • qscU z.2.1 F₁ - qscU z.2.2 F₂))⁻¹ * keplerJac z.2.2 F₂ with hΦ
  have hsc := qsc_continuous_sep z
  have hjoint : Continuous fun p : ℝ × ℝ =>
      (planeLength (z.1 • qscU z.2.1 p.1 - qscU z.2.2 p.2))⁻¹ * keplerJac z.2.2 p.2 :=
    (hsc.inv₀ fun p => (qsc_sep_pos hz _ _).ne').mul
      ((continuous_keplerJac z.2.2).comp continuous_snd)
  have hΦc : Continuous Φ :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun F₁ F₂ => (planeLength (z.1 • qscU z.2.1 F₁ - qscU z.2.2 F₂))⁻¹ *
        keplerJac z.2.2 F₂) hjoint 0 (2 * π)
  have hΦp : Function.Periodic Φ (2 * π) := fun F => by
    simp only [hΦ, qsc_periodic_qscU z.2.1 F]
  have hin : ∀ s, ∫ t in (0:ℝ)..2 * π,
      (planeLength (z.1 • unitPosition s z.2.1 - unitPosition t z.2.2))⁻¹ =
        Φ (keplerLong s z.2.1) := by
    intro s
    simp only [qsc_unitPosition]
    have hc : Continuous fun F : ℝ => (planeLength (z.1 • qscU z.2.1 (keplerLong s z.2.1) -
        qscU z.2.2 F))⁻¹ := by
      have h2 := qsc_continuous_qscU z.2.2
      have := qsc_continuous_planeLength
      refine Continuous.inv₀ (by fun_prop) fun F => (qsc_sep_pos hz _ _).ne'
    have hp : Function.Periodic (fun F : ℝ => (planeLength (z.1 • qscU z.2.1 (keplerLong s z.2.1) -
        qscU z.2.2 F))⁻¹) (2 * π) := fun F => by
      simp only [qsc_periodic_qscU z.2.2 F]
    exact integral_keplerLong_comp e2 hc hp
  have hqin : ∀ s, ∫ t in (0:ℝ)..2 * π, qscG z s t = Φ s * keplerJac z.2.1 s := by
    intro s
    simp only [qscG, hΦ]
    rw [← intervalIntegral.integral_mul_const]
    refine intervalIntegral.integral_congr fun t _ => ?_
    ring
  simp only [hin, hqin]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  congr 1
  exact integral_keplerLong_comp e1 hΦc hΦp

end SecularForm
end KAM.Planetary
end
