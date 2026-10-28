/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.SecularForm.Laplace

/-!
# Secular spectrum: `b_s^(1) > b_s^(2)`

Blueprint P, Part 9 (`bpP:p9:l74`, `stepP:p9:l74-red`, `stepP:p9:l74-ibp`): the difference of the
first two Laplace coefficients as a positive integral over `[0, π]`.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter Real Function
open scoped BigOperators Topology
namespace KAM.Planetary
open KAM KAM.Kepler

namespace SecularSpectrum
open SecularForm

lemma lap_base_pos {α : ℝ} (hα : 0 < α) (hα1 : α < 1) (t : ℝ) :
    0 < 1 + α^2 - 2*α*Real.cos t := by
  nlinarith [Real.cos_le_one t, sq_nonneg (1 - α)]

lemma lap_integrand_continuous (s : ℝ) {α : ℝ} (hα : 0 < α) (hα1 : α < 1) (k : ℤ) :
    Continuous fun t : ℝ => Real.cos ((k : ℝ) * t) * (1 + α^2 - 2*α*Real.cos t) ^ (-s) := by
  refine (by fun_prop : Continuous fun t : ℝ => Real.cos ((k : ℝ) * t)).mul ?_
  exact Continuous.rpow (by fun_prop) continuous_const fun t => Or.inl (lap_base_pos hα hα1 t).ne'

/-- Reduction to `[0, π]` (`stepP:p9:l74-red`). -/
lemma laplace_def_eq_half (s : ℝ) {α : ℝ} (hα : 0 < α) (hα1 : α < 1) (k : ℤ) :
    laplace_def s k α = π⁻¹ * ∫ t in (0:ℝ)..π,
      Real.cos ((k : ℝ) * t) * (1 + α^2 - 2*α*Real.cos t) ^ (-s) := by
  set g : ℝ → ℝ := fun t => Real.cos ((k : ℝ) * t) * (1 + α^2 - 2*α*Real.cos t) ^ (-s) with hg
  have hc : Continuous g := lap_integrand_continuous s hα hα1 k
  have hsym : ∀ t, g (2*π - t) = g t := fun t => by
    simp only [hg]
    have h1 : Real.cos ((k : ℝ) * (2*π - t)) = Real.cos ((k : ℝ) * t) := by
      rw [mul_sub, show (k : ℝ) * (2*π) = k * (2*π) by rfl, Real.cos_int_mul_two_pi_sub]
    rw [h1, Real.cos_two_pi_sub]
  have h2 : ∫ t in π..2*π, g t = ∫ t in (0:ℝ)..π, g t := by
    have := intervalIntegral.integral_comp_sub_left (a := 0) (b := π) g (2*π)
    rw [show 2*π - π = π by ring, sub_zero] at this
    rw [← this]
    exact (intervalIntegral.integral_congr fun t _ => hsym t)
  have h3 : ∫ t in (0:ℝ)..2*π, g t = 2 * ∫ t in (0:ℝ)..π, g t := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (b := π)
      (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _), h2]
    ring
  unfold laplace_def
  rw [← hg, h3]
  field_simp

lemma laplace_def_sub_eq (s : ℝ) {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    laplace_def s 1 α - laplace_def s 2 α = π⁻¹ * ∫ t in (0:ℝ)..π,
      (Real.cos t - Real.cos (2*t)) * (1 + α^2 - 2*α*Real.cos t) ^ (-s) := by
  rw [laplace_def_eq_half s hα hα1, laplace_def_eq_half s hα hα1, ← mul_sub,
    ← intervalIntegral.integral_sub
      ((lap_integrand_continuous s hα hα1 1).intervalIntegrable _ _)
      ((lap_integrand_continuous s hα hα1 2).intervalIntegrable _ _)]
  congr 1
  refine intervalIntegral.integral_congr fun t _ => ?_
  simp only [Int.cast_one, Int.cast_ofNat, one_mul]
  ring

/-- Integration by parts (`stepP:p9:l74-ibp`). -/
lemma ibp_formula (s : ℝ) {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    ∫ t in (0:ℝ)..π, (Real.cos t - Real.cos (2*t)) * (1 + α^2 - 2*α*Real.cos t) ^ (-s) =
      2*s*α * ∫ t in (0:ℝ)..π,
        Real.sin t^2 * (1-Real.cos t) * (1+α^2-2*α*Real.cos t)^(-s-1) := by
  have hA := lap_base_pos hα hα1
  have hu : ∀ x ∈ Set.uIcc (0:ℝ) π, HasDerivAt (fun t => (1 + α^2 - 2*α*Real.cos t) ^ (-s))
      (2*α*Real.sin x * (-s) * (1 + α^2 - 2*α*Real.cos x) ^ (-s-1)) x := fun x _ => by
    have h1 : HasDerivAt (fun t => 1 + α^2 - 2*α*Real.cos t) (2*α*Real.sin x) x := by
      have := ((Real.hasDerivAt_cos x).const_mul (2*α)).const_sub (1 + α^2)
      simpa using this
    exact h1.rpow_const (Or.inl (hA x).ne')
  have hv : ∀ x ∈ Set.uIcc (0:ℝ) π, HasDerivAt (fun t => Real.sin t * (1 - Real.cos t))
      (Real.cos x - Real.cos (2*x)) x := fun x _ => by
    have := (Real.hasDerivAt_sin x).mul ((Real.hasDerivAt_cos x).const_sub 1)
    convert this using 1
    rw [Real.cos_two_mul]
    nlinarith [Real.sin_sq_add_cos_sq x]
  have hu' : Continuous fun x => 2*α*Real.sin x * (-s) * (1 + α^2 - 2*α*Real.cos x) ^ (-s-1) :=
    (by fun_prop : Continuous fun x => 2*α*Real.sin x * (-s)).mul
      (Continuous.rpow (by fun_prop) continuous_const fun t => Or.inl (hA t).ne')
  have key := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv
    (hu'.intervalIntegrable _ _) ((by fun_prop : Continuous fun x => Real.cos x -
      Real.cos (2*x)).intervalIntegrable _ _)
  simp only [Real.sin_pi, Real.sin_zero, zero_mul, mul_zero, sub_self, zero_sub] at key
  rw [show (∫ t in (0:ℝ)..π, (Real.cos t - Real.cos (2*t)) *
        (1 + α^2 - 2*α*Real.cos t) ^ (-s)) =
      ∫ t in (0:ℝ)..π, (1 + α^2 - 2*α*Real.cos t) ^ (-s) * (Real.cos t - Real.cos (2*t)) from
    intervalIntegral.integral_congr fun t _ => mul_comm _ _, key, ← intervalIntegral.integral_neg,
    ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun t _ => ?_
  have : (1 + α^2 - 2*α*Real.cos t) ^ (-s-1) = (1 + α^2 - 2*α*Real.cos t) ^ (-s) *
      (1 + α^2 - 2*α*Real.cos t)⁻¹ := by
    rw [Real.rpow_sub (hA t), Real.rpow_one, div_eq_mul_inv]
  simp only [this]
  field_simp

theorem l74 {s α : ℝ} (hs : 0 < s) (hα : 0 < α) (hα1 : α < 1) :
    laplace_def s 1 α - laplace_def s 2 α =
      2*s*α/π * ∫ t in (0:ℝ)..π,
        Real.sin t^2 * (1-Real.cos t) * (1+α^2-2*α*Real.cos t)^(-s-1) ∧
    0 < laplace_def s 1 α - laplace_def s 2 α := by
  have e : laplace_def s 1 α - laplace_def s 2 α = 2*s*α/π * ∫ t in (0:ℝ)..π,
        Real.sin t^2 * (1-Real.cos t) * (1+α^2-2*α*Real.cos t)^(-s-1) := by
    rw [laplace_def_sub_eq s hα hα1, ibp_formula s hα hα1]
    ring
  refine ⟨e, ?_⟩
  rw [e]
  refine mul_pos (by positivity) ?_
  refine intervalIntegral.intervalIntegral_pos_of_pos_on ?_ (fun t ht => ?_) Real.pi_pos
  · exact (Continuous.mul (by fun_prop)
      (Continuous.rpow (by fun_prop) continuous_const fun t =>
        Or.inl (lap_base_pos hα hα1 t).ne')).intervalIntegrable _ _
  · have hsin : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht.1 ht.2
    have hcos : Real.cos t < 1 := by
      have := Real.cos_lt_cos_of_nonneg_of_le_pi (le_refl 0) ht.2.le ht.1
      simpa using this
    have := Real.rpow_pos_of_pos (lap_base_pos hα hα1 t) (-s-1)
    have : 0 < 1 - Real.cos t := by linarith
    positivity

end SecularSpectrum

end KAM.Planetary
