/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.SecularForm.CrossJet.PairAverage
public import KAM.Planetary.SecularForm.CrossJet.MixedKernel
public import KAM.Planetary.SecularForm.Basic
public import KAM.Planetary.SecularForm.LaplaceIdentities
public import KAM.Planetary.SecularForm.Coefficients

/-!
# Cross jet: Fourier selection

Blueprint P, Part 8, `stepP:p8:qf-cross` (Fourier selection): the double average of the cross
kernel over
the two mean longitudes is evaluated by the torus change of variables `t = s - ϑ`; the average over
`s` of the resulting quadratic form in `(cos s, sin s)` leaves a function of `ϑ` alone, which is
reduced to `laplace_def (3/2) 2` by one periodic integration by parts. No Laplace series is used.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter Real Function Metric KAM KAM.Kepler
open scoped Topology ContDiff
namespace KAM.Planetary
namespace SecularForm

/-- The squared separation `a² + b² - 2ab cos ϑ` of two points on circles of radii `a`, `b`. -/
def sep2 (a b ϑ : ℝ) : ℝ := a ^ 2 + b ^ 2 - 2 * a * b * Real.cos ϑ

theorem sep2_pos {a b : ℝ} (ha : 0 < a) (hab : a < b) (ϑ : ℝ) : 0 < sep2 a b ϑ := by
  unfold sep2
  nlinarith [Real.cos_le_one ϑ, mul_pos ha (sub_pos.2 hab), sq_nonneg (b - a)]

theorem continuous_sep2 (a b : ℝ) : Continuous (sep2 a b) := by unfold sep2; fun_prop

/-- `v(ϑ) = |d|⁻³` and its derivative `-3ab sin ϑ / |d|⁵`. -/
theorem hasDerivAt_sep2_inv_cube {a b : ℝ} (ha : 0 < a) (hab : a < b) (ϑ : ℝ) :
    HasDerivAt (fun ϑ => ((√(sep2 a b ϑ)) ^ 3)⁻¹)
      (-(3 * a * b * Real.sin ϑ) / (√(sep2 a b ϑ)) ^ 5) ϑ := by
  have hp := sep2_pos ha hab ϑ
  have hR : HasDerivAt (sep2 a b) (2 * a * b * Real.sin ϑ) ϑ := by
    unfold sep2
    exact ((hasDerivAt_const ϑ (a ^ 2 + b ^ 2)).sub
      ((Real.hasDerivAt_cos ϑ).const_mul (2 * a * b))).congr_deriv (by ring)
  have hs := (hR.sqrt hp.ne')
  have h3 := (hs.pow 3).inv (pow_ne_zero 3 (Real.sqrt_pos.2 hp).ne')
  refine h3.congr_deriv ?_
  have hr := (Real.sqrt_pos.2 hp).ne'
  simp only [Pi.pow_apply]
  norm_num
  field_simp

theorem ibp_selection {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    ∫ ϑ in (0:ℝ)..2 * π, 3 * a * b * (Real.sin ϑ ^ 2 * Real.cos ϑ) / (√(sep2 a b ϑ)) ^ 5 =
      ∫ ϑ in (0:ℝ)..2 * π, Real.cos (2 * ϑ) * ((√(sep2 a b ϑ)) ^ 3)⁻¹ := by
  have hv : ∀ ϑ ∈ uIcc (0:ℝ) (2 * π), HasDerivAt (fun ϑ => ((√(sep2 a b ϑ)) ^ 3)⁻¹)
      (-(3 * a * b * Real.sin ϑ) / (√(sep2 a b ϑ)) ^ 5) ϑ := fun ϑ _ => hasDerivAt_sep2_inv_cube
          ha hab ϑ
  have hu : ∀ ϑ ∈ uIcc (0:ℝ) (2 * π), HasDerivAt (fun ϑ => Real.sin ϑ * Real.cos ϑ)
      (Real.cos ϑ ^ 2 - Real.sin ϑ ^ 2) ϑ := by
    intro ϑ _
    have := (Real.hasDerivAt_sin ϑ).mul (Real.hasDerivAt_cos ϑ)
    refine this.congr_deriv ?_
    ring
  have hcont : Continuous fun ϑ => (√(sep2 a b ϑ)) := by
    exact (continuous_sep2 a b).sqrt
  have hpos : ∀ ϑ, 0 < √(sep2 a b ϑ) := fun ϑ => Real.sqrt_pos.2 (sep2_pos ha hab ϑ)
  have h1 : IntervalIntegrable (fun ϑ => (Real.cos ϑ ^ 2 - Real.sin ϑ ^ 2)) volume 0 (2 * π) := by
    apply Continuous.intervalIntegrable; fun_prop
  have h2 : IntervalIntegrable (fun ϑ => -(3 * a * b * Real.sin ϑ) / (√(sep2 a b ϑ)) ^ 5) volume
      0 (2 * π) := by
    apply Continuous.intervalIntegrable
    exact (by fun_prop : Continuous fun ϑ => -(3 * a * b * Real.sin ϑ)).div (hcont.pow 5)
      (fun ϑ => pow_ne_zero 5 (hpos ϑ).ne')
  have key := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv h1 h2
  simp only [Real.sin_zero, Real.cos_zero, zero_mul, Real.sin_two_pi, sub_self,
    zero_sub] at key
  have e1 : ∫ ϑ in (0:ℝ)..2 * π, 3 * a * b * (Real.sin ϑ ^ 2 * Real.cos ϑ) / (√(sep2 a b ϑ)) ^ 5 =
      -∫ ϑ in (0:ℝ)..2 * π, Real.sin ϑ * Real.cos ϑ *
        (-(3 * a * b * Real.sin ϑ) / (√(sep2 a b ϑ)) ^ 5) := by
    rw [← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun ϑ _ => ?_
    ring
  have e2 : ∫ ϑ in (0:ℝ)..2 * π, Real.cos (2 * ϑ) * ((√(sep2 a b ϑ)) ^ 3)⁻¹ =
      ∫ ϑ in (0:ℝ)..2 * π, (Real.cos ϑ ^ 2 - Real.sin ϑ ^ 2) * ((√(sep2 a b ϑ)) ^ 3)⁻¹ := by
    refine intervalIntegral.integral_congr fun ϑ _ => ?_
    rw [show Real.cos (2 * ϑ) = Real.cos ϑ ^ 2 - Real.sin ϑ ^ 2 by
      rw [Real.cos_two_mul]; nlinarith [Real.sin_sq_add_cos_sq ϑ]]
  rw [e1, e2, key, neg_neg]

/-- The torus average of a continuous function, periodic in the second variable, can be computed
along the diagonals `t = s - ϑ`. -/
theorem torus_reduce {G : ℝ → ℝ → ℝ} (hG : Continuous (Function.uncurry G))
    (hper : ∀ s, Function.Periodic (G s) (2 * π)) :
    ∫ s in (0:ℝ)..2 * π, ∫ t in (0:ℝ)..2 * π, G s t =
      ∫ ϑ in (0:ℝ)..2 * π, ∫ s in (0:ℝ)..2 * π, G s (s - ϑ) := by
  have h1 : ∀ s, ∫ t in (0:ℝ)..2 * π, G s t = ∫ ϑ in (0:ℝ)..2 * π, G s (s - ϑ) := by
    intro s
    rw [intervalIntegral.integral_comp_sub_left (fun x => G s x) s, sub_zero]
    have := (hper s).intervalIntegral_add_eq (s - 2 * π) 0
    simp only [sub_add_cancel, zero_add] at this
    exact this.symm
  simp_rw [h1]
  refine intervalIntegral_intervalIntegral_swap ?_
  have hc : Continuous (Function.uncurry fun s ϑ => G s (s - ϑ)) := by
    have : Function.uncurry (fun s ϑ => G s (s - ϑ)) =
        Function.uncurry G ∘ fun p : ℝ × ℝ => (p.1, p.1 - p.2) := by
      funext p; rfl
    rw [this]
    exact hG.comp (by fun_prop)
  have h2π : (0:ℝ) ≤ 2 * π := by positivity
  have hsub : uIoc (0:ℝ) (2 * π) ×ˢ uIoc (0:ℝ) (2 * π) ⊆ Icc (0:ℝ) (2 * π) ×ˢ Icc (0:ℝ) (2 * π)
      := by
    rw [uIoc_of_le h2π]
    exact prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self
  exact (hc.continuousOn.integrableOn_compact
    (isCompact_Icc (a := (0:ℝ)) (b := 2 * π) |>.prod (isCompact_Icc (a := (0:ℝ)) (b := 2 *
        π)))).mono_set hsub

/-- The coefficients of the quadratic form in `(cos s, sin s)` obtained from the cross kernel on the
diagonal `t = s - ϑ` (`x = cos ϑ`, `y = sin ϑ`). -/
def cN20 (a b ϑ : ℝ) : ℝ := a^2*Real.cos ϑ^2 + 2*a^2*Real.sin ϑ^2 - a*b*Real.cos ϑ^3 -
    2*a*b*Real.cos ϑ*Real.sin ϑ^2 - a*b*Real.cos ϑ + b^2*Real.cos ϑ^2
def cN11 (a b ϑ : ℝ) : ℝ := -a^2*Real.cos ϑ*Real.sin ϑ - a*b*Real.cos ϑ^2*Real.sin ϑ -
    4*a*b*Real.sin ϑ^3 - a*b*Real.sin ϑ + 3*b^2*Real.cos ϑ*Real.sin ϑ
def cN02 (a b ϑ : ℝ) : ℝ := 2*a*b*Real.cos ϑ*Real.sin ϑ^2 + 2*b^2*Real.sin ϑ^2
def cM20 (ϑ : ℝ) : ℝ := Real.cos ϑ^2 + 2*Real.sin ϑ^2
def cM11 (ϑ : ℝ) : ℝ := -3*Real.cos ϑ*Real.sin ϑ
def cM02 (ϑ : ℝ) : ℝ := 4*Real.cos ϑ^2 + 2*Real.sin ϑ^2

/-- `crossKernel 1` at two points of two circles, with the first variations. -/
def crossU (a b s t : ℝ) : ℝ :=
  crossKernel 1 (a • cvec s - b • cvec t) (uvec s) (uvec t)

theorem crossU_diag (a b s ϑ : ℝ) :
    crossU a b s (s - ϑ) =
      3 * (cN20 a b ϑ * Real.cos s ^ 2 + cN11 a b ϑ * (Real.cos s * Real.sin s) +
          cN02 a b ϑ * Real.sin s ^ 2) / (√(sep2 a b ϑ)) ^ 5 -
        (cM20 ϑ * Real.cos s ^ 2 + cM11 ϑ * (Real.cos s * Real.sin s) +
          cM02 ϑ * Real.sin s ^ 2) / (√(sep2 a b ϑ)) ^ 3 := by
  have h1 : Real.cos s ^ 2 + Real.sin s ^ 2 = 1 := Real.cos_sq_add_sin_sq s
  have h2 : Real.cos ϑ ^ 2 + Real.sin ϑ ^ 2 = 1 := Real.cos_sq_add_sin_sq ϑ
  have hℓ : planeLength (a • cvec s - b • cvec (s - ϑ)) = √(sep2 a b ϑ) := by
    rw [planeLength_eq_sqrt]
    congr 1
    simp only [cvec, sep2, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
      Matrix.cons_val_one, Real.cos_sub, Real.sin_sub]
    linear_combination (a ^ 2 - 2 * a * b * Real.cos ϑ + b ^ 2) * h1 +
      b ^ 2 * (Real.cos s ^ 2 + Real.sin s ^ 2) * h2
  have hN : ((a • cvec s - b • cvec (s - ϑ)) 0 * uvec s 0 + (a • cvec s - b • cvec (s - ϑ)) 1 *
      uvec s 1) *
      ((a • cvec s - b • cvec (s - ϑ)) 0 * uvec (s - ϑ) 0 +
        (a • cvec s - b • cvec (s - ϑ)) 1 * uvec (s - ϑ) 1) =
      cN20 a b ϑ * Real.cos s ^ 2 + cN11 a b ϑ * (Real.cos s * Real.sin s) +
        cN02 a b ϑ * Real.sin s ^ 2 := by
    simp only [cvec, uvec, cN20, cN11, cN02, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      Matrix.cons_val_zero, Matrix.cons_val_one, Real.cos_sub, Real.sin_sub]
    linear_combination (a^2*Real.cos s^2*Real.sin ϑ^2 - a^2*Real.cos s*Real.sin s*Real.cos
        ϑ*Real.sin ϑ - a^2*Real.cos ϑ^2 - a^2*Real.sin ϑ^2 + a^2 - a*b*Real.cos s^3*Real.sin
        s*Real.sin ϑ^3 + a*b*Real.cos s^2*Real.sin s^2*Real.cos ϑ*Real.sin ϑ^2 - a*b*Real.cos
        s^2*Real.cos ϑ*Real.sin ϑ^2 - a*b*Real.cos s*Real.sin s^3*Real.sin ϑ^3 + a*b*Real.cos
        s*Real.sin s*Real.cos ϑ^2*Real.sin ϑ - 2*a*b*Real.cos s*Real.sin s*Real.sin ϑ^3 -
        a*b*Real.cos s*Real.sin s*Real.sin ϑ + a*b*Real.sin s^4*Real.cos ϑ*Real.sin ϑ^2 +
        2*a*b*Real.sin s^2*Real.cos ϑ*Real.sin ϑ^2 + a*b*Real.cos ϑ^3 + a*b*Real.cos ϑ*Real.sin
        ϑ^2 - a*b*Real.cos ϑ + b^2*Real.cos s*Real.sin s*Real.cos ϑ*Real.sin ϑ + b^2*Real.sin
        s^2*Real.sin ϑ^2) * h1 + (a^2*Real.sin s^2 - a^2 + 2*a*b*Real.cos s*Real.sin s*Real.sin ϑ
        - a*b*Real.sin s^2*Real.cos ϑ + a*b*Real.cos ϑ) * h2
  have hM : uvec s 0 * uvec (s - ϑ) 0 + uvec s 1 * uvec (s - ϑ) 1 =
      cM20 ϑ * Real.cos s ^ 2 + cM11 ϑ * (Real.cos s * Real.sin s) + cM02 ϑ * Real.sin s ^ 2 := by
    simp only [uvec, cM20, cM11, cM02, Matrix.cons_val_zero,
      Matrix.cons_val_one, Real.cos_sub, Real.sin_sub]
    linear_combination (-Real.cos s*Real.sin s*Real.cos ϑ*Real.sin ϑ + Real.sin s^2*Real.cos ϑ^2
        - Real.cos ϑ^2 - Real.sin ϑ^2) * h1 + (-Real.sin s^2 - 1) * h2
  unfold crossU crossKernel
  rw [hℓ]
  rw [show ∀ A B : ℝ, 3 * A * B = 3 * (A * B) from fun A B => by ring, hN, hM]
  ring

theorem quad_integral (A B C : ℝ) :
    ∫ s in (0:ℝ)..2 * π, (A * Real.cos s ^ 2 + B * (Real.cos s * Real.sin s) + C * Real.sin s ^ 2) =
      π * (A + C) := by
  have hc : IntervalIntegrable (fun s => A * Real.cos s ^ 2) volume 0 (2 * π) := by
    apply Continuous.intervalIntegrable; fun_prop
  have hm : IntervalIntegrable (fun s => B * (Real.cos s * Real.sin s)) volume 0 (2 * π) := by
    apply Continuous.intervalIntegrable; fun_prop
  have hs : IntervalIntegrable (fun s => C * Real.sin s ^ 2) volume 0 (2 * π) := by
    apply Continuous.intervalIntegrable; fun_prop
  rw [intervalIntegral.integral_add (hc.add hm) hs, intervalIntegral.integral_add hc hm,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, integral_cos_sq, integral_sin_sq]
  have hcs : ∫ x in (0:ℝ)..2 * π, Real.cos x * Real.sin x = 0 := by
    have := integral_sin_mul_cos₁ (a := 0) (b := 2 * π)
    simp only [Real.sin_two_pi, Real.sin_zero] at this
    simp_rw [mul_comm (Real.cos _)] 
    simp
  rw [hcs]
  simp only [Real.cos_two_pi, Real.sin_two_pi, Real.cos_zero, Real.sin_zero]
  ring

/-- The average over `s` of the cross kernel along the diagonal `t = s - ϑ`. -/
theorem avg_cross_diag (a b ϑ : ℝ) :
    ∫ s in (0:ℝ)..2 * π, crossU a b s (s - ϑ) =
      π * (3 * (cN20 a b ϑ + cN02 a b ϑ) / (√(sep2 a b ϑ)) ^ 5 -
        (cM20 ϑ + cM02 ϑ) / (√(sep2 a b ϑ)) ^ 3) := by
  have : ∀ s, crossU a b s (s - ϑ) =
      (3 * cN20 a b ϑ / (√(sep2 a b ϑ)) ^ 5 - cM20 ϑ / (√(sep2 a b ϑ)) ^ 3) * Real.cos s ^ 2 +
      (3 * cN11 a b ϑ / (√(sep2 a b ϑ)) ^ 5 - cM11 ϑ / (√(sep2 a b ϑ)) ^ 3) *
        (Real.cos s * Real.sin s) +
      (3 * cN02 a b ϑ / (√(sep2 a b ϑ)) ^ 5 - cM02 ϑ / (√(sep2 a b ϑ)) ^ 3) * Real.sin s ^ 2 := by
    intro s
    rw [crossU_diag]
    ring
  simp_rw [this]
  rw [quad_integral]
  ring

/-- The averaged cross kernel, rewritten as the target plus an exact periodic derivative term. -/
theorem fbar_eq {a b : ℝ} (ha : 0 < a) (hab : a < b) (ϑ : ℝ) :
    3 * (cN20 a b ϑ + cN02 a b ϑ) / (√(sep2 a b ϑ)) ^ 5 -
        (cM20 ϑ + cM02 ϑ) / (√(sep2 a b ϑ)) ^ 3 =
      Real.cos (2 * ϑ) * ((√(sep2 a b ϑ)) ^ 3)⁻¹ +
        3 * (3 * a * b * (Real.sin ϑ ^ 2 * Real.cos ϑ) / (√(sep2 a b ϑ)) ^ 5 -
          Real.cos (2 * ϑ) * ((√(sep2 a b ϑ)) ^ 3)⁻¹) := by
  have hp := sep2_pos ha hab ϑ
  have hr := (Real.sqrt_pos.2 hp).ne'
  have hr2 : (√(sep2 a b ϑ)) ^ 2 = a ^ 2 + b ^ 2 - 2 * a * b * Real.cos ϑ := Real.sq_sqrt hp.le
  have h2 : Real.cos ϑ ^ 2 + Real.sin ϑ ^ 2 = 1 := Real.cos_sq_add_sin_sq ϑ
  have hc2 : Real.cos (2 * ϑ) = 2 * Real.cos ϑ ^ 2 - 1 := Real.cos_two_mul ϑ
  set r := √(sep2 a b ϑ) with hrdef
  have key : 3 * (cN20 a b ϑ + cN02 a b ϑ) - (cM20 ϑ + cM02 ϑ) * r ^ 2 =
      9 * a * b * (Real.sin ϑ ^ 2 * Real.cos ϑ) - 2 * Real.cos (2 * ϑ) * r ^ 2 := by
    rw [hr2, hc2]
    unfold cN20 cN02 cM20 cM02
    linear_combination (2 * a ^ 2 - a * b * Real.cos ϑ + 2 * b ^ 2) * h2
  have e1 : 3 * (cN20 a b ϑ + cN02 a b ϑ) / r ^ 5 - (cM20 ϑ + cM02 ϑ) / r ^ 3 =
      (3 * (cN20 a b ϑ + cN02 a b ϑ) - (cM20 ϑ + cM02 ϑ) * r ^ 2) / r ^ 5 := by
    field_simp
  rw [e1, key]
  field_simp
  ring

theorem planeLength_circ (a b s t : ℝ) :
    planeLength (a • cvec s - b • cvec t) = √(sep2 a b (s - t)) := by
  rw [planeLength_eq_sqrt]
  congr 1
  have h1 : Real.cos s ^ 2 + Real.sin s ^ 2 = 1 := Real.cos_sq_add_sin_sq s
  have h2 : Real.cos t ^ 2 + Real.sin t ^ 2 = 1 := Real.cos_sq_add_sin_sq t
  simp only [cvec, sep2, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
    Matrix.cons_val_one, Real.cos_sub]
  linear_combination a ^ 2 * h1 + b ^ 2 * h2

theorem continuous_crossU {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    Continuous (Function.uncurry (crossU a b)) := by
  have hpos : ∀ p : ℝ × ℝ, 0 < √(sep2 a b (p.1 - p.2)) :=
    fun p => Real.sqrt_pos.2 (sep2_pos ha hab _)
  have hs : Continuous fun p : ℝ × ℝ => √(sep2 a b (p.1 - p.2)) :=
    ((continuous_sep2 a b).comp (by fun_prop)).sqrt
  have : Function.uncurry (crossU a b) = fun p : ℝ × ℝ =>
      1 * (3 * (((a • cvec p.1 - b • cvec p.2) 0 * uvec p.1 0 +
          (a • cvec p.1 - b • cvec p.2) 1 * uvec p.1 1) *
        ((a • cvec p.1 - b • cvec p.2) 0 * uvec p.2 0 +
          (a • cvec p.1 - b • cvec p.2) 1 * uvec p.2 1)) / (√(sep2 a b (p.1 - p.2))) ^ 5 -
        (uvec p.1 0 * uvec p.2 0 + uvec p.1 1 * uvec p.2 1) / (√(sep2 a b (p.1 - p.2))) ^ 3) := by
    funext p
    unfold Function.uncurry crossU crossKernel
    rw [planeLength_circ]
    ring
  rw [this]
  simp only [cvec, uvec, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  refine continuous_const.mul (Continuous.sub (Continuous.div (by fun_prop) (hs.pow 5)
    fun p => pow_ne_zero 5 (hpos p).ne') (Continuous.div (by fun_prop) (hs.pow 3)
    fun p => pow_ne_zero 3 (hpos p).ne'))

theorem crossU_periodic (a b s : ℝ) : Function.Periodic (crossU a b s) (2 * π) := by
  intro t
  unfold crossU cvec uvec
  simp only [Real.cos_add_two_pi, Real.sin_add_two_pi]

theorem sep2_eq_mul {a b : ℝ} (hb : 0 < b) (ϑ : ℝ) :
    sep2 a b ϑ = b ^ 2 * (1 + (a / b) ^ 2 - 2 * (a / b) * Real.cos ϑ) := by
  unfold sep2; field_simp; ring

theorem inv_cube_sep2 {a b : ℝ} (ha : 0 < a) (hab : a < b) (ϑ : ℝ) :
    ((√(sep2 a b ϑ)) ^ 3)⁻¹ =
      (b ^ 3)⁻¹ * (1 + (a / b) ^ 2 - 2 * (a / b) * Real.cos ϑ) ^ (-(3 / 2 : ℝ)) := by
  have hb : 0 < b := ha.trans hab
  have h := sep2_eq_mul (a := a) hb ϑ
  have hX : 0 < 1 + (a / b) ^ 2 - 2 * (a / b) * Real.cos ϑ := by
    have := sep2_pos ha hab ϑ
    rw [h] at this
    exact (mul_pos_iff_of_pos_left (pow_pos hb 2)).1 this
  have hs : (√(1 + (a / b) ^ 2 - 2 * (a / b) * Real.cos ϑ)) ^ 3 =
      (1 + (a / b) ^ 2 - 2 * (a / b) * Real.cos ϑ) ^ (3 / 2 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hX.le]
    norm_num
  rw [h, Real.sqrt_mul (sq_nonneg b), Real.sqrt_sq hb.le, mul_pow, mul_inv,
    Real.rpow_neg hX.le, ← hs]

theorem integral_cos_two_inv_cube {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    ∫ ϑ in (0:ℝ)..2 * π, Real.cos (2 * ϑ) * ((√(sep2 a b ϑ)) ^ 3)⁻¹ =
      (b ^ 3)⁻¹ * ((2 * π) * laplace_def (3 / 2) 2 (a / b)) := by
  unfold laplace_def
  rw [mul_inv_cancel_left₀ (by positivity : (2 * π) ≠ 0)]
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun ϑ _ => ?_
  simp only [inv_cube_sep2 ha hab ϑ]
  push_cast
  ring

/-- Fourier selection: the double average of the cross kernel over the two mean longitudes.
`stepP:p8:qf-cross`: it equals `b_{3/2}^{(2)}(a/b) / (2 b³)`, with `laplace_def (3/2) 2`. -/
theorem cross_double_average {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    (2 * π)⁻¹ * ∫ s in (0:ℝ)..2 * π, (2 * π)⁻¹ * ∫ t in (0:ℝ)..2 * π, crossU a b s t =
      (2 * b ^ 3)⁻¹ * laplace_def (3 / 2) 2 (a / b) := by
  have hpos : ∀ ϑ, 0 < √(sep2 a b ϑ) := fun ϑ => Real.sqrt_pos.2 (sep2_pos ha hab ϑ)
  have hcs : Continuous fun ϑ => √(sep2 a b ϑ) := (continuous_sep2 a b).sqrt
  have hI1 : IntervalIntegrable
      (fun ϑ => 3 * a * b * (Real.sin ϑ ^ 2 * Real.cos ϑ) / (√(sep2 a b ϑ)) ^ 5)
      volume 0 (2 * π) := by
    apply Continuous.intervalIntegrable
    exact (by fun_prop : Continuous fun ϑ : ℝ => 3 * a * b * (Real.sin ϑ ^ 2 * Real.cos ϑ)).div
      (hcs.pow 5) fun ϑ => pow_ne_zero 5 (hpos ϑ).ne'
  have hI2 : IntervalIntegrable
      (fun ϑ => Real.cos (2 * ϑ) * ((√(sep2 a b ϑ)) ^ 3)⁻¹) volume 0 (2 * π) := by
    apply Continuous.intervalIntegrable
    exact (by fun_prop : Continuous fun ϑ : ℝ => Real.cos (2 * ϑ)).mul
      ((hcs.pow 3).inv₀ fun ϑ => pow_ne_zero 3 (hpos ϑ).ne')
  simp only [intervalIntegral.integral_const_mul]
  rw [torus_reduce (continuous_crossU ha hab) (crossU_periodic a b)]
  simp_rw [avg_cross_diag, fbar_eq ha hab]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add hI2
    (hI1.sub hI2 |>.const_mul 3), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub hI1 hI2, ibp_selection ha hab,
    integral_cos_two_inv_cube ha hab]
  field_simp
  ring

end SecularForm
end KAM.Planetary
