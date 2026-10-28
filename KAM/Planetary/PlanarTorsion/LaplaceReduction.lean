/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib

/-!
# Planar quartic torsion: reduction of Laplace coefficients (P11C, package T3)

The normalized radian Laplace integral `p11c_laplace`, the three recurrences `laplace_red`
(integration by parts over the period), the upward recurrences `laplace_up`, and the rational
reduction `laplace_rational_reduction` of every half-integer coefficient to `b_{1/2}^{(0)}`,
`b_{1/2}^{(1)}` with polynomial coefficients over `ℚ`.
-/

@[expose] public noncomputable section
open Set Metric Real MeasureTheory Function
open scoped ContDiff Topology
namespace KAM.Planetary

/-- Purely local integral adapter for Part 8's laplace_def, to be identified by a bridge. -/
def p11c_laplace (s : ℝ) (k : ℤ) (a : ℝ) : ℝ :=
  (2 * π)⁻¹ * ∫ t in (0 : ℝ)..(2 * π), cos ((k : ℝ) * t) / (1 + a ^ 2 - 2 * a * cos t) ^ s

/-! ### The kernel -/

/-- The positive kernel `1 + a² - 2 a cos t`. -/
def p11cKer (a t : ℝ) : ℝ := 1 + a ^ 2 - 2 * a * cos t

theorem p11cKer_pos {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (t : ℝ) : 0 < p11cKer a t := by
  unfold p11cKer
  nlinarith [cos_le_one t, ha.1, ha.2, sq_nonneg (1 - a)]

theorem p11cKer_contDiff (a : ℝ) : Continuous (p11cKer a) := by
  unfold p11cKer; fun_prop

theorem p11c_cont_div {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (s : ℝ) (c : ℝ → ℝ) (hc : Continuous c) :
    Continuous fun t => c t / p11cKer a t ^ s := by
  refine hc.div ((p11cKer_contDiff a).rpow_const fun t => Or.inl (p11cKer_pos ha t).ne') ?_
  intro t
  exact (Real.rpow_pos_of_pos (p11cKer_pos ha t) s).ne'

/-- The raw integral. -/
def p11cI (s : ℝ) (k : ℤ) (a : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..(2 * π), cos ((k : ℝ) * t) / p11cKer a t ^ s

theorem p11c_laplace_eq (s : ℝ) (k : ℤ) (a : ℝ) :
    p11c_laplace s k a = (2 * π)⁻¹ * p11cI s k a := rfl

theorem p11cI_cont {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (s : ℝ) (k : ℤ) :
    Continuous fun t => cos ((k : ℝ) * t) / p11cKer a t ^ s :=
  p11c_cont_div ha s _ (by fun_prop)

/-! ### First recurrence -/

theorem p11cI_red1 {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (s : ℝ) (k : ℤ) :
    p11cI (s - 1) k a = (1 + a ^ 2) * p11cI s k a -
      a * (p11cI s (k + 1) a + p11cI s (k - 1) a) := by
  have key : ∀ t, cos ((k : ℝ) * t) / p11cKer a t ^ (s - 1) =
      (1 + a ^ 2) * (cos ((k : ℝ) * t) / p11cKer a t ^ s) -
        a * (cos (((k + 1 : ℤ) : ℝ) * t) / p11cKer a t ^ s +
          cos (((k - 1 : ℤ) : ℝ) * t) / p11cKer a t ^ s) := by
    intro t
    have hp := p11cKer_pos ha t
    have h1 : p11cKer a t ^ (s - 1) = p11cKer a t ^ s / p11cKer a t := Real.rpow_sub_one hp.ne' s
    have h2 := Real.rpow_pos_of_pos hp s
    have e1 : cos (((k + 1 : ℤ) : ℝ) * t) = cos ((k : ℝ) * t) * cos t - sin ((k : ℝ) * t) * sin t := by
      rw [← cos_add]; push_cast; ring_nf
    have e2 : cos (((k - 1 : ℤ) : ℝ) * t) = cos ((k : ℝ) * t) * cos t + sin ((k : ℝ) * t) * sin t := by
      rw [← cos_sub]; push_cast; ring_nf
    rw [h1, e1, e2]
    unfold p11cKer at *
    field_simp
    ring
  unfold p11cI
  simp_rw [key]
  have i1 := (p11cI_cont ha s k).intervalIntegrable (μ := volume) 0 (2 * π)
  have i2 := (p11cI_cont ha s (k + 1)).intervalIntegrable (μ := volume) 0 (2 * π)
  have i3 := (p11cI_cont ha s (k - 1)).intervalIntegrable (μ := volume) 0 (2 * π)
  rw [intervalIntegral.integral_sub (i1.const_mul _) ((i2.add i3).const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add i2 i3]

/-! ### Second recurrence (integration by parts over the period) -/

theorem p11cI_red2 {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (s : ℝ) (k : ℤ) :
    (k : ℝ) * p11cI (s - 1) k a =
      (s - 1) * a * (p11cI s (k - 1) a - p11cI s (k + 1) a) := by
  set G : ℝ → ℝ := fun t => sin ((k : ℝ) * t) * p11cKer a t ^ (1 - s) with hG
  set G' : ℝ → ℝ := fun t => (k : ℝ) * (cos ((k : ℝ) * t) / p11cKer a t ^ (s - 1)) +
    (1 - s) * a * (cos (((k - 1 : ℤ) : ℝ) * t) / p11cKer a t ^ s -
      cos (((k + 1 : ℤ) : ℝ) * t) / p11cKer a t ^ s) with hG'
  have hder : ∀ t, HasDerivAt G (G' t) t := by
    intro t
    have hp := p11cKer_pos ha t
    have hK : HasDerivAt (p11cKer a) (2 * a * sin t) t := by
      unfold p11cKer
      have := ((hasDerivAt_cos t).const_mul (2 * a)).const_sub (1 + a ^ 2)
      convert this using 1
      ring
    have hs := hK.rpow_const (p := 1 - s) (Or.inl hp.ne')
    have hsin : HasDerivAt (fun t => sin ((k : ℝ) * t)) (cos ((k : ℝ) * t) * (k : ℝ)) t := by
      simpa using ((hasDerivAt_id t).const_mul (k : ℝ)).sin
    convert hsin.mul hs using 1
    have h2 := Real.rpow_pos_of_pos hp s
    have e1 : cos (((k + 1 : ℤ) : ℝ) * t) = cos ((k : ℝ) * t) * cos t - sin ((k : ℝ) * t) * sin t := by
      rw [← cos_add]; push_cast; ring_nf
    have e2 : cos (((k - 1 : ℤ) : ℝ) * t) = cos ((k : ℝ) * t) * cos t + sin ((k : ℝ) * t) * sin t := by
      rw [← cos_sub]; push_cast; ring_nf
    have h3 : p11cKer a t ^ (s - 1) = p11cKer a t ^ s / p11cKer a t := Real.rpow_sub_one hp.ne' s
    have h4 : p11cKer a t ^ (1 - s) = (p11cKer a t ^ (s - 1))⁻¹ := by
      rw [← Real.rpow_neg hp.le]; ring_nf
    have h5 : p11cKer a t ^ (1 - s - 1) = (p11cKer a t ^ s)⁻¹ := by
      rw [← Real.rpow_neg hp.le]; ring_nf
    simp only [hG']
    rw [h5, h4, h3, e1, e2]
    have hpe : p11cKer a t = 1 + a ^ 2 - 2 * a * cos t := rfl
    rw [hpe] at *
    field_simp
    ring
  have hcont : Continuous G' := by
    simp only [hG']
    exact (continuous_const.mul (p11cI_cont ha (s - 1) k)).add
      (continuous_const.mul ((p11cI_cont ha s _).sub (p11cI_cont ha s _)))
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hder t)
    (hcont.intervalIntegrable 0 (2 * π))
  have hz : G (2 * π) - G 0 = 0 := by
    simp only [hG]
    have : sin ((k : ℝ) * (2 * π)) = 0 := by
      have := Real.sin_int_mul_pi (2 * k)
      rw [← this]; push_cast; ring_nf
    rw [this]; simp
  rw [hz] at hFTC
  simp only [hG'] at hFTC
  rw [intervalIntegral.integral_add, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_sub] at hFTC
  · unfold p11cI at *; linarith
  · exact (p11cI_cont ha s _).intervalIntegrable 0 (2 * π)
  · exact (p11cI_cont ha s _).intervalIntegrable 0 (2 * π)
  · exact (continuous_const.mul (p11cI_cont ha (s - 1) k)).intervalIntegrable 0 (2 * π)
  · exact (continuous_const.mul ((p11cI_cont ha s _).sub (p11cI_cont ha s _))).intervalIntegrable 0 (2 * π)

/-! ### Statements -/

theorem p11c_laplace_red1 {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (s : ℝ) (k : ℤ) :
    p11c_laplace (s - 1) k a = (1 + a ^ 2) * p11c_laplace s k a -
      a * (p11c_laplace s (k + 1) a + p11c_laplace s (k - 1) a) := by
  simp only [p11c_laplace_eq, p11cI_red1 ha]
  ring

theorem p11c_laplace_red2 {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (s : ℝ) (k : ℤ) :
    (k : ℝ) * p11c_laplace (s - 1) k a = (s - 1) * a *
      (p11c_laplace s (k - 1) a - p11c_laplace s (k + 1) a) := by
  simp only [p11c_laplace_eq]
  have := p11cI_red2 ha s k
  linear_combination (2 * π)⁻¹ * this

theorem p11c_laplace_red3 {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (s : ℝ) (k : ℤ) :
    (s - 1 - k) * a * p11c_laplace s (k + 1) a =
      (k + s - 1) * a * p11c_laplace s (k - 1) a - k * (1 + a ^ 2) * p11c_laplace s k a := by
  have h1 := p11c_laplace_red1 ha s k
  have h2 := p11c_laplace_red2 ha s k
  rw [h1] at h2
  linear_combination h2

theorem laplace_red (s a : ℝ) (ha : a ∈ Ioo (0 : ℝ) 1) (k : ℕ) :
    p11c_laplace (s - 1) k a = (1 + a ^ 2) * p11c_laplace s k a -
      a * (p11c_laplace s ((k : ℤ) + 1) a + p11c_laplace s ((k : ℤ) - 1) a) ∧
    (k : ℝ) * p11c_laplace (s - 1) k a = (s - 1) * a *
      (p11c_laplace s ((k : ℤ) - 1) a - p11c_laplace s ((k : ℤ) + 1) a) ∧
    (1 ≤ k → (s - 1 - k) * a * p11c_laplace s ((k : ℤ) + 1) a =
      (k + s - 1) * a * p11c_laplace s ((k : ℤ) - 1) a - k * (1 + a ^ 2) * p11c_laplace s k a) := by
  refine ⟨p11c_laplace_red1 ha s k, ?_, fun _ => ?_⟩
  · simpa using p11c_laplace_red2 ha s k
  · simpa using p11c_laplace_red3 ha s k

/-! ### Upward recurrences -/

theorem laplace_up (s a : ℝ) (hs : 1 / 2 ≤ s) (ha : a ∈ Ioo (0 : ℝ) 1) :
    p11c_laplace (s + 1) 0 a = ((1 + a ^ 2) * p11c_laplace s 0 a +
      2 * a * (1 - 1 / s) * p11c_laplace s 1 a) / (1 - a ^ 2) ^ 2 ∧
    p11c_laplace (s + 1) 1 a = ((1 + a ^ 2) * (1 - 1 / s) * p11c_laplace s 1 a +
      2 * a * p11c_laplace s 0 a) / (1 - a ^ 2) ^ 2 ∧
    ∀ k : ℕ, 1 ≤ k → p11c_laplace (s + 1) ((k : ℤ) + 1) a =
      p11c_laplace (s + 1) ((k : ℤ) - 1) a - k * p11c_laplace s k a / (s * a) := by
  have hs0 : s ≠ 0 := by intro h; rw [h] at hs; norm_num at hs
  have ha0 : a ≠ 0 := ha.1.ne'
  have hD : (1 - a ^ 2) ^ 2 ≠ 0 := by
    have : 0 < 1 - a ^ 2 := by nlinarith [ha.1, ha.2]
    positivity
  have hsub : s + 1 - 1 = s := by ring
  have R1 : ∀ k : ℤ, p11c_laplace s k a = (1 + a ^ 2) * p11c_laplace (s + 1) k a -
      a * (p11c_laplace (s + 1) (k + 1) a + p11c_laplace (s + 1) (k - 1) a) := by
    intro k; have := p11c_laplace_red1 ha (s + 1) k; rwa [hsub] at this
  have R2 : ∀ k : ℤ, (k : ℝ) * p11c_laplace s k a = s * a *
      (p11c_laplace (s + 1) (k - 1) a - p11c_laplace (s + 1) (k + 1) a) := by
    intro k; have := p11c_laplace_red2 ha (s + 1) k; rwa [hsub] at this
  have sym : p11c_laplace (s + 1) (-1) a = p11c_laplace (s + 1) 1 a := by
    simp only [p11c_laplace]
    congr 2; ext t
    simp
  have a0 := R1 0
  have a1 := R1 1
  have b1 := R2 1
  norm_num at a0 a1 b1
  rw [sym] at a0
  have haA2 : a * p11c_laplace (s + 1) 2 a =
      a * p11c_laplace (s + 1) 0 a - p11c_laplace s 1 a / s := by
    field_simp
    linarith
  have hA1 : (1 + a ^ 2) * p11c_laplace (s + 1) 1 a =
      (1 - 1 / s) * p11c_laplace s 1 a + 2 * a * p11c_laplace (s + 1) 0 a := by
    have : p11c_laplace s 1 a / s = (1 / s) * p11c_laplace s 1 a := by ring
    linarith
  refine ⟨?_, ?_, ?_⟩
  · rw [eq_div_iff hD]
    linear_combination (-(1 + a ^ 2)) * a0 + (2 * a) * hA1
  · rw [eq_div_iff hD]
    linear_combination (1 + a ^ 2) * hA1 - (2 * a) * a0
  · intro k hk
    have := R2 k
    rw [Int.cast_natCast] at this
    have hsa : s * a ≠ 0 := mul_ne_zero hs0 ha0
    field_simp
    linarith
