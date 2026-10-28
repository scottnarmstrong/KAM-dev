/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.SecularForm.LaplaceIdentities

/-!
# Secular form: scaling and analyticity of the radial function

Blueprint P, Part 8, `stepP:p8:qf-scale`: the radial function
`Φ(r₁, r₂) = (2π)⁻¹ ∫ (r₁² + r₂² - 2 r₁ r₂ cos t)^{-1/2} dt` is symmetric, homogeneous of degree
`-1`, equal to `r₂⁻¹ b_{1/2}^{(0)}(r₁/r₂)` for `r₁ < r₂`, and real analytic off the diagonal
`r₁ = r₂` (on positive radii).
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter Real Function
open scoped BigOperators Topology
namespace KAM.Planetary
open KAM KAM.Kepler

namespace SecularForm

/-- The radial integrand base `r₁² + r₂² - 2 r₁ r₂ cos t` is nonnegative. -/
theorem radial_base_nonneg (a b t : ℝ) : 0 ≤ a ^ 2 + b ^ 2 - 2 * a * b * Real.cos t := by
  nlinarith [mul_nonneg (by linarith [Real.neg_one_le_cos t] : (0:ℝ) ≤ 1 + Real.cos t)
      (sq_nonneg (a - b)),
    mul_nonneg (by linarith [Real.cos_le_one t] : (0:ℝ) ≤ 1 - Real.cos t) (sq_nonneg (a + b))]

/-- `stepP:p8:qf-scale`: symmetry of `Φ`. -/
theorem radialPhi_comm (a b : ℝ) : radialPhi a b = radialPhi b a := by
  unfold radialPhi
  congr 1
  refine intervalIntegral.integral_congr fun t _ => ?_
  rw [show a ^ 2 + b ^ 2 - 2 * a * b * Real.cos t = b ^ 2 + a ^ 2 - 2 * b * a * Real.cos t by ring]

/-- `stepP:p8:qf-scale`: homogeneity of degree `-1`. -/
theorem radialPhi_smul {c : ℝ} (hc : 0 < c) (a b : ℝ) :
    radialPhi (c * a) (c * b) = c⁻¹ * radialPhi a b := by
  unfold radialPhi
  have hc2 : (c ^ 2) ^ (-1 / 2 : ℝ) = c⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hc.le]
    norm_num [Real.rpow_neg_one]
  have : ∀ t ∈ Set.uIcc (0:ℝ) (2 * π),
      ((c * a) ^ 2 + (c * b) ^ 2 - 2 * (c * a) * (c * b) * Real.cos t) ^ (-1 / 2 : ℝ) =
        c⁻¹ * (a ^ 2 + b ^ 2 - 2 * a * b * Real.cos t) ^ (-1 / 2 : ℝ) := fun t _ => by
    rw [show (c * a) ^ 2 + (c * b) ^ 2 - 2 * (c * a) * (c * b) * Real.cos t =
      c ^ 2 * (a ^ 2 + b ^ 2 - 2 * a * b * Real.cos t) by ring,
      Real.mul_rpow (by positivity) (radial_base_nonneg a b t), hc2]
  rw [intervalIntegral.integral_congr this, intervalIntegral.integral_const_mul]
  ring

/-- `stepP:p8:qf-scale`: for `0 < a < b`, `Φ(a, b) = b⁻¹ b_{1/2}^{(0)}(a/b)`. -/
theorem radialPhi_eq_laplace {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    radialPhi a b = b⁻¹ * laplace_def (1/2) 0 (a / b) := by
  have hb : 0 < b := ha.trans hab
  have h := radialPhi_smul (inv_pos.2 hb) a b
  rw [show b⁻¹ * b = 1 by field_simp, ] at h
  have h1 : radialPhi (b⁻¹ * a) 1 = b * radialPhi a b := by
    rw [h, inv_inv]
  have h2 : radialPhi (b⁻¹ * a) 1 = laplace_def (1/2) 0 (a / b) := by
    unfold radialPhi laplace_def
    congr 1
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [Int.cast_zero, zero_mul, Real.cos_zero, one_mul]
    rw [show -(1 / 2 : ℝ) = -1 / 2 by norm_num]
    congr 1
    rw [inv_mul_eq_div]; ring
  field_simp
  rw [← h2, h1]
  field_simp

/-- Analyticity of the explicit Laplace form `p ↦ p₂⁻¹ b_{1/2}^{(0)}(p₁/p₂)` where `0 < p₁ < p₂`. -/
theorem analyticAt_laplaceForm {p : ℝ × ℝ} (h1 : 0 < p.1) (h12 : p.1 < p.2) :
    AnalyticAt ℝ (fun q : ℝ × ℝ => q.2⁻¹ * laplace_def (1/2) 0 (q.1 / q.2)) p := by
  have h2 : p.2 ≠ 0 := (h1.trans h12).ne'
  have hq : AnalyticAt ℝ (fun q : ℝ × ℝ => q.1 / q.2) p :=
    analyticAt_fst.div analyticAt_snd h2
  have hb : AnalyticAt ℝ (laplace_def (1/2) 0) (p.1 / p.2) :=
    (analyticOnNhd_laplace_def (by norm_num) 0) _ ⟨div_pos h1 (h1.trans h12),
      (div_lt_one (h1.trans h12)).2 h12⟩
  exact (analyticAt_snd.inv h2).mul (hb.comp_of_eq hq rfl)

/-- `stepP:p8:qf-scale`: `Φ` is real analytic on `{0 < r₁, 0 < r₂, r₁ ≠ r₂}`. -/
theorem analyticOnNhd_radialPhi :
    AnalyticOnNhd ℝ (fun p : ℝ × ℝ => radialPhi p.1 p.2)
      {p : ℝ × ℝ | 0 < p.1 ∧ 0 < p.2 ∧ p.1 ≠ p.2} := by
  rintro p ⟨h1, h2, hne⟩
  rcases lt_or_gt_of_ne hne with h | h
  · refine (analyticAt_laplaceForm h1 h).congr ?_
    have : {q : ℝ × ℝ | 0 < q.1 ∧ q.1 < q.2} ∈ 𝓝 p :=
      (isOpen_lt continuous_const continuous_fst).inter
        (isOpen_lt continuous_fst continuous_snd) |>.mem_nhds ⟨h1, h⟩
    filter_upwards [this] with q hq
    exact (radialPhi_eq_laplace hq.1 hq.2).symm
  · have h1' : p.1 ≠ 0 := h1.ne'
    have hq : AnalyticAt ℝ (fun q : ℝ × ℝ => q.2 / q.1) p :=
      analyticAt_snd.div analyticAt_fst h1'
    have hb : AnalyticAt ℝ (laplace_def (1/2) 0) (p.2 / p.1) :=
      (analyticOnNhd_laplace_def (by norm_num) 0) _ ⟨div_pos h2 h1,
        (div_lt_one h1).2 h⟩
    have hs : AnalyticAt ℝ (fun q : ℝ × ℝ => q.1⁻¹ * laplace_def (1/2) 0 (q.2 / q.1)) p :=
      (analyticAt_fst.inv h1').mul (hb.comp_of_eq hq rfl)
    refine hs.congr ?_
    have : {q : ℝ × ℝ | 0 < q.2 ∧ q.2 < q.1} ∈ 𝓝 p :=
      (isOpen_lt continuous_const continuous_snd).inter
        (isOpen_lt continuous_snd continuous_fst) |>.mem_nhds ⟨h2, h⟩
    filter_upwards [this] with q hq
    rw [radialPhi_comm]
    exact (radialPhi_eq_laplace hq.1 hq.2).symm

/-- `radialH a b` is real analytic at `0` when `0 < a`, `0 < b`, `a ≠ b`. -/
theorem analyticAt_radialH {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) :
    AnalyticAt ℝ (radialH a b) 0 := by
  have hΦ := analyticOnNhd_radialPhi (a, b) ⟨ha, hb, hab⟩
  have hc : AnalyticAt ℝ (fun ε : ℝ => (a * (1 - ε), b)) 0 :=
    AnalyticAt.prod (by fun_prop) analyticAt_const
  have h := hΦ.comp_of_eq hc (by simp)
  exact h.mul (analyticAt_const.sub analyticAt_id)

private theorem laplace_half_analytic {x : ℝ} (hx : x ∈ Ioo (0:ℝ) 1) :
    AnalyticAt ℝ (laplace_def (1/2) 0) x :=
  analyticOnNhd_laplace_def (by norm_num) 0 x hx

private theorem laplace_half_hasDeriv {x : ℝ} (hx : x ∈ Ioo (0:ℝ) 1) :
    HasDerivAt (laplace_def (1/2) 0) (deriv (laplace_def (1/2) 0) x) x :=
  (laplace_half_analytic hx).differentiableAt.hasDerivAt

private theorem laplace_half_hasDeriv2 {x : ℝ} (hx : x ∈ Ioo (0:ℝ) 1) :
    HasDerivAt (deriv (laplace_def (1/2) 0)) (iteratedDeriv 2 (laplace_def (1/2) 0) x) x := by
  rw [iteratedDeriv_succ, iteratedDeriv_one]
  exact (laplace_half_analytic hx).deriv.differentiableAt.hasDerivAt

private theorem laplace_half_deriv2_eq (β : ℝ → ℝ) (x : ℝ) :
    iteratedDeriv 2 β x = deriv (deriv β) x := by
  rw [iteratedDeriv_succ, iteratedDeriv_one]

/-- `stepP:p8:qf-diag` (inner eccentric orbit): `h''(0) = (a/b²) b_{3/2}^{(1)}(a/b)` for `a < b`. -/
theorem iteratedDeriv_two_radialH_of_lt {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    iteratedDeriv 2 (radialH a b) 0 = a / b ^ 2 * laplace_def (3/2) 1 (a / b) := by
  have hb : 0 < b := ha.trans hab
  set α := a / b with hα
  have hα0 : 0 < α := div_pos ha hb
  have hα1 : α < 1 := (div_lt_one hb).2 hab
  set β := laplace_def (1/2) 0 with hβ
  have hmem : ∀ᶠ ε in 𝓝 (0:ℝ), α * (1 - ε) ∈ Ioo (0:ℝ) 1 := by
    have hc : ContinuousAt (fun ε : ℝ => α * (1 - ε)) 0 := by fun_prop
    exact hc.eventually_mem (isOpen_Ioo.mem_nhds (by simpa using ⟨hα0, hα1⟩))
  let E : ℝ → ℝ := fun ε => b⁻¹ * (β (α * (1 - ε)) * (1 - ε))
  let E' : ℝ → ℝ := fun ε =>
    b⁻¹ * (-α * deriv β (α * (1 - ε)) * (1 - ε) - β (α * (1 - ε)))
  have hEq : radialH a b =ᶠ[𝓝 0] E := by
    filter_upwards [hmem] with ε hε
    have h1 : 0 < a * (1 - ε) := by
      have := hε.1; rwa [hα, div_mul_eq_mul_div, div_pos_iff_of_pos_right hb] at this
    have h2 : a * (1 - ε) < b := by
      have := hε.2; rw [hα, div_mul_eq_mul_div, div_lt_one hb] at this; exact this
    unfold radialH
    rw [radialPhi_eq_laplace h1 h2]
    simp only [E]
    rw [show a * (1 - ε) / b = α * (1 - ε) by rw [hα]; ring]
    simp only [hβ]
    ring
  have hD : ∀ᶠ ε in 𝓝 (0:ℝ), HasDerivAt E (E' ε) ε := by
    filter_upwards [hmem] with ε hε
    have h1 : HasDerivAt (fun ε : ℝ => α * (1 - ε)) (-α) ε := by
      simpa using ((hasDerivAt_id ε).const_sub 1).const_mul α
    have h2 := (laplace_half_hasDeriv hε).comp ε h1
    have h3 := (h2.mul ((hasDerivAt_id ε).const_sub 1)).const_mul b⁻¹
    exact h3.congr_deriv (by simp only [E', id, Function.comp]; ring)
  have hE1 : deriv E =ᶠ[𝓝 0] E' := by
    filter_upwards [hD] with ε hε using hε.deriv
  have hm0 : α * (1 - 0) ∈ Ioo (0:ℝ) 1 := by simpa using ⟨hα0, hα1⟩
  have hE2 : HasDerivAt E' (b⁻¹ * (α ^ 2 * iteratedDeriv 2 β α + 2 * α * deriv β α)) 0 := by
    have h1 : HasDerivAt (fun ε : ℝ => α * (1 - ε)) (-α) 0 := by
      simpa using ((hasDerivAt_id (0:ℝ)).const_sub 1).const_mul α
    have hb1 := (laplace_half_hasDeriv hm0).comp 0 h1
    have hb2 := (laplace_half_hasDeriv2 hm0).comp 0 h1
    have h4 := (((hb2.const_mul (-α)).mul (((hasDerivAt_id (0:ℝ)).const_sub 1))).sub hb1).const_mul b⁻¹
    exact h4.congr_deriv (g' := b⁻¹ * (α ^ 2 * iteratedDeriv 2 β α + 2 * α * deriv β α))
      (by simp only [id, Function.comp, sub_zero, mul_one, hβ]; ring)
  have hfin : iteratedDeriv 2 (radialH a b) 0 = deriv (deriv E) 0 := by
    rw [laplace_half_deriv2_eq, hEq.deriv.deriv_eq]
  rw [hfin, hE1.deriv_eq, hE2.deriv]
  have hid := (identities hα0 hα1).1
  have : α ^ 2 * iteratedDeriv 2 β α + 2 * α * deriv β α = α * laplace_def (3/2) 1 α := hid
  rw [this, hα]
  field_simp

end SecularForm
end KAM.Planetary
end
