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

end SecularForm
end KAM.Planetary
end
