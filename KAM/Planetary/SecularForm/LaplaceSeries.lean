/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.SecularForm.LaplacePoch

/-!
# Secular form: the double series of the Laplace kernel

Blueprint P, Part 8 (`stepP:p8:la-exp`): for `0 ≤ α < 1` and `s > 0`, the kernel
`(1+α²-2α cos t)^(-s)` equals `∑_{a,b} c_a c_b α^(a+b) e^{i(a-b)t}` with `c_q = poch s q / q!`,
absolutely summable over `ℕ × ℕ`.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter Real Function
open scoped BigOperators Topology
namespace KAM.Planetary
open KAM KAM.Kepler

namespace SecularForm

/-- The Taylor coefficient `poch s q / q!` of `(1-z)^(-s)`. -/
def pcoef (s : ℝ) (q : ℕ) : ℝ := poch s q / q.factorial

/-- The double-series weight `c_a c_b α^(a+b)`. -/
def kernelWeight (s α : ℝ) (p : ℕ × ℕ) : ℝ := pcoef s p.1 * pcoef s p.2 * α ^ (p.1 + p.2)

theorem pcoef_nonneg {s : ℝ} (hs : 0 < s) (q : ℕ) : 0 ≤ pcoef s q :=
  div_nonneg (poch_nonneg hs q) (Nat.cast_nonneg _)

theorem pcoef_pos {s : ℝ} (hs : 0 < s) (q : ℕ) : 0 < pcoef s q :=
  div_pos (poch_pos hs q) (by exact_mod_cast q.factorial_pos)

theorem summable_pcoef_mul_pow {s α : ℝ} (_hs : 0 < s) (hα : 0 ≤ α) (hα1 : α < 1) :
    Summable (fun q : ℕ => pcoef s q * α ^ q) :=
  (poch_binomial (s := s) α (by rwa [abs_of_nonneg hα])).summable

theorem kernelWeight_nonneg {s α : ℝ} (hs : 0 < s) (hα : 0 ≤ α) (p : ℕ × ℕ) :
    0 ≤ kernelWeight s α p := by
  have := pcoef_nonneg hs p.1
  have := pcoef_nonneg hs p.2
  unfold kernelWeight; positivity

theorem summable_kernelWeight {s α : ℝ} (hs : 0 < s) (hα : 0 ≤ α) (hα1 : α < 1) :
    Summable (kernelWeight s α) := by
  have h := summable_pcoef_mul_pow hs hα hα1
  have := Summable.mul_of_nonneg h h (fun q => mul_nonneg (pcoef_nonneg hs q) (pow_nonneg hα q))
    (fun q => mul_nonneg (pcoef_nonneg hs q) (pow_nonneg hα q))
  refine this.congr fun p => ?_
  simp only [kernelWeight, pow_add]; ring

theorem kernelWeight_swap (s α : ℝ) (p : ℕ × ℕ) :
    kernelWeight s α p.swap = kernelWeight s α p := by
  simp [kernelWeight, add_comm, mul_comm]

/-- The complex binomial series, as a `HasSum` over `ℕ`. -/
theorem hasSum_cpow_series {s : ℝ} (z : ℂ) (hz : ‖z‖ < 1) :
    HasSum (fun q : ℕ => (pcoef s q : ℂ) * z ^ q) (1 / (1 - z) ^ (s : ℂ)) := by
  have H := (Complex.one_div_one_sub_cpow_hasFPowerSeriesOnBall_zero (s : ℂ)).hasSum
    (y := z) (by
      rw [Metric.mem_eball, edist_dist]
      exact ENNReal.ofReal_lt_one.2 (by simpa using hz))
  simp only [zero_add] at H
  convert H using 1
  ext q
  simp only [FormalMultilinearSeries.ofScalars, smul_eq_mul, smul_apply]
  have hc : Ring.choose ((s : ℂ) + q - 1) q = (pcoef s q : ℂ) := by
    have := congrArg (fun r : ℝ => (r : ℂ)) (choose_eq_poch_div s q)
    simp only [pcoef]
    rw [← this, Complex.ofReal_choose]
    push_cast; rfl
  simp [hc]

theorem kernelBase_norm_sq (α t : ℝ) :
    ‖(1 : ℂ) - α * Complex.exp (t * Complex.I)‖ ^ 2 = 1 + α ^ 2 - 2 * α * Real.cos t := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  nlinarith [Real.sin_sq_add_cos_sq t]

theorem kernelBase_re_pos {α : ℝ} (hα : 0 ≤ α) (hα1 : α < 1) (t : ℝ) :
    0 < ((1 : ℂ) - α * Complex.exp (t * Complex.I)).re := by
  simp [Complex.exp_ofReal_mul_I_re]
  nlinarith [Real.cos_le_one t, Real.neg_one_le_cos t]

/-- `stepP:p8:la-exp`: the complex double-series expansion of the Laplace kernel. -/
theorem hasSum_kernel_complex {s α : ℝ} (hs : 0 < s) (hα : 0 ≤ α) (hα1 : α < 1) (t : ℝ) :
    HasSum (fun p : ℕ × ℕ => (kernelWeight s α p : ℂ) *
        Complex.exp (((p.1 : ℂ) - p.2) * t * Complex.I))
      (((1 + α ^ 2 - 2 * α * Real.cos t) ^ (-s) : ℝ) : ℂ) := by
  set w : ℂ := Complex.exp (t * Complex.I) with hw
  set w' : ℂ := Complex.exp (-(t * Complex.I)) with hw'
  have hnw : ‖w‖ = 1 := by rw [hw]; exact Complex.norm_exp_ofReal_mul_I t
  have hnw' : ‖w'‖ = 1 := by
    have := Complex.norm_exp_ofReal_mul_I (-t)
    simpa using this
  have hz1 : ‖(α : ℂ) * w‖ < 1 := by
    rw [norm_mul, hnw, mul_one, Complex.norm_real, Real.norm_of_nonneg hα]; exact hα1
  have hz2 : ‖(α : ℂ) * w'‖ < 1 := by
    rw [norm_mul, hnw', mul_one, Complex.norm_real, Real.norm_of_nonneg hα]; exact hα1
  have hX := hasSum_cpow_series (s := s) _ hz1
  have hY := hasSum_cpow_series (s := s) _ hz2
  have hsum : Summable (fun p : ℕ × ℕ =>
      ((pcoef s p.1 : ℂ) * ((α : ℂ) * w) ^ p.1) * ((pcoef s p.2 : ℂ) * ((α : ℂ) * w') ^ p.2)) := by
    refine Summable.of_norm ((summable_kernelWeight hs hα hα1).congr fun p => ?_)
    simp only [norm_mul, mul_pow, norm_pow, hnw, hnw', Complex.norm_real, one_pow, mul_one,
      Real.norm_of_nonneg hα, Real.norm_of_nonneg (pcoef_nonneg hs _), kernelWeight, pow_add]
    ring
  have H := hX.mul hY hsum
  have hterm : ∀ p : ℕ × ℕ,
      ((pcoef s p.1 : ℂ) * ((α : ℂ) * w) ^ p.1) * ((pcoef s p.2 : ℂ) * ((α : ℂ) * w') ^ p.2) =
      (kernelWeight s α p : ℂ) * Complex.exp (((p.1 : ℂ) - p.2) * t * Complex.I) := by
    intro p
    have e1 : w ^ p.1 = Complex.exp (p.1 * (t * Complex.I)) := by
      rw [hw, ← Complex.exp_nat_mul]
    have e2 : w' ^ p.2 = Complex.exp (-(p.2 * (t * Complex.I))) := by
      rw [hw', ← Complex.exp_nat_mul]; congr 1; ring
    have e3 : Complex.exp (((p.1 : ℂ) - p.2) * t * Complex.I) =
        Complex.exp (p.1 * (t * Complex.I)) * Complex.exp (-(p.2 * (t * Complex.I))) := by
      rw [← Complex.exp_add]; congr 1; ring
    rw [e3, mul_pow, mul_pow, e1, e2]
    simp only [kernelWeight, pow_add]
    push_cast
    ring
  simp only [hterm] at H
  convert H using 1
  -- value
  set x : ℂ := 1 - (α : ℂ) * w with hx
  have hxre : 0 < x.re := kernelBase_re_pos hα hα1 t
  have hx0 : x ≠ 0 := fun h => by rw [h] at hxre; simp at hxre
  have hxarg : x.arg ≠ π := by
    rw [Ne, Complex.arg_eq_pi_iff]; intro h; linarith [h.1]
  have hconj : (starRingEnd ℂ) x = 1 - (α : ℂ) * w' := by
    rw [hx, map_sub, map_one, map_mul, Complex.conj_ofReal, hw, hw', ← Complex.exp_conj]
    simp
  have hcp : (starRingEnd ℂ) (x ^ (s : ℂ)) = (1 - (α : ℂ) * w') ^ (s : ℂ) := by
    rw [← hconj, Complex.conj_cpow _ _ hxarg]; simp
  have hY' : 1 / (1 - (α : ℂ) * w') ^ (s : ℂ) = (starRingEnd ℂ) (1 / x ^ (s : ℂ)) := by
    rw [map_div₀, map_one, hcp]
  rw [hY', Complex.mul_conj', one_div, norm_inv, Complex.norm_cpow_real]
  have hu : 0 < ‖x‖ := norm_pos_iff.2 hx0
  have hsq : ‖x‖ ^ 2 = 1 + α ^ 2 - 2 * α * Real.cos t := kernelBase_norm_sq α t
  rw [← hsq, Real.rpow_neg (by positivity), ← Real.rpow_pow_comm hu.le]
  push_cast
  simp

end SecularForm
end KAM.Planetary
