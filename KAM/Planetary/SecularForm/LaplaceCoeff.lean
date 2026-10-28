/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.SecularForm.LaplaceSeries

/-!
# Secular form: Laplace coefficients as series

Blueprint P, Part 8 (`bpP:p8:laplace-def`, `stepP:p8:la-conv`): the Laplace coefficient
`laplace_def s k α` (the cosine Fourier coefficient of `(1+α²-2α cos t)^(-s)`), its definition by
the integral, the series `laplaceTerm`, and the identification
`laplace_def s k α = ∑_q laplaceTerm s |k| q α`.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter Real Function
open scoped BigOperators Topology
namespace KAM.Planetary
open KAM KAM.Kepler

namespace SecularForm

def laplace_def (s : ℝ) (k : ℤ) (α : ℝ) : ℝ :=
  (2*π)⁻¹ * ∫ t in (0 : ℝ)..2*π,
    Real.cos ((k : ℝ)*t) * (1+α^2-2*α*Real.cos t) ^ (-s)
def laplaceTerm (s : ℝ) (k q : ℕ) (α : ℝ) : ℝ :=
  poch s (q+k) * poch s q / ((q+k).factorial * q.factorial) * α^(2*q+k)
def laplaceC (s : ℝ) (k : ℕ) (z : ℂ) : ℂ :=
  ∑' q : ℕ, (poch s (q+k) * poch s q / ((q+k).factorial * q.factorial) : ℝ) * z^(2*q+k)

/-- The integer frequency `a - b` of an index pair. -/
def freq (p : ℕ × ℕ) : ℤ := (p.1 : ℤ) - p.2

/-- The weight restricted to frequency `k`. -/
def freqWeight (s α : ℝ) (k : ℤ) (p : ℕ × ℕ) : ℝ := if freq p = k then kernelWeight s α p else 0

theorem integral_cos_int_mul (n : ℤ) :
    ∫ t in (0 : ℝ)..2*π, Real.cos ((n : ℝ) * t) = if n = 0 then 2*π else 0 := by
  split_ifs with h
  · subst h; simp
  · have hn : (n : ℝ) ≠ 0 := by exact_mod_cast h
    rw [intervalIntegral.integral_comp_mul_left (fun x => Real.cos x) hn, integral_cos]
    have : Real.sin ((n : ℝ) * (2*π)) = 0 := by
      have := Real.sin_int_mul_pi (2*n)
      rw [show ((n : ℝ) * (2*π)) = ((2*n : ℤ) : ℝ) * π by push_cast; ring]; exact this
    simp [this]

theorem integral_cos_mul_cos (k m : ℤ) :
    (2*π)⁻¹ * ∫ t in (0 : ℝ)..2*π, Real.cos ((k : ℝ)*t) * Real.cos ((m : ℝ)*t) =
      ((if m = k then 1 else 0) + (if m = -k then 1 else 0)) / 2 := by
  have h : ∀ t : ℝ, Real.cos ((k : ℝ)*t) * Real.cos ((m : ℝ)*t) =
      (Real.cos (((k+m : ℤ) : ℝ)*t) + Real.cos (((k-m : ℤ) : ℝ)*t)) / 2 := by
    intro t
    rw [show ((k+m : ℤ) : ℝ)*t = (k:ℝ)*t + (m:ℝ)*t by push_cast; ring,
      show ((k-m : ℤ) : ℝ)*t = (k:ℝ)*t - (m:ℝ)*t by push_cast; ring,
      Real.cos_add, Real.cos_sub]; ring
  simp only [h]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_add
    (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop),
    integral_cos_int_mul, integral_cos_int_mul]
  have hπ : (2*π) ≠ 0 := by positivity
  by_cases h1 : m = -k <;> by_cases h2 : m = k
  · have : k = 0 := by omega
    subst this; simp at h1 h2 ⊢; field_simp
  · have e1 : k + m = 0 := by omega
    have e2 : ¬ (k - m = 0) := by omega
    have e3 : k ≠ 0 := by omega
    simp [h1, h2, e1, e2, e3]
    have e4 : ¬ (-k = k) := by omega
    simp [e4]; field_simp
  · have e1 : ¬ (k + m = 0) := by omega
    have e2 : k - m = 0 := by omega
    have e3 : k ≠ 0 := by omega
    simp [h1, h2, e1, e2, e3]
    have e4 : ¬ (k = -k) := by omega
    simp [e4]; field_simp
  · have e1 : ¬ (k + m = 0) := by omega
    have e2 : ¬ (k - m = 0) := by omega
    simp [h1, h2, e1, e2]

theorem hasSum_kernel_real {s α : ℝ} (hs : 0 < s) (hα : 0 ≤ α) (hα1 : α < 1) (t : ℝ) :
    HasSum (fun p : ℕ × ℕ => kernelWeight s α p * Real.cos ((freq p : ℝ) * t))
      ((1 + α ^ 2 - 2 * α * Real.cos t) ^ (-s)) := by
  have H := (Complex.hasSum_re (hasSum_kernel_complex hs hα hα1 t))
  simp only [Complex.ofReal_re] at H
  convert H using 1
  ext p
  have : ((p.1 : ℂ) - p.2) * t * Complex.I = (((freq p : ℝ) * t : ℝ) : ℂ) * Complex.I := by
    simp [freq]
  rw [this, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]

theorem hasSum_freqWeight_pair {s α : ℝ} (hs : 0 < s) (hα : 0 ≤ α) (hα1 : α < 1) (k : ℤ) :
    HasSum (fun p : ℕ × ℕ => kernelWeight s α p *
      (((if freq p = k then 1 else 0) + (if freq p = -k then 1 else 0)) / 2))
      (laplace_def s k α) := by
  have hF := intervalIntegral.hasSum_integral_of_dominated_convergence
    (μ := volume) (a := 0) (b := 2*π)
    (F := fun (p : ℕ × ℕ) (t : ℝ) => kernelWeight s α p *
      (Real.cos ((k : ℝ) * t) * Real.cos ((freq p : ℝ) * t)))
    (f := fun t => Real.cos ((k : ℝ)*t) * (1+α^2-2*α*Real.cos t) ^ (-s))
    (fun p _ => kernelWeight s α p) (by
      intro p; apply Continuous.aestronglyMeasurable; fun_prop)
    (by
      intro p; refine Filter.Eventually.of_forall fun t _ => ?_
      rw [norm_mul, Real.norm_of_nonneg (kernelWeight_nonneg hs hα p), norm_mul]
      have := Real.abs_cos_le_one ((k : ℝ) * t)
      have := Real.abs_cos_le_one ((freq p : ℝ) * t)
      simp only [Real.norm_eq_abs]
      have h0 : 0 ≤ kernelWeight s α p := kernelWeight_nonneg hs hα p
      calc kernelWeight s α p * (|Real.cos ((k : ℝ) * t)| * |Real.cos ((freq p : ℝ) * t)|)
          ≤ kernelWeight s α p * (1 * 1) := by gcongr
        _ = _ := by ring)
    (Filter.Eventually.of_forall fun _ _ => summable_kernelWeight hs hα hα1)
    intervalIntegrable_const
    (Filter.Eventually.of_forall fun t _ => by
      have := (hasSum_kernel_real hs hα hα1 t).mul_left (Real.cos ((k : ℝ) * t))
      convert this using 2 with p
      ring)
  convert hF.mul_left ((2*π)⁻¹) using 1
  · ext p
    rw [intervalIntegral.integral_const_mul, ← mul_assoc, mul_comm _ (kernelWeight s α p),
      mul_assoc, integral_cos_mul_cos]
  · rfl
theorem summable_freqWeight {s α : ℝ} (hs : 0 < s) (hα : 0 ≤ α) (hα1 : α < 1) (k : ℤ) :
    Summable (freqWeight s α k) := by
  refine Summable.of_nonneg_of_le (fun p => ?_) (fun p => ?_) (summable_kernelWeight hs hα hα1)
  · unfold freqWeight; split_ifs
    · exact kernelWeight_nonneg hs hα p
    · exact le_rfl
  · unfold freqWeight; split_ifs
    · exact le_rfl
    · exact kernelWeight_nonneg hs hα p

theorem freqWeight_neg_swap (s α : ℝ) (k : ℤ) (p : ℕ × ℕ) :
    freqWeight s α (-k) p.swap = freqWeight s α k p := by
  have : freq p.swap = -freq p := by simp [freq]
  unfold freqWeight
  rw [this, kernelWeight_swap]
  simp

theorem tsum_freqWeight_neg (s α : ℝ) (k : ℤ) :
    ∑' p, freqWeight s α (-k) p = ∑' p, freqWeight s α k p := by
  rw [← (Equiv.prodComm ℕ ℕ).tsum_eq]
  exact tsum_congr fun p => freqWeight_neg_swap s α k p

theorem laplace_def_eq_tsum {s α : ℝ} (hs : 0 < s) (hα : 0 ≤ α) (hα1 : α < 1) (k : ℤ) :
    HasSum (freqWeight s α k) (laplace_def s k α) := by
  have h1 := hasSum_freqWeight_pair hs hα hα1 k
  have h2 := ((summable_freqWeight hs hα hα1 k).hasSum.add
    (summable_freqWeight hs hα hα1 (-k)).hasSum).div_const 2
  have h3 := h1.unique (by
    convert h2 using 1
    ext p
    unfold freqWeight; split_ifs <;> ring)
  rw [(summable_freqWeight hs hα hα1 k).hasSum.tsum_eq, (summable_freqWeight hs hα hα1 (-k)).hasSum.tsum_eq, tsum_freqWeight_neg] at h3
  have : laplace_def s k α = ∑' p, freqWeight s α k p := by linarith
  rw [this]; exact (summable_freqWeight hs hα hα1 k).hasSum

theorem laplaceTerm_eq_kernelWeight (s α : ℝ) (k q : ℕ) :
    laplaceTerm s k q α = kernelWeight s α (q + k, q) := by
  simp only [laplaceTerm, kernelWeight, pcoef]
  rw [show 2 * q + k = q + k + q by ring]
  field_simp

theorem hasSum_laplaceTerm {s α : ℝ} (hs : 0 < s) (hα : 0 ≤ α) (hα1 : α < 1) (k : ℕ) :
    HasSum (fun q => laplaceTerm s k q α) (laplace_def s k α) := by
  have hinj : Function.Injective (fun q : ℕ => (q + k, q)) := fun a b h => by
    simpa using congrArg Prod.snd h
  have H := (hinj.hasSum_iff (f := freqWeight s α (k : ℤ)) (a := laplace_def s k α) (by
    intro p hp
    unfold freqWeight
    rw [ite_eq_right_iff]
    intro h
    exfalso
    apply hp
    refine ⟨p.2, ?_⟩
    have : p.1 = p.2 + k := by simp [freq] at h; omega
    ext <;> simp [this]
    )).2 (laplace_def_eq_tsum hs hα hα1 k)
  convert H using 1
  ext q
  rw [laplaceTerm_eq_kernelWeight]
  simp [freqWeight, freq]

end SecularForm
end KAM.Planetary
