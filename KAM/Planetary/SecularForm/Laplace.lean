/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.SecularForm.Basic
public import KAM.Planetary.SecularForm.LaplacePoch
public import KAM.Planetary.SecularForm.LaplaceSeries
public import KAM.Planetary.SecularForm.LaplaceCoeff

/-!
# Secular form: Laplace coefficients

Blueprint P, Part 8 (`bpP:p8:laplace-def`, `bpP:p8:laplace`, `stepP:p8:la-exp`,
`stepP:p8:la-conv`): the exports `laplace` and `laplace_fourier` (the definitions `laplace_def`,
`poch`, `laplaceTerm`, `laplaceC` and `e_poch` live in the imported focused modules).
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter Real Function
open scoped BigOperators Topology
namespace KAM.Planetary
open KAM KAM.Kepler

namespace SecularForm

theorem laplaceTerm_nonneg {s : ℝ} (hs : 0 < s) {α : ℝ} (hα : 0 ≤ α) (k q : ℕ) :
    0 ≤ laplaceTerm s k q α := by
  rw [laplaceTerm_eq_kernelWeight]; exact kernelWeight_nonneg hs hα _

theorem laplaceTerm_pos {s : ℝ} (hs : 0 < s) {α : ℝ} (hα : 0 < α) (k q : ℕ) :
    0 < laplaceTerm s k q α := by
  rw [laplaceTerm_eq_kernelWeight]
  have := pcoef_pos hs (q + k)
  have := pcoef_pos hs q
  unfold kernelWeight; positivity

theorem laplaceTerm_eq_coef_mul (s : ℝ) (k q : ℕ) (r : ℝ) :
    laplaceTerm s k q r =
      (poch s (q+k) * poch s q / ((q+k).factorial * q.factorial) : ℝ) * r^(2*q+k) := rfl

theorem laplace_def_neg (s : ℝ) (k : ℤ) (α : ℝ) : laplace_def s (-k) α = laplace_def s k α := by
  unfold laplace_def
  congr 1
  refine intervalIntegral.integral_congr fun t _ => ?_
  simp [Real.cos_neg, neg_mul]

theorem laplace_def_zero (s : ℝ) (k : ℕ) :
    laplace_def s k 0 = if k = 0 then 1 else 0 := by
  have h0 := integral_cos_int_mul (k : ℤ)
  have h : ∀ t : ℝ, (1 + (0:ℝ)^2 - 2*0*Real.cos t) ^ (-s) = 1 := fun t => by simp
  unfold laplace_def
  simp only [h, mul_one]
  rw [h0]
  have hπ : (2*π) ≠ 0 := by positivity
  by_cases hk : k = 0
  · subst hk; simp; field_simp
  · simp [hk]

theorem differentiableOn_laplaceC {s : ℝ} (hs : 0 < s) (k : ℕ) :
    DifferentiableOn ℂ (laplaceC s k) (Metric.ball 0 1) := by
  intro z hz
  have hz' : ‖z‖ < 1 := by simpa using hz
  set r : ℝ := (‖z‖ + 1) / 2 with hr
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := by rw [hr]; linarith
  have hzr : ‖z‖ < r := by rw [hr]; linarith
  have hsum := (hasSum_laplaceTerm hs hr0 hr1 k).summable
  have hd : DifferentiableOn ℂ (laplaceC s k) (Metric.ball 0 r) := by
    unfold laplaceC
    refine Complex.differentiableOn_tsum_of_summable_norm (u := fun q => laplaceTerm s k q r) hsum
      (fun q => ?_) Metric.isOpen_ball (fun q w hw => ?_)
    · fun_prop
    · have hw' : ‖w‖ < r := by simpa using hw
      rw [norm_mul, norm_pow, Complex.norm_real, laplaceTerm_eq_coef_mul]
      have h0 : 0 ≤ (poch s (q+k) * poch s q / ((q+k).factorial * q.factorial) : ℝ) := by
        have := poch_nonneg hs (q+k); have := poch_nonneg hs q; positivity
      rw [Real.norm_of_nonneg h0]
      gcongr
  exact (hd.differentiableAt
    (Metric.isOpen_ball.mem_nhds (by simpa using hzr))).differentiableWithinAt

theorem laplaceC_ofReal {s : ℝ} (hs : 0 < s) (k : ℕ) {α : ℝ} (hα : 0 ≤ α) (hα1 : α < 1) :
    laplaceC s k (α : ℂ) = (laplace_def s k α : ℂ) := by
  rw [← (hasSum_laplaceTerm hs hα hα1 k).tsum_eq, Complex.ofReal_tsum]
  unfold laplaceC
  refine tsum_congr fun q => ?_
  rw [laplaceTerm_eq_coef_mul]; push_cast; rfl

theorem analyticOnNhd_laplace_def {s : ℝ} (hs : 0 < s) (k : ℕ) :
    AnalyticOnNhd ℝ (laplace_def s k) (Ioo 0 1) := by
  have hC : AnalyticOnNhd ℂ (laplaceC s k) (Metric.ball 0 1) :=
    (differentiableOn_laplaceC hs k).analyticOnNhd Metric.isOpen_ball
  have h1 : AnalyticOnNhd ℝ (fun x : ℝ => Complex.re (laplaceC s k (x : ℂ))) (Ioo 0 1) := by
    intro x hx
    have hxb : (x : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by
      simp [abs_of_pos hx.1, hx.2]
    have a1 : AnalyticAt ℝ (laplaceC s k) (x : ℂ) := (hC _ hxb).restrictScalars
    have a2 : AnalyticAt ℝ (fun x : ℝ => (x : ℂ)) x := Complex.ofRealCLM.analyticAt x
    exact Complex.reCLM.analyticAt _ |>.comp (a1.comp a2)
  refine h1.congr isOpen_Ioo fun x hx => ?_
  rw [laplaceC_ofReal hs k hx.1.le hx.2, Complex.ofReal_re]

theorem laplace {s : ℝ} (hs : 0 < s) (k : ℕ) {α : ℝ} (hα : 0 ≤ α) (hα1 : α < 1) :
    HasSum (fun q => laplaceTerm s k q α) (laplace_def s k α) ∧
    laplace_def s (-(k : ℤ)) α = laplace_def s k α ∧
    0 ≤ laplace_def s k α ∧
    (0 < α → 0 < laplace_def s k α) ∧
    laplace_def s k 0 = (if k = 0 then 1 else 0) ∧
    DifferentiableOn ℂ (laplaceC s k) (Metric.ball 0 1) ∧
    laplaceC s k (α : ℂ) = (laplace_def s k α : ℂ) ∧
    AnalyticOnNhd ℝ (laplace_def s k) (Ioo 0 1) := by
  have H := hasSum_laplaceTerm hs hα hα1 k
  refine ⟨H, laplace_def_neg s k α, H.nonneg (laplaceTerm_nonneg hs hα k), fun hpos => ?_,
    laplace_def_zero s k, differentiableOn_laplaceC hs k, laplaceC_ofReal hs k hα hα1,
    analyticOnNhd_laplace_def hs k⟩
  rw [← H.tsum_eq]
  exact H.summable.tsum_pos (laplaceTerm_nonneg hs hα k) 0 (laplaceTerm_pos hs hpos k 0)

theorem laplace_fourier {s α : ℝ} (hs : 0 < s) (hα : 0 ≤ α) (hα1 : α < 1) (t : ℝ) :
    HasSum (fun k : ℤ => (laplace_def s k α : ℂ) * Complex.exp ((k : ℂ)*(t : ℂ)*Complex.I))
      ((1+α^2-2*α*Real.cos t)^(-s) : ℝ) := by
  have H := (hasSum_kernel_complex hs hα hα1 t).tsum_fiberwise freq
  convert H using 1
  ext k
  have e : ∀ p ∈ freq ⁻¹' {k}, (kernelWeight s α p : ℂ) *
      Complex.exp (((p.1 : ℂ) - p.2) * t * Complex.I) =
      (kernelWeight s α p : ℂ) * Complex.exp ((k : ℂ) * t * Complex.I) := by
    intro p hp
    have : ((p.1 : ℂ) - p.2) = (k : ℂ) := by
      have h : freq p = k := hp
      rw [freq] at h
      exact_mod_cast h
    rw [this]
  rw [tsum_congr fun p : freq ⁻¹' {k} => e p p.2, tsum_mul_right, ← Complex.ofReal_tsum,
    tsum_subtype (freq ⁻¹' {k}) (kernelWeight s α)]
  congr 2
  rw [← (laplace_def_eq_tsum hs hα hα1 k).tsum_eq]
  refine tsum_congr fun p => ?_
  simp [Set.indicator, freqWeight]

end SecularForm
end KAM.Planetary
