/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Measure.OpenPos
public import KAM.Frozen.Wave.Defs.SineMode

/-!
# Completeness of the sine system (blueprint `bpW:w1:sine-completeness`)

Infrastructure used by several nodes; the dependency graph is still being built.

If `f ∈ L²(0, π)` and `∫₀^π f φ_l = 0` for all `l ≥ 1` (`φ_l = KAM.Wave.sineMode l`), then `f = 0`
almost everywhere on `(0, π)` (`KAM.Wave.ae_eq_zero_of_integral_sineMode_eq_zero`); if moreover
`f` is continuous on `[0, π]` then `f = 0` there
(`KAM.Wave.eqOn_zero_of_integral_sineMode_eq_zero`).

The proof extends `f` to the odd function `g` on `(-π, π]` (`KAM.Wave.oddExt`), shows that all
Fourier coefficients of `g` on `AddCircle (2π)` vanish, and concludes with Parseval for the
Fourier basis (`tsum_sq_fourierCoeffOn`).
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped Real ENNReal

namespace KAM.Wave

/-- The extension by zero of `f` from `(0, π)`, valued in `ℂ`. -/
def sineExtZero (f : ℝ → ℝ) : ℝ → ℂ := (Ioo 0 π).indicator fun x => (f x : ℂ)

/-- The odd extension `g(x) = f(x)` for `0 < x < π`, `g(x) = -f(-x)` for `-π < x < 0`, `g(0) = 0`
(blueprint `bpW:w1:sine-completeness`, step `stepW:w1:odd`), valued in `ℂ`. -/
def oddExt (f : ℝ → ℝ) (x : ℝ) : ℂ := sineExtZero f x - sineExtZero f (-x)

lemma oddExt_of_mem_Ioo (f : ℝ → ℝ) {x : ℝ} (hx : x ∈ Ioo 0 π) : oddExt f x = f x := by
  have h : -x ∉ Ioo 0 π := fun h => by linarith [h.1, hx.1]
  simp [oddExt, sineExtZero, hx, h]

lemma memLp_sineExtZero {f : ℝ → ℝ} (hf : MemLp f 2 (volume.restrict (Ioo 0 π))) :
    MemLp (sineExtZero f) 2 volume := by
  unfold sineExtZero
  exact (memLp_indicator_iff_restrict measurableSet_Ioo.nullMeasurableSet).2 hf.ofReal

lemma memLp_oddExt {f : ℝ → ℝ} (hf : MemLp f 2 (volume.restrict (Ioo 0 π))) :
    MemLp (oddExt f) 2 volume := by
  have h1 := memLp_sineExtZero hf
  have h2 : MemLp (sineExtZero f ∘ Neg.neg) 2 volume :=
    h1.comp_measurePreserving (Measure.measurePreserving_neg (volume : Measure ℝ))
  exact h1.sub h2

lemma integral_sineExtZero_mul (φ : ℝ → ℂ) (f : ℝ → ℝ) :
    ∫ x in (-π)..π, φ x * sineExtZero f x = ∫ x in (0 : ℝ)..π, φ x * f x := by
  have h : ∀ x, φ x * sineExtZero f x = (Ioo 0 π).indicator (fun x => φ x * f x) x := by
    intro x; by_cases hx : x ∈ Ioo 0 π <;> simp [sineExtZero, hx]
  simp_rw [h]
  rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos]),
    intervalIntegral.integral_of_le Real.pi_pos.le, integral_indicator measurableSet_Ioo,
    Measure.restrict_restrict measurableSet_Ioo, integral_Ioc_eq_integral_Ioo]
  have hsub : Ioo 0 π ⊆ Ioc (-π) π := fun x hx =>
    ⟨by linarith [hx.1, Real.pi_pos], hx.2.le⟩
  rw [Set.inter_eq_left.2 hsub]

lemma fourier_neg_coe_two_pi (n : ℤ) (x : ℝ) :
    fourier (-n) (x : AddCircle (π - -π)) = Complex.exp (-((n : ℂ) * x) * Complex.I) := by
  rw [fourier_coe_apply]
  congr 1
  have : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  push_cast
  field_simp
  ring

lemma exp_neg_sub_exp (z : ℂ) :
    Complex.exp (-z * Complex.I) - Complex.exp (z * Complex.I) =
      -2 * Complex.I * Complex.sin z := by
  rw [Complex.sin]
  have : Complex.exp (-z * Complex.I) = Complex.exp (-(z * Complex.I)) := by rw [neg_mul]
  rw [this]
  ring_nf
  simp [Complex.I_sq]
  ring

/-- The sine moments vanish for every integer frequency (blueprint step `stepW:w1:coeffs`). -/
lemma integral_sin_int_mul_eq_zero (f : ℝ → ℝ)
    (h : ∀ l : ℕ+, ∫ x in (0 : ℝ)..π, f x * sineMode l x = 0) (n : ℤ) :
    ∫ x in (0 : ℝ)..π, Real.sin (n * x) * f x = 0 := by
  have key : ∀ k : ℕ+, ∫ x in (0 : ℝ)..π, Real.sin (k * x) * f x = 0 := by
    intro k
    have h1 : ∫ x in (0 : ℝ)..π, f x * sineMode k x =
        Real.sqrt (2 / π) * ∫ x in (0 : ℝ)..π, Real.sin (k * x) * f x := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun x _ => ?_
      simp only [sineMode]; ring
    have hne : Real.sqrt (2 / π) ≠ 0 := by
      have : 0 < 2 / π := div_pos two_pos Real.pi_pos
      exact (Real.sqrt_pos.2 this).ne'
    rw [h k] at h1
    exact (mul_eq_zero.1 h1.symm).resolve_left hne
  have key' : ∀ k : ℕ, 0 < k → ∫ x in (0 : ℝ)..π, Real.sin ((k : ℝ) * x) * f x = 0 := fun k hk => by
    simpa using key ⟨k, hk⟩
  have habs : ((n.natAbs : ℕ) : ℝ) = |(n : ℝ)| := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  rcases lt_trichotomy n 0 with hn | hn | hn
  · have hk : 0 < n.natAbs := Int.natAbs_pos.2 hn.ne
    have h0 := key' _ hk
    have hn' : (n : ℝ) < 0 := by exact_mod_cast hn
    rw [habs, abs_of_neg hn'] at h0
    have e : ∀ x : ℝ, Real.sin (n * x) * f x = -(Real.sin (-(n : ℝ) * x) * f x) := by
      intro x; rw [neg_mul, Real.sin_neg]; ring
    simp_rw [e]
    rw [intervalIntegral.integral_neg, h0, neg_zero]
  · simp [hn]
  · have hk : 0 < n.natAbs := Int.natAbs_pos.2 hn.ne'
    have h0 := key' _ hk
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    rwa [habs, abs_of_pos hn'] at h0

lemma integrable_sineExtZero {f : ℝ → ℝ} (hf : MemLp f 2 (volume.restrict (Ioo 0 π))) :
    Integrable (sineExtZero f) volume := by
  have h1 : Integrable f (volume.restrict (Ioo 0 π)) := hf.integrable (by norm_num)
  exact (integrable_indicator_iff measurableSet_Ioo).2 h1.ofReal

lemma intervalIntegrable_mul_sineExtZero {f : ℝ → ℝ}
    (hf : MemLp f 2 (volume.restrict (Ioo 0 π))) {φ : ℝ → ℂ} (hφ : Continuous φ) :
    IntervalIntegrable (fun x => φ x * sineExtZero f x) volume (-π) π := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith [Real.pi_pos])]
  exact (integrable_sineExtZero hf).integrableOn.continuousOn_mul hφ.continuousOn isCompact_Icc

/-- All Fourier coefficients of the odd extension vanish (blueprint step `stepW:w1:coeffs`). -/
theorem fourierCoeffOn_oddExt_eq_zero {f : ℝ → ℝ} (hf : MemLp f 2 (volume.restrict (Ioo 0 π)))
    (h : ∀ l : ℕ+, ∫ x in (0 : ℝ)..π, f x * sineMode l x = 0) (n : ℤ) :
    fourierCoeffOn (by linarith [Real.pi_pos] : -π < π) (oddExt f) n = 0 := by
  rw [fourierCoeffOn_eq_integral _ _ (by linarith [Real.pi_pos] : -π < π)]
  have hint : ∫ x in (-π)..π, fourier (-n) (x : AddCircle (π - -π)) • oddExt f x = 0 := by
    set Em : ℝ → ℂ := fun x => Complex.exp (-((n : ℂ) * x) * Complex.I) with hEm
    set Ep : ℝ → ℂ := fun x => Complex.exp (((n : ℂ) * x) * Complex.I) with hEp
    have hEmc : Continuous Em := by rw [hEm]; fun_prop
    have hEpc : Continuous Ep := by rw [hEp]; fun_prop
    have h1 : ∀ x : ℝ, fourier (-n) (x : AddCircle (π - -π)) • oddExt f x =
        Em x * sineExtZero f x - Ep (-x) * sineExtZero f (-x) := by
      intro x
      rw [fourier_neg_coe_two_pi, smul_eq_mul, oddExt, mul_sub]
      congr 2
      simp only [hEp, Complex.ofReal_neg, mul_neg, neg_mul]
    simp_rw [h1]
    have hI : IntervalIntegrable (fun x => Ep x * sineExtZero f x) volume (-π) π :=
      intervalIntegrable_mul_sineExtZero hf hEpc
    have hI' : IntervalIntegrable (fun x => Ep (-x) * sineExtZero f (-x)) volume (-π) π := by
      have := (IntervalIntegrable.iff_comp_neg (a := -π) (b := π)
      (by rw [enorm_mul]; exact ENNReal.mul_ne_top enorm_ne_top enorm_ne_top)).1 hI
      simpa using this.symm
    rw [intervalIntegral.integral_sub (intervalIntegrable_mul_sineExtZero hf hEmc) hI',
      intervalIntegral.integral_comp_neg (fun x => Ep x * sineExtZero f x) (a := -π) (b := π),
      neg_neg, ← intervalIntegral.integral_sub (intervalIntegrable_mul_sineExtZero hf hEmc) hI]
    have h2 : ∀ x : ℝ, Em x * sineExtZero f x - Ep x * sineExtZero f x =
        (Em - Ep) x * sineExtZero f x := fun x => by simp [sub_mul]
    simp_rw [h2]
    rw [integral_sineExtZero_mul (Em - Ep) f]
    have h3 : ∀ x : ℝ, (Em - Ep) x * (f x : ℂ) =
        (-2 * Complex.I) * ((Real.sin (n * x) * f x : ℝ) : ℂ) := by
      intro x
      have := exp_neg_sub_exp ((n : ℂ) * x)
      simp only [Pi.sub_apply, hEm, hEp, this]
      push_cast
      ring
    simp_rw [h3]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal,
      integral_sin_int_mul_eq_zero f h n]
    simp
  rw [hint, smul_zero]

/-- **Completeness of the sine system**, part (i) (blueprint `bpW:w1:sine-completeness`): an `L²`
function on `(0, π)` orthogonal to every `φ_l` vanishes almost everywhere. -/
theorem ae_eq_zero_of_integral_sineMode_eq_zero {f : ℝ → ℝ}
    (hf : MemLp f 2 (volume.restrict (Ioo 0 π)))
    (h : ∀ l : ℕ+, ∫ x in (0 : ℝ)..π, f x * sineMode l x = 0) :
    f =ᵐ[volume.restrict (Ioo 0 π)] 0 := by
  have hab : -π < π := by linarith [Real.pi_pos]
  have hL2 : MemLp (oddExt f) 2 (volume.restrict (Ioc (-π) π)) := (memLp_oddExt hf).restrict _
  have hP := tsum_sq_fourierCoeffOn hab hL2
  simp only [fourierCoeffOn_oddExt_eq_zero hf h, norm_zero] at hP
  have hP0 : ∫ x in (-π)..π, ‖oddExt f x‖ ^ 2 = 0 := by
    have hpos : (0 : ℝ) < (π - -π)⁻¹ := inv_pos.2 (by linarith [Real.pi_pos])
    have : (π - -π)⁻¹ • ∫ x in (-π)..π, ‖oddExt f x‖ ^ 2 = 0 := by
      rw [← hP]; simp
    exact (smul_eq_zero.1 this).resolve_left hpos.ne'
  have hint : Integrable (fun x => ‖oddExt f x‖ ^ 2) (volume.restrict (Ioc (-π) π)) := by
    have : MemLp (oddExt f) ((2 : ℕ) : ℝ≥0∞) (volume.restrict (Ioc (-π) π)) := by
      simpa using hL2
    exact this.integrable_norm_pow'
  rw [intervalIntegral.integral_of_le hab.le,
    integral_eq_zero_iff_of_nonneg (fun x => by positivity) hint] at hP0
  have hsub : Ioo 0 π ⊆ Ioc (-π) π := fun x hx => ⟨by linarith [hx.1, Real.pi_pos], hx.2.le⟩
  have hP1 := ae_restrict_of_ae_restrict_of_subset hsub hP0
  filter_upwards [hP1, ae_restrict_mem measurableSet_Ioo] with x hx hxm
  have h0 : ‖oddExt f x‖ ^ 2 = 0 := hx
  have h1 : oddExt f x = 0 := norm_eq_zero.1 (pow_eq_zero_iff (two_ne_zero)|>.1 h0)
  rw [oddExt_of_mem_Ioo f hxm] at h1
  simpa using h1

/-- **Completeness of the sine system**, part (ii) (blueprint `bpW:w1:sine-completeness`): if
moreover `f` is continuous on `[0, π]`, it vanishes on `[0, π]`. -/
theorem eqOn_zero_of_integral_sineMode_eq_zero {f : ℝ → ℝ}
    (hf : MemLp f 2 (volume.restrict (Ioo 0 π))) (hc : ContinuousOn f (Icc 0 π))
    (h : ∀ l : ℕ+, ∫ x in (0 : ℝ)..π, f x * sineMode l x = 0) :
    ∀ x ∈ Icc 0 π, f x = 0 := by
  have hae := ae_eq_zero_of_integral_sineMode_eq_zero hf h
  have hIoo : EqOn f 0 (Ioo 0 π) :=
    Measure.eqOn_open_of_ae_eq hae isOpen_Ioo (hc.mono Ioo_subset_Icc_self) continuousOn_const
  have hcl : EqOn f 0 (Icc 0 π) :=
    hIoo.of_subset_closure hc continuousOn_const Ioo_subset_Icc_self
      (by rw [closure_Ioo Real.pi_pos.ne])
  exact fun x hx => hcl hx

end KAM.Wave

end
