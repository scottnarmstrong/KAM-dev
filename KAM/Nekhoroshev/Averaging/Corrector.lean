/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Nekhoroshev.Averaging.Coefficients

/-!
# Part N12: the corrector (`bpN:p12:corrector`)

The rational regularization `avgPsi κ y = y / (y² + κ²)` of the divisor `1/y`, its derivative
`avgPsiD`, the termwise corrector coefficients `avgU`, the corrector `avgW` (all modes; the zero
mode contributes `0` because of the factor `k j`), the ENNReal envelopes and the residual
`avgResidual`. No regularity of `avgW` is assumed here (see `CorrectorRegular`).
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory
open scoped ENNReal ContDiff

namespace KAM.Nekhoroshev

variable {n : ℕ}

def avgPsi (κ y : ℝ) : ℝ := y / (y ^ 2 + κ ^ 2)
def avgPsiD (κ y : ℝ) : ℝ := (κ ^ 2 - y ^ 2) / (y ^ 2 + κ ^ 2) ^ 2

theorem corrector {κ : ℝ} (hκ : 0 < κ) :
    ContDiff ℝ ∞ (avgPsi κ) ∧ ∀ y : ℝ,
      HasDerivAt (avgPsi κ) (avgPsiD κ y) y ∧
      |avgPsi κ y| ≤ 1 / (2 * κ) ∧ |avgPsiD κ y| ≤ κ⁻¹ ^ 2 ∧
      1 - y * avgPsi κ y = κ ^ 2 / (y ^ 2 + κ ^ 2) ∧
      0 ≤ κ ^ 2 / (y ^ 2 + κ ^ 2) ∧ κ ^ 2 / (y ^ 2 + κ ^ 2) ≤ 1 ∧
      (y ≠ 0 → |avgPsi κ y| ≤ 1 / |y| ∧ |avgPsiD κ y| ≤ y⁻¹ ^ 2 ∧
        κ ^ 2 / (y ^ 2 + κ ^ 2) ≤ κ ^ 2 * y⁻¹ ^ 2) := by
  have hden : ∀ y : ℝ, 0 < y ^ 2 + κ ^ 2 := fun y => by positivity
  refine ⟨?_, fun y => ?_⟩
  · exact contDiff_id.div (contDiff_id.pow 2 |>.add contDiff_const)
      (fun y => (hden y).ne')
  have hd := hden y
  have hκ2 : 0 < κ ^ 2 := by positivity
  refine ⟨?_, ?_, ?_, ?_, by positivity, ?_, fun hy => ?_⟩
  · have h1 : HasDerivAt (fun x : ℝ => x ^ 2 + κ ^ 2) (2 * y) y := by
      simpa using (hasDerivAt_pow 2 y).add_const (κ ^ 2)
    have := (hasDerivAt_id y).div h1 hd.ne'
    have e : avgPsiD κ y = (1 * (y ^ 2 + κ ^ 2) - y * (2 * y)) / (y ^ 2 + κ ^ 2) ^ 2 := by
      unfold avgPsiD; ring
    rw [e]
    exact this
  · unfold avgPsi
    rw [abs_div, abs_of_pos hd, div_le_div_iff₀ hd (by positivity)]
    nlinarith [sq_nonneg (|y| - κ), sq_abs y]
  · unfold avgPsiD
    rw [abs_div, abs_of_pos (by positivity : 0 < (y ^ 2 + κ ^ 2) ^ 2), inv_pow,
      div_le_iff₀ (by positivity)]
    have h1 : |κ ^ 2 - y ^ 2| ≤ y ^ 2 + κ ^ 2 :=
      abs_le.2 ⟨by nlinarith [sq_nonneg y], by nlinarith [sq_nonneg y]⟩
    calc |κ ^ 2 - y ^ 2| ≤ y ^ 2 + κ ^ 2 := h1
      _ ≤ (κ ^ 2)⁻¹ * (y ^ 2 + κ ^ 2) ^ 2 := by
        rw [← div_eq_inv_mul, le_div_iff₀ hκ2]
        nlinarith [sq_nonneg y, mul_nonneg (sq_nonneg y) hκ2.le]
  · unfold avgPsi
    field_simp
    ring
  · rw [div_le_one hd]; nlinarith [sq_nonneg y]
  · have hy2 : 0 < y ^ 2 := by positivity
    refine ⟨?_, ?_, ?_⟩
    · unfold avgPsi
      rw [abs_div, abs_of_pos hd, div_le_div_iff₀ hd (abs_pos.2 hy)]
      nlinarith [abs_mul_abs_self y, abs_nonneg y]
    · unfold avgPsiD
      rw [abs_div, abs_of_pos (by positivity : 0 < (y ^ 2 + κ ^ 2) ^ 2), inv_pow,
        div_le_iff₀ (by positivity)]
      have h1 : |κ ^ 2 - y ^ 2| ≤ y ^ 2 + κ ^ 2 :=
        abs_le.2 ⟨by nlinarith [sq_nonneg y], by nlinarith [sq_nonneg y]⟩
      calc |κ ^ 2 - y ^ 2| ≤ y ^ 2 + κ ^ 2 := h1
        _ ≤ (y ^ 2)⁻¹ * (y ^ 2 + κ ^ 2) ^ 2 := by
          rw [← div_eq_inv_mul, le_div_iff₀ hy2]
          nlinarith [mul_nonneg hy2.le hκ2.le, sq_nonneg κ, mul_nonneg hκ2.le hκ2.le]
    · rw [inv_pow, ← div_eq_mul_inv, div_le_div_iff₀ hd hy2]
      nlinarith [sq_nonneg κ, hκ2]

def avgU (h : (Fin n → ℂ) → ℂ) (f : AvgComplexPhase n → ℂ)
    (κ : ℝ) (k : Fin n → ℤ) (I : Fin n → ℝ) : Fin n → ℂ :=
  fun j => avgCoeff f (KAM.realInclusion n I) k * (avgPsi κ (avgQ h k I) : ℂ) * (k j : ℂ)
def avgW (h : (Fin n → ℂ) → ℂ) (f : AvgComplexPhase n → ℂ)
    (κ : ℝ) (z : AvgPhase n) : Fin n → ℂ :=
  -∑' k : Fin n → ℤ, KAM.character k (KAM.realInclusion n z.1) • avgU h f κ k z.2

def avgWenv (h : (Fin n → ℂ) → ℂ) (s κ : ℝ) (I : Fin n → ℝ) : ℝ≥0∞ :=
  ∑' k : Fin n → ℤ, ENNReal.ofReal
    (‖fun j => (k j : ℝ)‖ * avgBeta s k * |avgPsi κ (avgQ h k I)|)
def avgW1env (h : (Fin n → ℂ) → ℂ) (s κ : ℝ) (I : Fin n → ℝ) : ℝ≥0∞ :=
  ∑' k : Fin n → ℤ, ENNReal.ofReal (2 * Real.pi *
    ‖fun j => (k j : ℝ)‖ * KAM.Fourier.modeSize k * avgBeta s k * |avgPsi κ (avgQ h k I)|)
def avgBterm (h : (Fin n → ℂ) → ℂ) (s M₂ κ : ℝ) (k : Fin n → ℤ)
    (I : Fin n → ℝ) : ℝ :=
  ‖fun j => (k j : ℝ)‖ * avgBeta s k *
    (2 * n / s * |avgPsi κ (avgQ h k I)| +
      M₂ * KAM.Fourier.modeSize k * |avgPsiD κ (avgQ h k I)|)
def avgBenv (h : (Fin n → ℂ) → ℂ) (s M₂ κ : ℝ) (I : Fin n → ℝ) : ℝ≥0∞ :=
  ∑' k : Fin n → ℤ, ENNReal.ofReal (avgBterm h s M₂ κ k I)
def avgRenv (h : (Fin n → ℂ) → ℂ) (s κ : ℝ) (I : Fin n → ℝ) : ℝ≥0∞ :=
  ∑' k : Fin n → ℤ, ENNReal.ofReal (2 * Real.pi * ‖fun j => (k j : ℝ)‖ * avgBeta s k *
    (κ ^ 2 / (avgQ h k I ^ 2 + κ ^ 2)))
def avgPhiEnv (h : (Fin n → ℂ) → ℂ) (s M₂ ε κ : ℝ) (I : Fin n → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (ε * 4 / s) * avgBenv h s M₂ κ I +
    ENNReal.ofReal (ε * 2 / s) * avgW1env h s κ I + avgRenv h s κ I

def avgResidual (h : (Fin n → ℂ) → ℂ) (f : AvgComplexPhase n → ℂ)
    (κ : ℝ) (z : AvgPhase n) : Fin n → ℂ :=
  KAM.realInclusion n (avgA f z) - fderiv ℝ (avgW h f κ) z (KAM.frequencyMap h z.2, 0)

end KAM.Nekhoroshev

end
