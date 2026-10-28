/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Nekhoroshev.Averaging.Shells
public import KAM.Nekhoroshev.Averaging.Coefficients

/-!
# Part N12: integrals of the envelopes (`bpN:p12:envelopes`)

The `ℝ≥0∞` envelopes `avgWenv`, `avgW1env`, `avgBenv`, `avgRenv`, `avgPhiEnv` are integrated over `G`
termwise (`en-term`, Tonelli for `tsum`) using the shell integrals, and summed with the weight
`(1 + |k|₁)³ e^(-π s |k|₁)` (`avgSigma`). The constants `avgCW`, `avgCB`, `avgCR`, `avgCPhi` are
computed (`en-choice`). `envelopes_from_slab` takes the slab constant as a derived hypothesis;
`envelopes` constructs it.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory
open scoped ENNReal

namespace KAM.Nekhoroshev

variable {n : ℕ} {R s : ℝ} {h : (Fin n → ℂ) → ℂ} {f : AvgComplexPhase n → ℂ}

/-- All envelope constants are computed, not postulated bound witnesses. -/
def avgSigma (s : ℝ) : ℝ :=
  ∑' k : Fin n → ℤ, if k = 0 then 0 else (1 + KAM.Fourier.modeSize k) ^ 3 * avgBeta s k
def avgCW (n : ℕ) (s C₁ Ω₀ : ℝ) : ℝ := 3 * C₁ * (1 + Ω₀) * avgSigma (n := n) s
def avgCB (n : ℕ) (s C₁ Ω₀ M₂ : ℝ) : ℝ :=
  avgSigma (n := n) s * C₁ * (6 * n * (1 + Ω₀) / s + 5 * Real.sqrt n * M₂)
def avgCR (n : ℕ) (s C₁ : ℝ) : ℝ := 10 * Real.pi * C₁ * avgSigma (n := n) s
def avgCPhi (n : ℕ) (s C₁ Ω₀ M₂ : ℝ) : ℝ :=
  4 / s * avgCB n s C₁ Ω₀ M₂ + 8 * Real.pi / s * avgCW n s C₁ Ω₀ + avgCR n s C₁

namespace AvgEnv

/-- The summation weight vanishing at `k = 0`. -/
def wt (s : ℝ) (k : Fin n → ℤ) : ℝ :=
  if k = 0 then 0 else (1 + KAM.Fourier.modeSize k) ^ 3 * avgBeta s k

theorem avgBeta_nonneg (s : ℝ) (k : Fin n → ℤ) : 0 ≤ avgBeta s k := (Real.exp_pos _).le

theorem wt_nonneg (s : ℝ) (k : Fin n → ℤ) : 0 ≤ wt s k := by
  unfold wt
  split_ifs
  · exact le_rfl
  · have := AvgShell.mode_nonneg (n := n) k
    have := avgBeta_nonneg s k
    positivity

theorem wt_summable (d : AveragingData n R s h f) : Summable (wt (n := n) s) := by
  refine Summable.of_nonneg_of_le (wt_nonneg s) (fun k => ?_) (coef d).2.2.2.2.2
  unfold wt
  split_ifs
  · have := AvgShell.mode_nonneg (n := n) k
    have := avgBeta_nonneg s k
    positivity
  · exact le_rfl

theorem sigma_eq (s : ℝ) : avgSigma (n := n) s = ∑' k : Fin n → ℤ, wt s k := rfl

theorem sigma_nonneg (s : ℝ) : 0 ≤ avgSigma (n := n) s := tsum_nonneg (wt_nonneg s)

theorem aem_comp (d : AveragingData n R s h f) (k : Fin n → ℤ) {φ : ℝ → ℝ}
    (hφ : Measurable φ) :
    AEMeasurable (fun I => ENNReal.ofReal (φ (avgQ h k I))) (volume.restrict (avgG n R)) :=
  ENNReal.measurable_ofReal.comp_aemeasurable (hφ.comp_aemeasurable (AvgShell.Q_aemeasurable d k))

theorem env_aem (d : AveragingData n R s h f) {φ : (Fin n → ℤ) → ℝ → ℝ}
    (hφ : ∀ k, Measurable (φ k)) :
    AEMeasurable (fun I => ∑' k, ENNReal.ofReal (φ k (avgQ h k I)))
      (volume.restrict (avgG n R)) :=
  AEMeasurable.ennreal_tsum fun k => aem_comp d k (hφ k)

/-- Termwise integration of an envelope. -/
theorem env_le (d : AveragingData n R s h f) {φ : (Fin n → ℤ) → ℝ → ℝ}
    (hφ : ∀ k, Measurable (φ k)) {c : ℝ} (hc : 0 ≤ c)
    (hint : ∀ k, ∫⁻ I in avgG n R, ENNReal.ofReal (φ k (avgQ h k I)) ≤
      ENNReal.ofReal (c * wt s k)) :
    ∫⁻ I in avgG n R, ∑' k, ENNReal.ofReal (φ k (avgQ h k I)) ≤
      ENNReal.ofReal (c * avgSigma (n := n) s) := by
  rw [lintegral_tsum fun k => aem_comp d k (hφ k)]
  calc ∑' k, ∫⁻ I in avgG n R, ENNReal.ofReal (φ k (avgQ h k I))
      ≤ ∑' k, ENNReal.ofReal (c * wt s k) := ENNReal.tsum_le_tsum hint
    _ = ENNReal.ofReal (∑' k, c * wt s k) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun k => mul_nonneg hc (wt_nonneg s k))
          ((wt_summable d).mul_left c)).symm
    _ = _ := by rw [tsum_mul_left, sigma_eq]

theorem lint_const_mul (a : ℝ) (ha : 0 ≤ a) (g : ℝ → ℝ) (k : Fin n → ℤ) :
    ∫⁻ I in avgG n R, ENNReal.ofReal (a * g (avgQ h k I)) =
      ENNReal.ofReal a * ∫⁻ I in avgG n R, ENNReal.ofReal (g (avgQ h k I)) := by
  simp_rw [ENNReal.ofReal_mul ha]
  exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

theorem contPsi {κ : ℝ} (hκ : 0 < κ) : Continuous (avgPsi κ) :=
  (corrector hκ).1.continuous

theorem contPsiD {κ : ℝ} (hκ : 0 < κ) : Continuous (avgPsiD κ) := by
  unfold avgPsiD
  exact Continuous.div (by fun_prop) (by fun_prop) fun y => by positivity

theorem contRes {κ : ℝ} (hκ : 0 < κ) : Continuous (fun y : ℝ => κ ^ 2 / (y ^ 2 + κ ^ 2)) :=
  Continuous.div (by fun_prop) (by fun_prop) fun y => by positivity

theorem avgLog_ge_one {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) : 1 ≤ avgLog κ := by
  unfold avgLog; linarith [AvgShell.avgLog_nonneg hκ hκ1]

theorem mul_avgLog_le {κ : ℝ} (hκ : 0 < κ) : κ * avgLog κ ≤ 1 := by
  unfold avgLog
  have := Real.log_le_sub_one_of_pos (show 0 < 1 / κ by positivity)
  have h2 : κ * (1 / κ - 1) = 1 - κ := by field_simp
  nlinarith

theorem avgLog_le {κ : ℝ} (hκ : 0 < κ) : avgLog κ ≤ 1 / κ := by
  have := mul_avgLog_le hκ
  rw [le_div_iff₀ hκ]; linarith

end AvgEnv

end KAM.Nekhoroshev

end
