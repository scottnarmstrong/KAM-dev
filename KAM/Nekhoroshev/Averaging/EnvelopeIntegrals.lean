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

/-! ### Per-mode integral bounds (`en-term`) -/

section PerMode

variable (d : AveragingData n R s h f) {C₁ Ω₀ κ : ℝ} (hC : AvgSlabBound h R C₁)
  (hΩ : ∀ I ∈ avgG n R, ‖KAM.frequencyMap h I‖ ≤ Ω₀) (hκ : 0 < κ) (hκ1 : κ ≤ 1)

include d hC hΩ hκ hκ1

theorem term_W {k : Fin n → ℤ} (hk : k ≠ 0) :
    ∫⁻ I in avgG n R, ENNReal.ofReal (‖fun j => (k j : ℝ)‖ * avgBeta s k *
        |avgPsi κ (avgQ h k I)|) ≤
      ENNReal.ofReal (3 * C₁ * (1 + Ω₀) * avgLog κ * wt s k) := by
  have hm := AvgShell.mode_nonneg (n := n) k
  have hb := avgBeta_nonneg s k
  have hk1 := AvgShell.norm_le_mode k
  have hC1 := hC.1
  have hΩ0 : 0 ≤ Ω₀ := (norm_nonneg _).trans (hΩ 0 (by
    simp only [avgG, mem_closedBall, dist_self]; linarith [d.hR]))
  have hL := avgLog_ge_one hκ hκ1
  rw [lint_const_mul _ (by positivity) (fun y => |avgPsi κ y|)]
  refine (mul_le_mul_right (shells_from_slab d hC hΩ hκ hκ1 hk).2.1 _).trans ?_
  rw [← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hn := norm_nonneg (fun j => (k j : ℝ))
  have h3 : ‖fun j => (k j : ℝ)‖ * (1 + KAM.Fourier.modeSize k) ≤
      (1 + KAM.Fourier.modeSize k) ^ 3 := by
    calc _ ≤ (1 + KAM.Fourier.modeSize k) * (1 + KAM.Fourier.modeSize k) := by gcongr; linarith
      _ ≤ _ := by
        have : (1 + KAM.Fourier.modeSize k) ^ 2 ≤ (1 + KAM.Fourier.modeSize k) ^ 3 :=
          pow_le_pow_right₀ (by linarith) (by norm_num)
        nlinarith
  have hw : wt s k = (1 + KAM.Fourier.modeSize k) ^ 3 * avgBeta s k := by simp [wt, hk]
  rw [hw]
  have hX : 0 ≤ 3 * C₁ * (1 + Ω₀) * avgLog κ * avgBeta s k := by positivity
  calc _ = (3 * C₁ * (1 + Ω₀) * avgLog κ * avgBeta s k) *
        (‖fun j => (k j : ℝ)‖ * (1 + KAM.Fourier.modeSize k)) := by ring
    _ ≤ (3 * C₁ * (1 + Ω₀) * avgLog κ * avgBeta s k) * (1 + KAM.Fourier.modeSize k) ^ 3 :=
        mul_le_mul_of_nonneg_left h3 hX
    _ = _ := by ring

theorem term_W1 {k : Fin n → ℤ} (hk : k ≠ 0) :
    ∫⁻ I in avgG n R, ENNReal.ofReal (2 * Real.pi * ‖fun j => (k j : ℝ)‖ *
        KAM.Fourier.modeSize k * avgBeta s k * |avgPsi κ (avgQ h k I)|) ≤
      ENNReal.ofReal (2 * Real.pi * (3 * C₁ * (1 + Ω₀) * avgLog κ) * wt s k) := by
  have hm := AvgShell.mode_nonneg (n := n) k
  have hb := avgBeta_nonneg s k
  have hk1 := AvgShell.norm_le_mode k
  have hC1 := hC.1
  have hΩ0 : 0 ≤ Ω₀ := (norm_nonneg _).trans (hΩ 0 (by
    simp only [avgG, mem_closedBall, dist_self]; linarith [d.hR]))
  have hL := avgLog_ge_one hκ hκ1
  have hpi := Real.pi_pos
  have hn := norm_nonneg (fun j => (k j : ℝ))
  rw [lint_const_mul _ (by positivity) (fun y => |avgPsi κ y|)]
  refine (mul_le_mul_right (shells_from_slab d hC hΩ hκ hκ1 hk).2.1 _).trans ?_
  rw [← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have h3 : ‖fun j => (k j : ℝ)‖ * KAM.Fourier.modeSize k * (1 + KAM.Fourier.modeSize k) ≤
      (1 + KAM.Fourier.modeSize k) ^ 3 := by
    calc _ ≤ (1 + KAM.Fourier.modeSize k) * (1 + KAM.Fourier.modeSize k) *
          (1 + KAM.Fourier.modeSize k) := by gcongr <;> linarith
      _ = _ := by ring
  have hw : wt s k = (1 + KAM.Fourier.modeSize k) ^ 3 * avgBeta s k := by simp [wt, hk]
  rw [hw]
  have hX : 0 ≤ 2 * Real.pi * (3 * C₁ * (1 + Ω₀) * avgLog κ) * avgBeta s k := by positivity
  calc _ = (2 * Real.pi * (3 * C₁ * (1 + Ω₀) * avgLog κ) * avgBeta s k) *
        (‖fun j => (k j : ℝ)‖ * KAM.Fourier.modeSize k * (1 + KAM.Fourier.modeSize k)) := by ring
    _ ≤ (2 * Real.pi * (3 * C₁ * (1 + Ω₀) * avgLog κ) * avgBeta s k) *
        (1 + KAM.Fourier.modeSize k) ^ 3 := mul_le_mul_of_nonneg_left h3 hX
    _ = _ := by ring

theorem term_R {k : Fin n → ℤ} (hk : k ≠ 0) :
    ∫⁻ I in avgG n R, ENNReal.ofReal (2 * Real.pi * ‖fun j => (k j : ℝ)‖ * avgBeta s k *
        (κ ^ 2 / (avgQ h k I ^ 2 + κ ^ 2))) ≤
      ENNReal.ofReal (10 * Real.pi * C₁ * κ * wt s k) := by
  have hm := AvgShell.mode_nonneg (n := n) k
  have hb := avgBeta_nonneg s k
  have hk1 := AvgShell.norm_le_euclid k
  have hK := AvgShell.euclid_ge_one hk
  have hC1 := hC.1
  have hΩ0 : 0 ≤ Ω₀ := (norm_nonneg _).trans (hΩ 0 (by
    simp only [avgG, mem_closedBall, dist_self]; linarith [d.hR]))
  have hpi := Real.pi_pos
  have hn := norm_nonneg (fun j => (k j : ℝ))
  rw [lint_const_mul _ (by positivity) (fun y => κ ^ 2 / (y ^ 2 + κ ^ 2))]
  refine (mul_le_mul_right (shells_from_slab d hC hΩ hκ hκ1 hk).2.2.2 _).trans ?_
  rw [← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hK0 : 0 < euclid (fun j => (k j : ℝ)) := by linarith
  have h2 : ‖fun j => (k j : ℝ)‖ / euclid (fun j => (k j : ℝ)) ≤ 1 :=
    (div_le_one hK0).2 hk1
  have h3 : (1 : ℝ) ≤ (1 + KAM.Fourier.modeSize k) ^ 3 := one_le_pow₀ (by linarith)
  have hw : wt s k = (1 + KAM.Fourier.modeSize k) ^ 3 * avgBeta s k := by simp [wt, hk]
  rw [hw]
  have hX : 0 ≤ 10 * Real.pi * C₁ * κ * avgBeta s k := by positivity
  calc 2 * Real.pi * ‖fun j => (k j : ℝ)‖ * avgBeta s k *
        (5 * C₁ * κ / euclid (fun j => (k j : ℝ)))
      = (10 * Real.pi * C₁ * κ * avgBeta s k) *
        (‖fun j => (k j : ℝ)‖ / euclid (fun j => (k j : ℝ))) := by ring
    _ ≤ (10 * Real.pi * C₁ * κ * avgBeta s k) * 1 := mul_le_mul_of_nonneg_left h2 hX
    _ ≤ (10 * Real.pi * C₁ * κ * avgBeta s k) * (1 + KAM.Fourier.modeSize k) ^ 3 :=
        mul_le_mul_of_nonneg_left h3 hX
    _ = _ := by ring

theorem term_B {M₂ : ℝ} (hM0 : 0 ≤ M₂) {k : Fin n → ℤ} (hk : k ≠ 0) :
    ∫⁻ I in avgG n R, ENNReal.ofReal (avgBterm h s M₂ κ k I) ≤
      ENNReal.ofReal (C₁ * (6 * n * (1 + Ω₀) / s + 5 * Real.sqrt n * M₂) / κ * wt s k) := by
  have hm := AvgShell.mode_nonneg (n := n) k
  have hb := avgBeta_nonneg s k
  have hk1 := AvgShell.norm_le_mode k
  have hk2 := AvgShell.norm_le_euclid k
  have hK := AvgShell.euclid_ge_one hk
  have hC1 := hC.1
  have hs := d.hs
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast d.hn
  have hsq : (1 : ℝ) ≤ Real.sqrt n := by rw [Real.one_le_sqrt]; exact hn1
  have hΩ0 : 0 ≤ Ω₀ := (norm_nonneg _).trans (hΩ 0 (by
    simp only [avgG, mem_closedBall, dist_self]; linarith [d.hR]))
  have hL := avgLog_ge_one hκ hκ1
  have hLκ := avgLog_le hκ
  have hn := norm_nonneg (fun j => (k j : ℝ))
  have hK0 : 0 < euclid (fun j => (k j : ℝ)) := by linarith
  have hsh := shells_from_slab d hC hΩ hκ hκ1 hk
  set m := KAM.Fourier.modeSize k with hmdef
  set nk := ‖fun j => (k j : ℝ)‖ with hnk
  have hsplit : ∀ I, ENNReal.ofReal (avgBterm h s M₂ κ k I) =
      ENNReal.ofReal ((nk * avgBeta s k * (2 * n / s)) * |avgPsi κ (avgQ h k I)|) +
      ENNReal.ofReal ((nk * avgBeta s k * (M₂ * m)) * |avgPsiD κ (avgQ h k I)|) := fun I => by
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    unfold avgBterm
    ring
  simp_rw [hsplit]
  rw [lintegral_add_left' (aem_comp d k (φ := fun y => (nk * avgBeta s k * (2 * n / s)) *
    |avgPsi κ y|) (Continuous.measurable (by have := contPsi hκ; fun_prop))),
    lint_const_mul _ (by positivity) (fun y => |avgPsi κ y|),
    lint_const_mul _ (by positivity) (fun y => |avgPsiD κ y|)]
  refine (add_le_add (mul_le_mul_right hsh.2.1 _) (mul_le_mul_right hsh.2.2.1 _)).trans ?_
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hw : wt s k = (1 + m) ^ 3 * avgBeta s k := by unfold wt; rw [if_neg hk]
  rw [hw]
  have h3 : nk * (1 + m) ≤ (1 + m) ^ 3 := by
    calc _ ≤ (1 + m) * (1 + m) := by gcongr; linarith
      _ ≤ _ := by
        have : (1 + m) ^ 2 ≤ (1 + m) ^ 3 := pow_le_pow_right₀ (by linarith) (by norm_num)
        nlinarith
  have h4 : m ≤ (1 + m) ^ 3 := by
    have : (1 + m) ≤ (1 + m) ^ 3 := le_self_pow₀ (by linarith) (by norm_num)
    linarith
  have h5 : nk / euclid (fun j => (k j : ℝ)) ≤ 1 := (div_le_one hK0).2 hk2
  have real1 : nk * avgBeta s k * (2 * n / s) * (3 * C₁ * (1 + Ω₀) * (1 + m) * avgLog κ) ≤
      (6 * n * C₁ * (1 + Ω₀) / s) * (avgBeta s k * (1 + m) ^ 3) * (1 / κ) := by
    calc _ = (6 * n * C₁ * (1 + Ω₀) / s) * (avgBeta s k * (nk * (1 + m))) * avgLog κ := by ring
      _ ≤ _ := by gcongr
  have real2 : nk * avgBeta s k * (M₂ * m) * (5 * C₁ / (κ * euclid (fun j => (k j : ℝ)))) ≤
      (5 * C₁ * M₂ / κ) * (avgBeta s k * (1 + m) ^ 3) := by
    calc _ = (5 * C₁ * M₂ / κ) * (avgBeta s k * m) * (nk / euclid (fun j => (k j : ℝ))) := by
          field_simp
      _ ≤ (5 * C₁ * M₂ / κ) * (avgBeta s k * (1 + m) ^ 3) * 1 := by gcongr
      _ = _ := by ring
  have real3 : (5 * C₁ * M₂ / κ) * (avgBeta s k * (1 + m) ^ 3) ≤
      (5 * C₁ * Real.sqrt n * M₂ / κ) * (avgBeta s k * (1 + m) ^ 3) := by
    refine mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right ?_ hκ.le) (by positivity)
    nlinarith [mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ C₁) hM0)
      (by linarith : 0 ≤ Real.sqrt n - 1)]
  calc _ ≤ _ := add_le_add real1 (real2.trans real3)
    _ = _ := by ring

end PerMode

section Main

theorem env_zero (k : Fin n → ℤ) (hk : k = 0) : ‖fun j => (k j : ℝ)‖ = 0 := by
  subst hk
  have : (fun j : Fin n => (((0 : Fin n → ℤ) j : ℤ) : ℝ)) = 0 := by funext j; simp
  rw [this, norm_zero]

theorem wt_zero : wt (n := n) s 0 = 0 := by simp [wt]

variable (d : AveragingData n R s h f) {C₁ Ω₀ M₂ κ : ℝ} (hC : AvgSlabBound h R C₁)
  (hΩ : ∀ I ∈ avgG n R, ‖KAM.frequencyMap h I‖ ≤ Ω₀) (hM0 : 0 ≤ M₂)
  (hκ : 0 < κ) (hκ1 : κ ≤ 1)

include d hC hΩ hM0 hκ hκ1

theorem kappa_part :
    (∫⁻ I in avgG n R, avgWenv h s κ I) ≤ ENNReal.ofReal (avgCW n s C₁ Ω₀ * avgLog κ) ∧
    (∫⁻ I in avgG n R, avgW1env h s κ I) ≤
      ENNReal.ofReal (2 * Real.pi * avgCW n s C₁ Ω₀ * avgLog κ) ∧
    (∫⁻ I in avgG n R, avgBenv h s M₂ κ I) ≤ ENNReal.ofReal (avgCB n s C₁ Ω₀ M₂ / κ) ∧
    (∫⁻ I in avgG n R, avgRenv h s κ I) ≤ ENNReal.ofReal (avgCR n s C₁ * κ) := by
  have hC1 := hC.1
  have hΩ0 : 0 ≤ Ω₀ := (norm_nonneg _).trans (hΩ 0 (by
    simp only [avgG, mem_closedBall, dist_self]; linarith [d.hR]))
  have hpsi := contPsi hκ
  have hpsiD := contPsiD hκ
  have hres := contRes hκ
  have hL := avgLog_ge_one hκ hκ1
  have hσ := sigma_nonneg (n := n) s
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold avgWenv
    refine (env_le d (φ := fun k y => ‖fun j => (k j : ℝ)‖ * avgBeta s k * |avgPsi κ y|)
      (fun k => Continuous.measurable (by fun_prop)) (c := 3 * C₁ * (1 + Ω₀) * avgLog κ)
      (by positivity) (fun k => ?_)).trans (le_of_eq ?_)
    · by_cases hk : k = 0
      · simp [env_zero k hk]
      · exact term_W d hC hΩ hκ hκ1 hk
    · congr 1; unfold avgCW; ring
  · unfold avgW1env
    refine (env_le d (φ := fun k y => 2 * Real.pi * ‖fun j => (k j : ℝ)‖ *
        KAM.Fourier.modeSize k * avgBeta s k * |avgPsi κ y|)
      (fun k => Continuous.measurable (by fun_prop))
      (c := 2 * Real.pi * (3 * C₁ * (1 + Ω₀) * avgLog κ))
      (by positivity) (fun k => ?_)).trans (le_of_eq ?_)
    · by_cases hk : k = 0
      · simp [env_zero k hk]
      · exact term_W1 d hC hΩ hκ hκ1 hk
    · congr 1; unfold avgCW; ring
  · unfold avgBenv
    refine (env_le d (φ := fun k y => ‖fun j => (k j : ℝ)‖ * avgBeta s k *
        (2 * n / s * |avgPsi κ y| + M₂ * KAM.Fourier.modeSize k * |avgPsiD κ y|))
      (fun k => Continuous.measurable (by fun_prop))
      (c := C₁ * (6 * n * (1 + Ω₀) / s + 5 * Real.sqrt n * M₂) / κ)
      (by have := d.hs; positivity) (fun k => ?_)).trans (le_of_eq ?_)
    · by_cases hk : k = 0
      · simp [env_zero k hk]
      · exact term_B d hC hΩ hκ hκ1 hM0 hk
    · unfold avgCB; congr 1; ring
  · unfold avgRenv
    refine (env_le d (φ := fun k y => 2 * Real.pi * ‖fun j => (k j : ℝ)‖ * avgBeta s k *
        (κ ^ 2 / (y ^ 2 + κ ^ 2)))
      (fun k => Continuous.measurable (by fun_prop)) (c := 10 * Real.pi * C₁ * κ)
      (by positivity) (fun k => ?_)).trans (le_of_eq ?_)
    · by_cases hk : k = 0
      · simp [env_zero k hk]
      · exact term_R d hC hΩ hκ hκ1 hk
    · unfold avgCR; congr 1; ring

end Main

end AvgEnv

end KAM.Nekhoroshev

end
