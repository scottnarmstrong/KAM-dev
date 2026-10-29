/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.WeakKAM.Evaluation
public import KAM.Planetary.Quantitative.BudgetPower
public import KAM.Planetary.Quantitative.BudgetAdmissible

/-! # P11B polynomial budget

The polynomial lower bound `adm_budget` for the admissibility threshold `selectionAdmissible`
(`bpP:p11a:budget`, step `ab-lam`), its beta-variation form `adm_budget_beta` and the uniform
displacement power law `displacement_power` (`bpP:p11a:displacement-power`, K5 and K6).

`adm_budget` is obtained from the delivered quantitative bound `qb_poly` through the data
correspondence `qbcOfSelection` (with the derivative supremum replaced by `selectionM₀ d + 1`,
which is positive), once the data-only threshold is shown to lie below `selectionAdmissible`.
The three branches of `selectionLambdaMax` are compared with those of `lambdaFlat` using
`C₁ ≥ 1` in the first branch.
-/

@[expose] public noncomputable section
open Set Real MeasureTheory Filter Function
open scoped BigOperators Topology
namespace KAM.Planetary
open KAM KAM.Kepler
variable {n μ : ℕ} {t C₁ : ℝ}

/-- Only geometric/numerical data, including actual M₀, are fixed; h and beta vary. -/
def selectionFixedKey (d : SelectionData n) :=
  (d.μ, d.ρ, d.τ, d.ϑ, d.strip, d.C₁, d.M, d.loss, d.K, selectionM₀ d)
def selectionBetaExponent (d : SelectionData n) : ℝ :=
  2 * max (2 * (((d.μ : ℝ) + 1) / d.ρ))
    (1 + d.μ * (((d.μ : ℝ) + 1) / d.ρ))

/-- Rates of the eight actual inputs, in the order of adm-budget. -/
structure SelectionRates where
  theta : ℝ
  strip : ℝ
  beta : ℝ
  loss : ℝ
  M : ℝ
  M₀ : ℝ
  C₁ : ℝ
  diam : ℝ
  nonneg : 0 ≤ theta ∧ 0 ≤ strip ∧ 0 ≤ beta ∧ 0 ≤ loss ∧
    0 ≤ M ∧ 0 ≤ M₀ ∧ 0 ≤ C₁ ∧ 0 ≤ diam

def selectionBudgetD (n μ : ℕ) (r : SelectionRates) : ℝ :=
  n * r.diam + r.M + r.theta + (1 + (μ : ℝ)⁻¹) * r.beta
def selectionBudgetG (n μ ρ : ℕ) (r : SelectionRates) : ℝ :=
  max (r.beta / ρ) ((μ : ℝ) / ρ * (r.loss + selectionBudgetD n μ r))
def selectionBudgetL (r : SelectionRates) : ℝ := if r.strip = 0 then 0 else r.strip + 1
def selectionBudgetJ (n μ ρ : ℕ) (τ : ℝ) (r : SelectionRates) : ℝ :=
  max r.theta (selectionBudgetG n μ ρ r + (τ + 1) * selectionBudgetL r + r.C₁)
def selectionBudgetX (n μ ρ : ℕ) (τ : ℝ) (r : SelectionRates) : ℝ :=
  max (selectionBudgetJ n μ ρ τ r) (selectionBudgetL r)
def selectionBudgetH (n μ ρ : ℕ) (τ : ℝ) (r : SelectionRates) : ℝ :=
  max (selectionBudgetJ n μ ρ τ r)
    (max (selectionBudgetG n μ ρ r + (n + 1) * r.strip + τ * selectionBudgetL r +
      selectionBudgetX n μ ρ τ r) (r.beta + r.M₀ + μ * selectionBudgetJ n μ ρ τ r))
def selectionBudgetExponent (n μ ρ : ℕ) (τ : ℝ) (r : SelectionRates) : ℝ :=
  2 * selectionBudgetH n μ ρ τ r + r.C₁

/-- Input bounds on a family of data, not a smallness conclusion. -/
def selectionFamilyBounds (c u : ℝ) (r : SelectionRates) (d : SelectionData n) : Prop :=
  c * u ^ r.theta ≤ d.ϑ ∧ c * u ^ r.strip ≤ d.strip ∧
  c * u ^ r.beta ≤ d.β ∧ c * u ^ r.loss ≤ d.loss ∧
  d.M ≤ c⁻¹ * u ^ (-r.M) ∧ selectionM₀ d ≤ c⁻¹ * u ^ (-r.M₀) ∧
  d.C₁ ≤ c⁻¹ * u ^ (-r.C₁) ∧ Metric.diam d.K ≤ c⁻¹ * u ^ (-r.diam)

/-! ### Comparison of the quantitative threshold with `selectionAdmissible` -/

theorem polyBudget_thetaMax_le {d : SelectionData n} {m0 : ℝ} (hm : selectionM₀ d ≤ m0) :
    (qbcOfSelection d m0).thetaMax ≤ selectionThetaMax d := by
  have hb := d.beta_pos
  have h0 := selectionM₀_nonneg d
  unfold QuantitativeData.thetaMax selectionThetaMax
  simp only [qbcOfSelection]
  split_ifs
  · exact le_rfl
  · refine min_le_min le_rfl ?_
    have hc : (0 : ℝ) < 2 ^ (d.μ + 1) := by positivity
    have h1 : 0 < 2 ^ (d.μ + 1) * (2 * selectionM₀ d + d.β) := by positivity
    refine div_le_div_of_nonneg_left hb.le h1 ?_
    exact mul_le_mul_of_nonneg_left (by linarith) hc.le

/-- The data-only threshold of the correspondence lies below `selectionAdmissible`. -/
theorem polyBudget_threshold_le {d : SelectionData n} {m0 : ℝ}
    (hd : (qbcOfSelection d m0).NumericalValid) (hM : selectionM₀ d ≤ m0) :
    thresholds (qbcOfSelection d m0) ≤ selectionAdmissible d := by
  have hb := d.beta_pos
  have hdq := hd
  set Q := qbcOfSelection d m0 with hQ
  obtain ⟨hT1, hT⟩ := qbc_oldT_bounds hd
  obtain ⟨ht0, htf, ht1⟩ := qbc_oldt_bounds hd
  obtain ⟨hX0, hX⟩ := qbc_oldX_bounds hd
  have hl := qbc_lambdaFlat_pos hd
  have hN : 0 < n := hd.1
  have hN' : (0 : ℝ) < n := by exact_mod_cast hN
  have hC1 : 1 ≤ Q.C1 := hd.2.2.2.2.2.2.2.2.2.1
  have hC : 0 < Q.C1 := by linarith
  have hQ' : ({ Q with M0 := selectionM₀ d } : QuantitativeData n) =
      qbcOfSelection d (selectionM₀ d) := rfl
  rw [← qbc_oldThreshold_eq_selectionAdmissible, ← hQ', qbc_old_eq]
  have hlam : Q.lambdaFlat ≤ qbcLam n Q.mu Q.tau (Q.C1 * qbcOldt Q / 8) Q.varpi (qbcOldX Q)
      Q.gamma Q.s (qbcOldT Q) ({ Q with M0 := selectionM₀ d } : QuantitativeData n).thetaMax
      (qbcOldt Q) (p11c_cutoffConstant n Q.mu) := by
    rw [qbc_lambdaFlat_eq]
    refine qbcLam_mono hN ?_ hX0 hX (qbc_gamma_pos hd).le le_rfl hd.2.2.2.2.2.2.2.1.le le_rfl
      (by linarith) hT hd.2.2.2.2.1 (qbc_thetaMax_pos hd).le ?_ (qbc_tflat_pos hd).le htf
      (qbc_cutoffConstant_pos hd.1 Q.mu) (qbc_varpi_pos Q).le
    · have : Q.tflat ≤ Q.C1 * qbcOldt Q := htf.trans (by nlinarith)
      linarith
    · rw [hQ', qbc_thetaMax_sel]
      exact polyBudget_thetaMax_le hM
  unfold thresholds
  exact div_le_div_of_nonneg_right (pow_le_pow_left₀ hl.le hlam 2) (by positivity)

/-! ### `adm_budget` -/

theorem polyBudget_exponent_eq (n μ ρ : ℕ) (τ : ℝ) (r : SelectionRates) :
    (BudgetRates.exponent n μ ρ τ
      ⟨r.theta, r.strip, r.beta, r.loss, r.M, r.M₀, r.C₁, r.diam⟩) =
      selectionBudgetExponent n μ ρ τ r := by
  have hL : (if 0 < r.strip then r.strip + 1 else 0) = selectionBudgetL r := by
    unfold selectionBudgetL
    rcases r.nonneg.2.1.lt_or_eq with h | h
    · simp [h, h.ne']
    · simp [← h]
  unfold BudgetRates.exponent selectionBudgetExponent selectionBudgetH selectionBudgetJ
    selectionBudgetX selectionBudgetG selectionBudgetD
  simp only [one_div, hL]

/-- Uniform coefficient depends on the strip rate but not the other seven rates. -/
theorem adm_budget (n μ ρ : ℕ) (τ c as_ : ℝ) (hn : 1 ≤ n) (hμ : 1 ≤ μ)
    (hρ : ρ = 1 ∨ ρ = 2) (hτ : 0 ≤ τ) (hgap : (n : ℝ) * μ / ρ - 1 < τ)
    (hc : 0 < c) (hc1 : c ≤ 1) (has : 0 ≤ as_) :
    ∃ c' : ℝ, 0 < c' ∧ ∀ r : SelectionRates, r.strip = as_ →
      ∀ u : ℝ, 0 < u → u ≤ 1 → ∀ d : SelectionData n,
        d.μ = μ → d.ρ = ρ → d.τ = τ → selectionFamilyBounds c u r d →
        c' * u ^ selectionBudgetExponent n μ ρ τ r ≤ selectionAdmissible d := by
  obtain ⟨c', hc', H⟩ := qb_poly n μ ρ τ (c / 2) as_ hn hμ hρ hgap hτ (by positivity)
    (by linarith) has
  refine ⟨c', hc', ?_⟩
  intro r hs u hu0 hu1 d hμd hρd hτd fam
  obtain ⟨hθ0, hs0, hβ0, hl0, hM0, hm00, hC0, hd0⟩ := r.nonneg
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8⟩ := fam
  have hup : ∀ e : ℝ, 0 < u ^ e := fun e => Real.rpow_pos_of_pos hu0 e
  have hc2 : (c / 2)⁻¹ = 2 * c⁻¹ := by field_simp
  have hcinv : 1 ≤ c⁻¹ := one_le_inv₀ hc |>.2 hc1
  have hlow : ∀ e : ℝ, ∀ x : ℝ, c * u ^ e ≤ x → c / 2 * u ^ e ≤ x := by
    intro e x h
    have := hup e
    nlinarith
  have hup' : ∀ e : ℝ, ∀ x : ℝ, 0 ≤ e → x ≤ c⁻¹ * u ^ (-e) → x ≤ (c / 2)⁻¹ * u ^ (-e) := by
    intro e x he h
    have := qbPoly_negpow_ge_one hu0 hu1 he
    have h1 : 0 ≤ c⁻¹ := by positivity
    rw [hc2]
    nlinarith
  set a : BudgetRates := ⟨r.theta, r.strip, r.beta, r.loss, r.M, r.M₀, r.C₁, r.diam⟩ with ha
  have hv : a.Valid := ⟨hθ0, hs0, hβ0, hl0, hM0, hm00, hC0, hd0⟩
  have hQ : (qbcOfSelection d (selectionM₀ d + 1)).NumericalValid := by
    have := selectionM₀_nonneg d
    exact ⟨d.n_pos, d.μ_pos, d.rho_mem, d.tau_gap, d.tau_nonneg, d.theta_pos, d.theta_le,
      d.strip_pos, d.strip_le, d.hessian_normalized, by show 0 < selectionM₀ d + 1; linarith,
      d.beta_pos, d.beta_le, d.compact, d.loss_pos, d.loss_lt⟩
  have hrb : RateBounds a (c / 2) u (qbcOfSelection d (selectionM₀ d + 1)) := by
    refine ⟨hlow _ _ f1, hlow _ _ f2, hlow _ _ f3, hlow _ _ f4, hup' _ _ hM0 f5, ?_,
      hup' _ _ hC0 f7, hup' _ _ hd0 f8⟩
    have hE := qbPoly_negpow_ge_one hu0 hu1 hm00
    show selectionM₀ d + 1 ≤ (c / 2)⁻¹ * u ^ (-r.M₀)
    rw [hc2]
    nlinarith
  have h1 := H a hv hs (qbcOfSelection d (selectionM₀ d + 1)) hQ hμd hρd hτd u ⟨hu0, hu1⟩ hrb
  have h2 := polyBudget_threshold_le hQ (by linarith : selectionM₀ d ≤ selectionM₀ d + 1)
  rw [polyBudget_exponent_eq] at h1
  exact h1.trans h2

/-! ### `adm_budget_beta` -/

theorem polyBudget_key {d d₀ : SelectionData n} (hk : selectionFixedKey d = selectionFixedKey d₀) :
    d.μ = d₀.μ ∧ d.ρ = d₀.ρ ∧ d.τ = d₀.τ ∧ d.ϑ = d₀.ϑ ∧ d.strip = d₀.strip ∧ d.C₁ = d₀.C₁ ∧
      d.M = d₀.M ∧ d.loss = d₀.loss ∧ d.K = d₀.K ∧ selectionM₀ d = selectionM₀ d₀ := by
  simpa only [selectionFixedKey, Prod.mk.injEq] using hk

theorem polyBudget_exponent_beta (n μ ρ : ℕ) (hμ : 1 ≤ μ) (hρ : ρ = 1 ∨ ρ = 2) (τ : ℝ) :
    selectionBudgetExponent n μ ρ τ ⟨0, 0, 1, 0, 0, 0, 0, 0, by norm_num⟩ =
      2 * max (2 * (((μ : ℝ) + 1) / ρ)) (1 + μ * (((μ : ℝ) + 1) / ρ)) := by
  have hr : (0 : ℝ) < ρ := by rcases hρ with h | h <;> simp [h]
  have hm : (0 : ℝ) < μ := by exact_mod_cast hμ
  have hG : selectionBudgetG n μ ρ ⟨0, 0, 1, 0, 0, 0, 0, 0, by norm_num⟩ =
      ((μ : ℝ) + 1) / ρ := by
    unfold selectionBudgetG selectionBudgetD
    simp only [mul_zero, add_zero, zero_add, mul_one]
    have : (μ : ℝ) / ρ * (1 + (μ : ℝ)⁻¹) = ((μ : ℝ) + 1) / ρ := by field_simp
    rw [this]
    exact max_eq_right (div_le_div_of_nonneg_right (by linarith) hr.le)
  have hG0 : 0 ≤ ((μ : ℝ) + 1) / ρ := by positivity
  have hL : selectionBudgetL ⟨0, 0, 1, 0, 0, 0, 0, 0, by norm_num⟩ = 0 := by
    simp [selectionBudgetL]
  have hJ : selectionBudgetJ n μ ρ τ ⟨0, 0, 1, 0, 0, 0, 0, 0, by norm_num⟩ =
      ((μ : ℝ) + 1) / ρ := by
    unfold selectionBudgetJ
    rw [hG, hL]
    simp only [mul_zero, add_zero]
    exact max_eq_right hG0
  have hX : selectionBudgetX n μ ρ τ ⟨0, 0, 1, 0, 0, 0, 0, 0, by norm_num⟩ =
      ((μ : ℝ) + 1) / ρ := by
    unfold selectionBudgetX
    rw [hJ, hL]
    exact max_eq_left hG0
  unfold selectionBudgetExponent selectionBudgetH
  rw [hJ, hG, hL, hX]
  simp only [mul_zero, add_zero, zero_add]
  rw [max_eq_right (le_max_of_le_left (by linarith)), ← two_mul]
  congr 1

/-- c_* chosen BEFORE varying h, beta, epsilon and f with the same numerical/geometric key. -/
theorem adm_budget_beta (d₀ : SelectionData n) :
    ∃ c : ℝ, 0 < c ∧ ∀ d : SelectionData n,
      selectionFixedKey d = selectionFixedKey d₀ → d.β ≤ 1 →
      c * d.β ^ selectionBetaExponent d ≤ selectionAdmissible d := by
  have hm0 := selectionM₀_nonneg d₀
  have hdiam := selectionAdm_diam_pos d₀
  have hM := d₀.beta_pos.trans_le d₀.beta_le
  have hC1 := d₀.hessian_normalized
  set S : ℝ := 1 + d₀.M + selectionM₀ d₀ + d₀.C₁ + Metric.diam d₀.K with hS
  have hSpos : 0 < S := by rw [hS]; positivity
  set c0 : ℝ := min (min d₀.ϑ (min d₀.strip d₀.loss)) (1 / S) with hc0
  have hc0pos : 0 < c0 := lt_min (lt_min d₀.theta_pos (lt_min d₀.strip_pos d₀.loss_pos))
    (by positivity)
  have hc01 : c0 ≤ 1 := (min_le_left _ _).trans ((min_le_left _ _).trans d₀.theta_le)
  have hinv : S ≤ c0⁻¹ := by
    have : c0 ≤ 1 / S := min_le_right _ _
    have h2 := inv_anti₀ hc0pos this
    simpa using h2
  obtain ⟨c', hc', H⟩ := adm_budget n d₀.μ d₀.ρ d₀.τ c0 0 d₀.n_pos d₀.μ_pos d₀.rho_mem
    d₀.tau_nonneg d₀.tau_gap hc0pos hc01 le_rfl
  refine ⟨c', hc', ?_⟩
  intro d hk hβ
  obtain ⟨hμ, hρ, hτ, hϑ, hs, hC, hMd, hl, hK, hM0⟩ := polyBudget_key hk
  have hβ0 := d.beta_pos
  have hfam : selectionFamilyBounds c0 d.β ⟨0, 0, 1, 0, 0, 0, 0, 0, by norm_num⟩ d := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [Real.rpow_zero, mul_one, hϑ]
      exact (min_le_left _ _).trans (min_le_left _ _)
    · simp only [Real.rpow_zero, mul_one, hs]
      exact (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
    · simp only [Real.rpow_one]
      nlinarith
    · simp only [Real.rpow_zero, mul_one, hl]
      exact (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
    · simp only [neg_zero, Real.rpow_zero, mul_one, hMd]
      linarith
    · simp only [neg_zero, Real.rpow_zero, mul_one, hM0]
      linarith
    · simp only [neg_zero, Real.rpow_zero, mul_one, hC]
      linarith
    · simp only [neg_zero, Real.rpow_zero, mul_one, hK]
      linarith
  have h := H ⟨0, 0, 1, 0, 0, 0, 0, 0, by norm_num⟩ rfl d.β hβ0 hβ d hμ hρ hτ hfam
  rw [polyBudget_exponent_beta n d₀.μ d₀.ρ d₀.μ_pos d₀.rho_mem, ← hμ, ← hρ] at h
  exact h

/-! ### `displacement_power` -/

theorem polyBudget_CDelta {d d₀ : SelectionData n}
    (hk : selectionFixedKey d = selectionFixedKey d₀) :
    selectionCDelta d = selectionCDelta d₀ := by
  obtain ⟨hμ, hρ, hτ, hϑ, hs, hC, hMd, hl, hK, hM0⟩ := polyBudget_key hk
  simp only [selectionCDelta, selectionT₀, hμ, hτ, hs, hC]

theorem polyBudget_CGamma {d d₀ : SelectionData n}
    (hk : selectionFixedKey d = selectionFixedKey d₀) :
    selectionCGamma d = selectionCGamma d₀ := by
  obtain ⟨hμ, hρ, hτ, hϑ, hs, hC, hMd, hl, hK, hM0⟩ := polyBudget_key hk
  simp only [selectionCGamma, selectionChat, hμ, hρ, hτ, hϑ, hMd, hl, hK]

/-- Both K5 and K6, with one family witness and constants uniform in h, beta, epsilon and f at fixed key. -/
theorem displacement_power (d₀ : SelectionData n) :
    ∃ cD cstar : ℝ, 0 < cD ∧ 0 < cstar ∧ ∀ d : SelectionData n,
      selectionFixedKey d = selectionFixedKey d₀ → d.β ≤ 1 →
      cstar * d.β ^ selectionBetaExponent d ≤ selectionAdmissible d ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ selectionAdmissible d →
      ∀ f : SelectionPhaseC n → ℂ, SelectionPerturbation d f ε →
      ∃ o : SelectionEvaluationOutput d f ε,
        ∀ b ∈ o.Kinf, ∀ θ, ‖o.defect b θ‖ ≤
          cD * Real.sqrt ε * d.β ^ (-((d.μ : ℝ) + 1) / d.ρ) := by
  obtain ⟨c, hc, hB⟩ := adm_budget_beta d₀
  have hn : (0 : ℝ) < n := by exact_mod_cast d₀.n_pos
  have hT : 0 < selectionT₀ d₀ := lt_of_lt_of_le one_pos (selectionT₀_pos d₀)
  have hs24 : 0 < d₀.strip / 24 := by linarith [d₀.strip_pos]
  have hCQ : 0 < selectionCQ n := by unfold selectionCQ; positivity
  have hCD : 0 < selectionCDelta d₀ := by
    have := d₀.hessian_normalized
    unfold selectionCDelta
    positivity
  have hCG : 0 < selectionCGamma d₀ := by
    unfold selectionCGamma
    have : 0 < 2 * Real.sqrt n * (4 : ℝ) ^ ((d₀.ρ : ℝ)⁻¹) := by
      have := Real.sqrt_pos.2 hn
      positivity
    exact mul_pos two_pos (lt_max_of_lt_left this)
  refine ⟨selectionCDelta d₀ * selectionCGamma d₀, c, mul_pos hCD hCG, hc, ?_⟩
  intro d hk hβ
  refine ⟨hB d hk hβ, ?_⟩
  intro ε he hsm f hf
  obtain ⟨o⟩ := evaluation_bilipschitz d ε he hsm f hf
  refine ⟨o, fun b hb θ => ?_⟩
  have h := (o.displacement b hb θ).trans (selectionDelta_le_power d ε he hsm hβ)
  rwa [polyBudget_CDelta hk, polyBudget_CGamma hk] at h

end KAM.Planetary

end
