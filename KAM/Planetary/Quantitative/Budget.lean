/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Quantitative.Interface
public import KAM.Planetary.Quantitative.BudgetCompare
public import KAM.Planetary.Quantitative.BudgetPower

/-!
# Quantitative budget: the `beta` power law and the K5/K6 statements (P11C-Q4)

`qb_beta` (`stepP:p11a:qb-beta`: the threshold of the data with `beta` replaced by `b` is at least
`c * b ^ B0`), `p11c_budget` (K5: `qb_comp`, `qb_mono` and `qb_beta` together) and
`displacement_power_flat` (K6: the displacement is at most `cD * eps ^ (1/2) * b ^ (-G0)`).
Both power laws are specializations of `qb_poly` and `qbPoly_gamma_lower` to the rates
`a_beta = 1` and all other rates `0`.
-/

@[expose] public noncomputable section
open Set Metric Real MeasureTheory Function
open scoped ContDiff Topology
namespace KAM.Planetary

def p11c_G0 {N : ℕ} (d : QuantitativeData N) : ℝ := (d.mu + 1 : ℝ) / d.rho
def p11c_B0 {N : ℕ} (d : QuantitativeData N) : ℝ :=
  2 * max (2 * p11c_G0 d) (1 + d.mu * p11c_G0 d)

/-- The rates of the `beta` budget: only `beta` varies. -/
def qbBetaRates : BudgetRates where
  vartheta := 0
  s := 0
  beta := 1
  loss := 0
  M := 0
  M0 := 0
  C1 := 0
  diam := 0

theorem qbBetaRates_valid : qbBetaRates.Valid := by
  simp [BudgetRates.Valid, qbBetaRates]

theorem qbBeta_rateG {N : ℕ} (d : QuantitativeData N) (hd : d.NumericalValid) :
    qbBetaRates.rateG N d.mu d.rho = p11c_G0 d := by
  obtain ⟨-, hmu, hrho, -⟩ := hd
  have hr : (0 : ℝ) < d.rho := by rcases hrho with h | h <;> simp [h]
  have hm : (1 : ℝ) ≤ d.mu := by exact_mod_cast hmu
  have hm0 : (0 : ℝ) < d.mu := by linarith
  have hD : qbBetaRates.rateD N d.mu = 1 + 1 / (d.mu : ℝ) := by
    simp [BudgetRates.rateD, qbBetaRates]
  have h1 : (d.mu : ℝ) / d.rho * (qbBetaRates.loss + qbBetaRates.rateD N d.mu) =
      p11c_G0 d := by
    rw [hD]; simp only [qbBetaRates, p11c_G0]; field_simp; ring
  unfold BudgetRates.rateG
  rw [h1]
  refine max_eq_right ?_
  simp only [qbBetaRates, p11c_G0]
  rw [div_le_div_iff_of_pos_right hr]; linarith

theorem qbBeta_exponent {N : ℕ} (d : QuantitativeData N) (hd : d.NumericalValid) :
    qbBetaRates.exponent N d.mu d.rho d.tau = p11c_B0 d := by
  have hG := qbBeta_rateG d hd
  have hG0 : 0 ≤ p11c_G0 d := by
    obtain ⟨-, -, hrho, -⟩ := hd
    have hr : (0 : ℝ) < d.rho := by rcases hrho with h | h <;> simp [h]
    unfold p11c_G0; positivity
  rw [BudgetRates.exponent_eq]
  have hL : qbBetaRates.rateL = 0 := by simp [BudgetRates.rateL, qbBetaRates]
  have hJ : qbBetaRates.rateJ N d.mu d.rho d.tau = p11c_G0 d := by
    unfold BudgetRates.rateJ
    rw [hG, hL]
    simpa [qbBetaRates] using hG0
  have hX : qbBetaRates.rateX N d.mu d.rho d.tau = p11c_G0 d := by
    unfold BudgetRates.rateX
    rw [hJ, hL]; exact max_eq_left hG0
  have hH : qbBetaRates.rateH N d.mu d.rho d.tau =
      max (2 * p11c_G0 d) (1 + d.mu * p11c_G0 d) := by
    unfold BudgetRates.rateH
    rw [hJ, hX, hG, hL]
    simp only [qbBetaRates]
    have : max (p11c_G0 d) (p11c_G0 d + (↑N + 1) * 0 + d.tau * 0 + p11c_G0 d) =
        2 * p11c_G0 d := by
      rw [max_eq_right (by linarith)]; ring
    rw [this]; congr 1; ring
  rw [hH]; simp [qbBetaRates, p11c_B0]

/-- The constant `c0` of the rate bounds: it is below every datum and the inverse bounds. -/
def qbBetaC {N : ℕ} (d : QuantitativeData N) : ℝ :=
  min (min (min 1 d.vartheta) (min d.s d.epsLoss))
    (min (min d.M⁻¹ d.M0⁻¹) (min d.C1⁻¹ d.diameter⁻¹))

theorem qbBetaC_pos {N : ℕ} {d : QuantitativeData N} (hd : d.NumericalValid) : 0 < qbBetaC d := by
  have hdi := qbPoly_diameter_pos d hd
  obtain ⟨-, -, -, -, -, hv, -, hs, -, hC, hM0, hb, hbM, -, he, -⟩ := hd
  have hM : 0 < d.M := lt_of_lt_of_le hb hbM
  have : 0 < d.C1 := by linarith
  unfold qbBetaC
  refine lt_min (lt_min (lt_min one_pos hv) (lt_min hs he))
    (lt_min (lt_min (inv_pos.2 hM) (inv_pos.2 hM0)) (lt_min (inv_pos.2 this) (inv_pos.2 hdi)))

theorem qbBeta_rateBounds {N : ℕ} {d : QuantitativeData N} (hd : d.NumericalValid) {b : ℝ}
    (hb : 0 < b) :
    RateBounds qbBetaRates (qbBetaC d) b { d with beta := b } := by
  have hdi := qbPoly_diameter_pos d hd
  have hc := qbBetaC_pos hd
  obtain ⟨-, -, -, -, -, hv, -, hs, -, hC, hM0, hb0, hbM0, -, he, -⟩ := hd
  have hM : 0 < d.M := lt_of_lt_of_le hb0 hbM0
  have hC0 : 0 < d.C1 := by linarith
  have inv : ∀ x : ℝ, 0 < x → qbBetaC d ≤ x⁻¹ → x ≤ (qbBetaC d)⁻¹ :=
    fun x hx h => (le_inv_comm₀ hc hx).1 h
  have h1 : qbBetaC d ≤ 1 := (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have hv' : qbBetaC d ≤ d.vartheta :=
    (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have hs' : qbBetaC d ≤ d.s :=
    (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have he' : qbBetaC d ≤ d.epsLoss :=
    (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hM' : qbBetaC d ≤ d.M⁻¹ :=
    (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have hM0' : qbBetaC d ≤ d.M0⁻¹ :=
    (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have hC' : qbBetaC d ≤ d.C1⁻¹ :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hdi' : qbBetaC d ≤ d.diameter⁻¹ :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  simp only [RateBounds, qbBetaRates, neg_zero, Real.rpow_zero, mul_one, Real.rpow_one]
  refine ⟨hv', hs', ?_, he', ?_, ?_, ?_, ?_⟩
  · calc qbBetaC d * b ≤ 1 * b := by gcongr
      _ = b := one_mul b
  · exact inv _ hM hM'
  · exact inv _ hM0 hM0'
  · exact inv _ hC0 hC'
  · exact inv _ hdi hdi'

theorem qbBeta_valid {N : ℕ} {d : QuantitativeData N} (hd : d.NumericalValid) {b : ℝ}
    (hb : 0 < b) (hbM : b ≤ d.M) : ({ d with beta := b } : QuantitativeData N).NumericalValid := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, -, -, h14, h15, h16⟩ := hd
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, hb, hbM, h14, h15, h16⟩

theorem qb_beta {N : ℕ} (d : QuantitativeData N) (hd : d.NumericalValid) :
    ∃ c : ℝ, 0 < c ∧ ∀ b ∈ Ioc (0 : ℝ) (min 1 d.M),
      c * b ^ p11c_B0 d ≤ thresholds { d with beta := b } := by
  obtain ⟨hN, hmu, hrho, htau, htau0, -⟩ := id hd
  have hc := qbBetaC_pos hd
  have h1 : qbBetaC d ≤ 1 := (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  obtain ⟨c', hc', hbound⟩ := qb_poly N d.mu d.rho d.tau (qbBetaC d) 0 hN hmu hrho htau htau0 hc
    h1 le_rfl
  refine ⟨c', hc', fun b hb => ?_⟩
  obtain ⟨hb0, hb1⟩ := hb
  have hbM : b ≤ d.M := hb1.trans (min_le_right _ _)
  have hb1' : b ≤ 1 := hb1.trans (min_le_left _ _)
  have := hbound qbBetaRates qbBetaRates_valid rfl { d with beta := b } (qbBeta_valid hd hb0 hbM)
    rfl rfl rfl b ⟨hb0, hb1'⟩ (qbBeta_rateBounds hd hb0)
  rwa [qbBeta_exponent d hd] at this

theorem p11c_budget {N : ℕ} (d : QuantitativeData N) (hd : d.NumericalValid) :
    (∀ M0' : ℝ, 0 < M0' → M0' ≤ d.M0 →
      0 < thresholds d ∧ thresholds d ≤ p11c_oldThreshold { d with M0 := M0' }) ∧
    (∀ d' : QuantitativeData N, d'.NumericalValid → BudgetOrder d d' →
      d.gamma ≤ d'.gamma ∧ thresholds d ≤ thresholds d') ∧
    ∃ c : ℝ, 0 < c ∧ ∀ b ∈ Ioc (0 : ℝ) (min 1 d.M),
      c * b ^ p11c_B0 d ≤ thresholds { d with beta := b } :=
  ⟨fun M0' h0 hM => qb_comp d hd M0' h0 hM, fun d' hd' h => qb_mono d d' hd hd' h, qb_beta d hd⟩

theorem displacement_power_flat {N : ℕ} (d : QuantitativeData N) (hd : d.Valid)
    (cDelta : ℝ) (hc : 0 < cDelta) :
    ∃ cD : ℝ, 0 < cD ∧ ∀ b ∈ Ioc (0 : ℝ) (min 1 d.M), ∀ eps : ℝ, 0 ≤ eps →
      p11c_displacement { d with beta := b } cDelta eps ≤
        cD * eps ^ (1 / 2 : ℝ) * b ^ (-p11c_G0 d) := by
  obtain ⟨hnv, -, -⟩ := id hd
  have hc0 := qbBetaC_pos hnv
  have h1 : qbBetaC d ≤ 1 := (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  obtain ⟨hN, hmu, hrho, htau, -⟩ := id hnv
  obtain ⟨k, hk, hgam⟩ := qbPoly_gamma_lower N d.mu d.rho d.tau (qbBetaC d) hN hmu hrho htau hc0
  refine ⟨cDelta / k, div_pos hc hk, fun b hb eps heps => ?_⟩
  obtain ⟨hb0, hb1⟩ := hb
  have hbM : b ≤ d.M := hb1.trans (min_le_right _ _)
  have hb1' : b ≤ 1 := hb1.trans (min_le_left _ _)
  have hG := hgam 0 1 0 0 0 le_rfl zero_le_one le_rfl le_rfl le_rfl { d with beta := b }
    (qbBeta_valid hd.1 hb0 hbM) rfl rfl rfl b ⟨hb0, hb1'⟩
  have hR := qbBeta_rateBounds hd.1 hb0
  simp only [RateBounds, qbBetaRates] at hR
  obtain ⟨hv, -, hbb, he, hM, -, -, hdi⟩ := hR
  have hexp : max ((1 : ℝ) / d.rho) ((d.mu : ℝ) / d.rho *
      (0 + ((N : ℝ) * 0 + 0 + 0 + (1 + 1 / (d.mu : ℝ)) * 1))) = p11c_G0 d := by
    have := qbBeta_rateG d hd.1
    simpa [BudgetRates.rateG, BudgetRates.rateD, qbBetaRates] using this
  have hgam' : k * b ^ p11c_G0 d ≤ ({ d with beta := b } : QuantitativeData N).gamma := by
    rw [← hexp]
    exact hG (by simpa using hv) (by simpa using hbb) (by simpa using he) (by simpa using hM)
      (by simpa using hdi)
  have hgpos : 0 < k * b ^ p11c_G0 d := mul_pos hk (Real.rpow_pos_of_pos hb0 _)
  have hs : Real.sqrt eps = eps ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow eps
  unfold p11c_displacement
  refine (min_le_right _ _).trans ?_
  calc cDelta * Real.sqrt eps / ({ d with beta := b } : QuantitativeData N).gamma
      ≤ cDelta * Real.sqrt eps / (k * b ^ p11c_G0 d) := by
        gcongr
    _ = cDelta / k * eps ^ (1 / 2 : ℝ) * b ^ (-p11c_G0 d) := by
        rw [hs, Real.rpow_neg hb0.le]; field_simp

end KAM.Planetary
