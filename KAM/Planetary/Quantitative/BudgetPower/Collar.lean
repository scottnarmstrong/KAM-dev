/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Quantitative.BudgetPower.Gamma

/-!
# Polynomial bounds for `tbar`, `tflat`, `xibar` (P11C-Q3, fragments `ab_T0`, `ab_t0`)

`tbar ≤ C u^{-L}` (`stepP:p11a:ab-T0`), `tflat ≥ k u^J` and `xibar ≤ C u^{-X}`
(`stepP:p11a:ab-t0`).
-/

@[expose] public noncomputable section
open Set Metric Real
namespace KAM.Planetary

theorem qbPoly_tbar_bound (N mu : ℕ) (tau c asRate : ℝ) (hN : 1 ≤ N) (hc : 0 < c)
    (hc1 : c ≤ 1) (has : 0 ≤ asRate) :
    ∃ C : ℝ, 0 < C ∧ ∀ d : QuantitativeData N, d.mu = mu → d.tau = tau → 0 < d.s → d.s ≤ 1 →
      ∀ u ∈ Ioc (0 : ℝ) 1, c * u ^ asRate ≤ d.s →
        1 ≤ d.tbar ∧ d.tbar ≤ C * u ^ (-(if 0 < asRate then asRate + 1 else 0)) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  set A0c : ℝ := |Real.log (16 * QuantitativeData.cN N /
    (2 : ℝ) ^ (-(2 * (2 * (tau + 1) * ((mu : ℝ) + 1) + N + 4))))| with hA0c
  set Lc : ℝ := Real.log (32 * N / c) with hLc
  have hLc0 : 0 ≤ Lc := Real.log_nonneg (by rw [le_div_iff₀ hc]; nlinarith)
  have hpi := Real.pi_pos
  refine ⟨1 + 16 / (π * c) * (A0c + N * (Lc + asRate)), by positivity, ?_⟩
  intro d hmu' htau' hs0 hs1 u hu hcs
  obtain ⟨hu0, hu1⟩ := hu
  have hA0 : |d.A0| = A0c := by
    unfold QuantitativeData.A0 QuantitativeData.varpi
    rw [hmu', htau']
  have hcu : 0 < c * u ^ asRate := mul_pos hc (Real.rpow_pos_of_pos hu0 _)
  have hlog1 : 0 ≤ Real.log (32 * N / d.s) :=
    Real.log_nonneg (by rw [le_div_iff₀ hs0]; nlinarith)
  have hlogbd : Real.log (32 * N / d.s) ≤ Lc + asRate * Real.log u⁻¹ := by
    have h1 : 32 * (N : ℝ) / d.s ≤ 32 * N / (c * u ^ asRate) :=
      div_le_div_of_nonneg_left (by positivity) hcu hcs
    have h2 : 32 * (N : ℝ) / (c * u ^ asRate) = (32 * N / c) * (u⁻¹) ^ asRate := by
      rw [Real.inv_rpow hu0.le]; field_simp
    have hpos : 0 < 32 * (N : ℝ) / d.s := by positivity
    calc Real.log (32 * N / d.s) ≤ Real.log (32 * N / (c * u ^ asRate)) :=
          Real.log_le_log hpos h1
      _ = Lc + asRate * Real.log u⁻¹ := by
          rw [h2, Real.log_mul (by positivity) (by positivity),
            Real.log_rpow (inv_pos.mpr hu0)]
  have hinv : 16 / (π * d.s) ≤ 16 / (π * c) * u ^ (-asRate) := by
    have h1 : 16 / (π * d.s) ≤ 16 / (π * (c * u ^ asRate)) :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity)
        (mul_le_mul_of_nonneg_left hcs hpi.le)
    have h2 : 16 / (π * (c * u ^ asRate)) = 16 / (π * c) * u ^ (-asRate) := by
      rw [Real.rpow_neg hu0.le]; field_simp
    linarith
  have hlogu : 0 ≤ Real.log u⁻¹ := Real.log_nonneg (one_le_inv_iff₀.mpr ⟨hu0, hu1⟩)
  constructor
  · unfold QuantitativeData.tbar
    rw [hA0]
    have : 0 ≤ 16 / (π * d.s) * (A0c + N * Real.log (32 * N / d.s)) := by positivity
    linarith
  · unfold QuantitativeData.tbar
    rw [hA0]
    have hnn : 0 ≤ A0c + N * Real.log (32 * N / d.s) := by positivity
    have hstep : 16 / (π * d.s) * (A0c + N * Real.log (32 * N / d.s)) ≤
        16 / (π * c) * u ^ (-asRate) * (A0c + N * (Lc + asRate * Real.log u⁻¹)) := by
      apply mul_le_mul hinv _ hnn (by positivity)
      have := mul_le_mul_of_nonneg_left hlogbd hN0.le
      linarith
    by_cases hpos : 0 < asRate
    · rw [if_pos hpos]
      set E := u ^ (-(asRate + 1)) with hE
      have hE1 : u ^ (-asRate) * u⁻¹ = E := by
        rw [hE, neg_add, Real.rpow_add hu0, Real.rpow_neg_one]
      have hEa : u ^ (-asRate) ≤ E := by
        rw [hE]; exact qbPoly_negpow_mono hu0 hu1 (by linarith)
      have hE0 : 1 ≤ E := qbPoly_negpow_ge_one hu0 hu1 (by linarith)
      have hv : 1 ≤ u⁻¹ := one_le_inv_iff₀.mpr ⟨hu0, hu1⟩
      have hlogle : Real.log u⁻¹ ≤ u⁻¹ := by
        have := Real.log_le_sub_one_of_pos (inv_pos.mpr hu0); linarith
      have hF0 : 0 ≤ u ^ (-asRate) := (Real.rpow_pos_of_pos hu0 _).le
      have hA00 : 0 ≤ A0c := abs_nonneg _
      have h2 : Lc + asRate * Real.log u⁻¹ ≤ (Lc + asRate) * u⁻¹ := by
        nlinarith [mul_le_mul_of_nonneg_left hlogle has, mul_nonneg hLc0 (sub_nonneg.mpr hv)]
      have h3 : u ^ (-asRate) * (A0c + N * (Lc + asRate * Real.log u⁻¹)) ≤
          E * (A0c + N * (Lc + asRate)) := by
        calc u ^ (-asRate) * (A0c + N * (Lc + asRate * Real.log u⁻¹))
            ≤ u ^ (-asRate) * (A0c + N * ((Lc + asRate) * u⁻¹)) :=
              mul_le_mul_of_nonneg_left (by nlinarith [mul_le_mul_of_nonneg_left h2 hN0.le]) hF0
          _ ≤ (u ^ (-asRate) * u⁻¹) * (A0c + N * (Lc + asRate)) := by
              nlinarith [mul_nonneg (mul_nonneg hF0 hA00) (sub_nonneg.mpr hv)]
          _ = _ := by rw [hE1]
      have h4 : 16 / (π * c) * u ^ (-asRate) * (A0c + N * (Lc + asRate * Real.log u⁻¹)) ≤
          16 / (π * c) * (E * (A0c + N * (Lc + asRate))) := by
        rw [mul_assoc]; exact mul_le_mul_of_nonneg_left h3 (by positivity)
      have hK : 0 ≤ 16 / (π * c) * (A0c + N * (Lc + asRate)) := by positivity
      nlinarith [hstep, h4, mul_le_mul_of_nonneg_left hE0 hK]
    · have h0 : asRate = 0 := le_antisymm (not_lt.mp hpos) has
      rw [if_neg hpos]
      subst h0
      simp at hstep ⊢
      linarith

/-- Lower bound for `thetaMax` (`stepP:p11a:ab-lam`, third term). -/
theorem qbPoly_thetaMax_lower (N mu rho : ℕ) (c : ℝ) (hrho : rho = 1 ∨ rho = 2) (hc : 0 < c)
    (hc1 : c ≤ 1) :
    ∀ aβ aM0 : ℝ, 0 ≤ aβ → 0 ≤ aM0 → ∀ d : QuantitativeData N, d.mu = mu → d.rho = rho →
      0 < d.beta → 0 < d.M0 → ∀ u ∈ Ioc (0 : ℝ) 1, c * u ^ aβ ≤ d.beta →
        d.M0 ≤ c⁻¹ * u ^ (-aM0) →
          c ^ 2 / 2 ^ (mu + 3) * u ^ (aβ + aM0) ≤ d.thetaMax := by
  intro aβ aM0 haβ haM0 d hmu' hrho' hβ0 hM00 u hu hβ hM0
  obtain ⟨hu0, hu1⟩ := hu
  have hupos : ∀ e : ℝ, 0 < u ^ e := fun e => Real.rpow_pos_of_pos hu0 e
  have hP : 0 < (2 : ℝ) ^ (mu + 3) := by positivity
  have hs1 : u ^ (aβ + aM0) ≤ u ^ aβ := qbPoly_pow_anti hu0 hu1 (by linarith)
  have hs2 : u ^ (aβ + aM0) ≤ 1 := qbPoly_pow_le_one hu0 hu1 (by linarith)
  have hθβ : c ^ 2 / 2 ^ (mu + 3) * u ^ (aβ + aM0) ≤ d.beta / 2 := by
    have h8 : (8 : ℝ) ≤ 2 ^ (mu + 3) := by
      calc (8 : ℝ) = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ (mu + 3) := pow_le_pow_right₀ (by norm_num) (by omega)
    have h1 : c ^ 2 / 2 ^ (mu + 3) ≤ c / 8 := by
      rw [div_le_div_iff₀ hP (by norm_num)]; nlinarith
    calc c ^ 2 / 2 ^ (mu + 3) * u ^ (aβ + aM0) ≤ c / 8 * u ^ aβ :=
          mul_le_mul h1 hs1 (hupos _).le (by positivity)
      _ ≤ d.beta / 2 := by nlinarith [hupos aβ]
  unfold QuantitativeData.thetaMax
  rw [hmu', hrho']
  by_cases h1 : rho = 1
  · rw [if_pos h1]; exact hθβ
  · rw [if_neg h1]
    refine le_min (hθβ.trans (by linarith)) ?_
    have hden : 0 < 2 ^ (mu + 1) * (2 * d.M0 + d.beta) := by positivity
    rw [le_div_iff₀ hden]
    have h2 : (2 : ℝ) ^ (mu + 1) * 4 = 2 ^ (mu + 3) := by ring
    by_cases hb : d.beta ≤ 2 * d.M0
    · -- ratio ≥ beta / (2^(mu+3) M0)
      have key : c ^ 2 / 2 ^ (mu + 3) * u ^ (aβ + aM0) * (2 ^ (mu + 1) * (2 * d.M0 + d.beta))
          ≤ d.beta := by
        have e1 : u ^ (aβ + aM0) * u ^ (-aM0) = u ^ aβ := by
          rw [← Real.rpow_add hu0]; congr 1; ring
        have e2 : d.M0 * u ^ aM0 ≤ c⁻¹ := by
          have := mul_le_mul_of_nonneg_right hM0 (hupos aM0).le
          rwa [mul_assoc, ← Real.rpow_add hu0, neg_add_cancel, Real.rpow_zero, mul_one] at this
        have e3 : u ^ (aβ + aM0) * d.M0 ≤ c⁻¹ * u ^ aβ := by
          have : u ^ (aβ + aM0) * d.M0 = u ^ aβ * (d.M0 * u ^ aM0) := by
            rw [Real.rpow_add hu0]; ring
          rw [this]; nlinarith [hupos aβ]
        have e4 : 2 * d.M0 + d.beta ≤ 4 * d.M0 := by linarith
        calc c ^ 2 / 2 ^ (mu + 3) * u ^ (aβ + aM0) * (2 ^ (mu + 1) * (2 * d.M0 + d.beta))
            ≤ c ^ 2 / 2 ^ (mu + 3) * u ^ (aβ + aM0) * (2 ^ (mu + 1) * (4 * d.M0)) := by
              gcongr
          _ = c ^ 2 * (u ^ (aβ + aM0) * d.M0) := by
              field_simp; rw [← h2]
          _ ≤ c ^ 2 * (c⁻¹ * u ^ aβ) := by gcongr
          _ = c * u ^ aβ := by field_simp
          _ ≤ d.beta := hβ
      exact key
    · rw [not_le] at hb
      have e4 : 2 * d.M0 + d.beta ≤ 2 * d.beta := by linarith
      calc c ^ 2 / 2 ^ (mu + 3) * u ^ (aβ + aM0) * (2 ^ (mu + 1) * (2 * d.M0 + d.beta))
          ≤ 1 / 2 ^ (mu + 3) * 1 * (2 ^ (mu + 1) * (2 * d.beta)) := by
            gcongr
            · nlinarith
          _ ≤ d.beta := by
            field_simp
            rw [show (2 : ℝ) ^ (mu + 3) = 2 ^ (mu + 1) * 4 by ring]
            nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) (mu + 1)]

end KAM.Planetary
