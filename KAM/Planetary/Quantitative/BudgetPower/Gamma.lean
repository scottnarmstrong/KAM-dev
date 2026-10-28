/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Quantitative.BudgetPower.Positivity
public import KAM.Planetary.Quantitative.BudgetPower.Rates

/-!
# Polynomial lower bound for the loss `gamma` (P11C-Q3, fragment `ab_gamma`)

The Diophantine constant `cDio` is positive and at most `C * u ^ (-D)`, hence the loss
`gamma` is at least `k * u ^ G` (`stepP:p11a:ab-gamma`).
-/

@[expose] public noncomputable section
open Set Metric Real
namespace KAM.Planetary

theorem qbPoly_gap_pos (N mu rho : ℕ) (tau : ℝ) (hmu : 1 ≤ mu) (hrho : rho = 1 ∨ rho = 2)
    (htau : (N : ℝ) * mu / rho - 1 < tau) : 0 < (rho : ℝ) * (tau + 1) / mu - N := by
  have hr : (0 : ℝ) < rho := by rcases hrho with h | h <;> simp [h]
  have hm : (0 : ℝ) < mu := by exact_mod_cast hmu
  have h1 : (N : ℝ) * mu / rho < tau + 1 := by linarith
  rw [div_lt_iff₀ hr] at h1
  have h2 : (N : ℝ) < rho * (tau + 1) / mu := by
    rw [lt_div_iff₀ hm]; linarith
  linarith

/-- `cDio` is positive and polynomially bounded: `cDio ≤ C u^{-D}`. -/
theorem qbPoly_cDio_bound (N mu rho : ℕ) (tau c : ℝ) (hN : 1 ≤ N) (hmu : 1 ≤ mu)
    (hrho : rho = 1 ∨ rho = 2) (htau : (N : ℝ) * mu / rho - 1 < tau) (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧ ∀ aϑ aβ aM ad : ℝ, 0 ≤ aϑ → 0 ≤ aβ → 0 ≤ aM → 0 ≤ ad →
      ∀ d : QuantitativeData N, d.NumericalValid → d.mu = mu → d.rho = rho → d.tau = tau →
        ∀ u ∈ Ioc (0 : ℝ) 1, c * u ^ aϑ ≤ d.vartheta → c * u ^ aβ ≤ d.beta →
          d.M ≤ c⁻¹ * u ^ (-aM) → d.diameter ≤ c⁻¹ * u ^ (-ad) →
            0 < d.cDio ∧
              d.cDio ≤ C * u ^ (-((N : ℝ) * ad + aM + aϑ + (1 + 1 / (mu : ℝ)) * aβ)) := by
  have hmu0 : (0 : ℝ) < mu := by exact_mod_cast hmu
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hsN : 0 < √(N : ℝ) := Real.sqrt_pos.mpr hN0
  have hgap := qbPoly_gap_pos N mu rho tau hmu hrho htau
  have hc' : 0 < c⁻¹ := inv_pos.mpr hc
  set K0 : ℝ := (2 : ℝ) ^ (N + 2) * mu * (N : ℝ) ^ ((rho : ℝ) / (2 * mu)) * 2 * 3 ^ (N - 1) *
    (1 + 1 / ((rho : ℝ) * (tau + 1) / mu - N)) with hK0
  have hK0pos : 0 < K0 := by
    have : 0 < 1 + 1 / ((rho : ℝ) * (tau + 1) / mu - N) := by positivity
    have h2 : (0 : ℝ) < (N : ℝ) ^ ((rho : ℝ) / (2 * mu)) := Real.rpow_pos_of_pos hN0 _
    positivity
  set K3 : ℝ := 1 + 4 * √(N : ℝ) * c⁻¹ + √(N : ℝ) * c⁻¹ * c⁻¹ with hK3
  refine ⟨K0 * (((√(N : ℝ) * c⁻¹) ^ (N - 1)) * (c⁻¹ * c⁻¹) * K3 * c ^ (-(1 / (mu : ℝ)))),
    by positivity, ?_⟩
  intro aϑ aβ aM ad haϑ haβ haM had d hd hmu' hrho' htau' u hu hϑ hβ hM hdiam
  obtain ⟨hu0, hu1⟩ := hu
  have hdpos := qbPoly_diameter_pos d hd
  obtain ⟨-, -, -, -, -, hϑ0, -, -, -, -, -, hβ0, hβM, -, -, -⟩ := hd
  have hM0 : 0 < d.M := lt_of_lt_of_le hβ0 hβM
  have hform : d.cDio = K0 * (((√(N : ℝ) * d.diameter) ^ (N - 1)) * (d.M / d.beta) *
      (1 + (4 + 1 / d.vartheta) * √(N : ℝ) * d.diameter) * d.beta ^ (-(1 / (mu : ℝ)))) := by
    unfold QuantitativeData.cDio
    rw [hmu', hrho', htau', hK0]
    ring
  have hcu : ∀ e : ℝ, 0 < c * u ^ e := fun e => mul_pos hc (Real.rpow_pos_of_pos hu0 e)
  -- P1
  have hP1 : (√(N : ℝ) * d.diameter) ^ (N - 1) ≤
      (√(N : ℝ) * c⁻¹) ^ (N - 1) * u ^ (-(ad * ((N : ℝ) - 1))) := by
    calc (√(N : ℝ) * d.diameter) ^ (N - 1)
        ≤ (√(N : ℝ) * (c⁻¹ * u ^ (-ad))) ^ (N - 1) :=
          pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left hdiam hsN.le) _
      _ = (√(N : ℝ) * c⁻¹) ^ (N - 1) * (u ^ (-ad)) ^ (N - 1) := by
          rw [← mul_assoc, mul_pow]
      _ = _ := by
          congr 1
          rw [← Real.rpow_natCast, ← Real.rpow_mul hu0.le]
          congr 1
          rw [Nat.cast_sub hN]; push_cast; ring
  -- P2
  have hP2 : d.M / d.beta ≤ (c⁻¹ * c⁻¹) * u ^ (-(aM + aβ)) := by
    have h1 : d.M / d.beta ≤ d.M / (c * u ^ aβ) :=
      div_le_div_of_nonneg_left hM0.le (hcu aβ) hβ
    have h2 : d.M / (c * u ^ aβ) ≤ (c⁻¹ * u ^ (-aM)) / (c * u ^ aβ) :=
      div_le_div_of_nonneg_right hM (hcu aβ).le
    have h3 : (c⁻¹ * u ^ (-aM)) / (c * u ^ aβ) = (c⁻¹ * c⁻¹) * u ^ (-(aM + aβ)) := by
      rw [neg_add, Real.rpow_add hu0, Real.rpow_neg hu0.le aβ]
      field_simp
    linarith
  -- P3
  have hP3 : 1 + (4 + 1 / d.vartheta) * √(N : ℝ) * d.diameter ≤ K3 * u ^ (-(aϑ + ad)) := by
    have hE : u ^ (-(aϑ + ad)) = u ^ (-aϑ) * u ^ (-ad) := by
      rw [neg_add, Real.rpow_add hu0]
    have hE1 := qbPoly_negpow_ge_one hu0 hu1 haϑ
    have hE2 := qbPoly_negpow_ge_one hu0 hu1 had
    have hinv : 1 / d.vartheta ≤ c⁻¹ * u ^ (-aϑ) := by
      have : 1 / d.vartheta ≤ 1 / (c * u ^ aϑ) := one_div_le_one_div_of_le (hcu aϑ) hϑ
      have h' : 1 / (c * u ^ aϑ) = c⁻¹ * u ^ (-aϑ) := by
        rw [Real.rpow_neg hu0.le]; have := Real.rpow_pos_of_pos hu0 aϑ; field_simp
      linarith
    set E1 := u ^ (-aϑ)
    set E2 := u ^ (-ad)
    have h1 : (4 + 1 / d.vartheta) * √(N : ℝ) * d.diameter ≤
        (4 + c⁻¹ * E1) * √(N : ℝ) * (c⁻¹ * E2) := by
      gcongr
    have h2 : (4 + c⁻¹ * E1) * √(N : ℝ) * (c⁻¹ * E2) =
        4 * √(N : ℝ) * c⁻¹ * E2 + √(N : ℝ) * c⁻¹ * c⁻¹ * (E1 * E2) := by ring
    have h3 : E2 ≤ E1 * E2 := by nlinarith
    have h4 : 1 ≤ E1 * E2 := by nlinarith
    have hk1 : 0 ≤ 4 * √(N : ℝ) * c⁻¹ := by positivity
    have hk2 : 0 ≤ √(N : ℝ) * c⁻¹ * c⁻¹ := by positivity
    rw [hE, hK3]
    calc 1 + (4 + 1 / d.vartheta) * √(N : ℝ) * d.diameter
        ≤ 1 + (4 * √(N : ℝ) * c⁻¹ * E2 + √(N : ℝ) * c⁻¹ * c⁻¹ * (E1 * E2)) := by
          rw [← h2]; linarith
      _ ≤ 1 * (E1 * E2) + 4 * √(N : ℝ) * c⁻¹ * (E1 * E2) +
            √(N : ℝ) * c⁻¹ * c⁻¹ * (E1 * E2) := by
          have := mul_le_mul_of_nonneg_left h3 hk1
          linarith
      _ = _ := by ring
  -- P4
  have hP4 : d.beta ^ (-(1 / (mu : ℝ))) ≤ c ^ (-(1 / (mu : ℝ))) * u ^ (-(aβ / mu)) := by
    have hexp : (0 : ℝ) ≤ 1 / (mu : ℝ) := by positivity
    have h1 : (c * u ^ aβ) ^ (1 / (mu : ℝ)) ≤ d.beta ^ (1 / (mu : ℝ)) :=
      Real.rpow_le_rpow (hcu aβ).le hβ hexp
    have h2 : (c * u ^ aβ) ^ (1 / (mu : ℝ)) = c ^ (1 / (mu : ℝ)) * u ^ (aβ / mu) := by
      rw [Real.mul_rpow hc.le (Real.rpow_pos_of_pos hu0 _).le, ← Real.rpow_mul hu0.le]
      congr 2; ring
    have h3 : 0 < (c * u ^ aβ) ^ (1 / (mu : ℝ)) := Real.rpow_pos_of_pos (hcu aβ) _
    have h4 := inv_anti₀ h3 h1
    rw [Real.rpow_neg hβ0.le]
    refine h4.trans (le_of_eq ?_)
    rw [h2, mul_inv, Real.rpow_neg hc.le, Real.rpow_neg hu0.le]
  have hp1 : 0 < (√(N : ℝ) * d.diameter) ^ (N - 1) := pow_pos (mul_pos hsN hdpos) _
  have hp2 : 0 < d.M / d.beta := div_pos hM0 hβ0
  have hp3 : 0 < 1 + (4 + 1 / d.vartheta) * √(N : ℝ) * d.diameter := by positivity
  have hp4 : 0 < d.beta ^ (-(1 / (mu : ℝ))) := Real.rpow_pos_of_pos hβ0 _
  refine ⟨by rw [hform]; positivity, ?_⟩
  rw [hform]
  have hexp : -((N : ℝ) * ad + aM + aϑ + (1 + 1 / (mu : ℝ)) * aβ) =
      -(ad * ((N : ℝ) - 1)) + -(aM + aβ) + -(aϑ + ad) + -(aβ / mu) := by
    field_simp; ring
  rw [hexp, Real.rpow_add hu0, Real.rpow_add hu0, Real.rpow_add hu0]
  have hq := qbPoly_ub_mul (A := (√(N : ℝ) * c⁻¹) ^ (N - 1)) (B := c⁻¹ * c⁻¹)
    (w := u ^ (-(ad * ((N : ℝ) - 1)))) (z := u ^ (-(aM + aβ))) hp2.le (by positivity) hP1 hP2
  have hq2 := qbPoly_ub_mul (B := K3) (z := u ^ (-(aϑ + ad))) hp3.le (by positivity) hq hP3
  have hq3 := qbPoly_ub_mul (B := c ^ (-(1 / (mu : ℝ)))) (z := u ^ (-(aβ / mu))) hp4.le
    (by positivity) hq2 hP4
  refine (mul_le_mul_of_nonneg_left hq3 hK0pos.le).trans (le_of_eq ?_)
  ring

/-- `stepP:p11a:ab-gamma`: `gamma ≥ k u^G`. -/
theorem qbPoly_gamma_lower (N mu rho : ℕ) (tau c : ℝ) (hN : 1 ≤ N) (hmu : 1 ≤ mu)
    (hrho : rho = 1 ∨ rho = 2) (htau : (N : ℝ) * mu / rho - 1 < tau) (hc : 0 < c) :
    ∃ k : ℝ, 0 < k ∧ ∀ aϑ aβ aε aM ad : ℝ, 0 ≤ aϑ → 0 ≤ aβ → 0 ≤ aε → 0 ≤ aM → 0 ≤ ad →
      ∀ d : QuantitativeData N, d.NumericalValid → d.mu = mu → d.rho = rho → d.tau = tau →
        ∀ u ∈ Ioc (0 : ℝ) 1, c * u ^ aϑ ≤ d.vartheta → c * u ^ aβ ≤ d.beta →
          c * u ^ aε ≤ d.epsLoss → d.M ≤ c⁻¹ * u ^ (-aM) → d.diameter ≤ c⁻¹ * u ^ (-ad) →
            k * u ^ (max (aβ / rho) ((mu : ℝ) / rho *
              (aε + ((N : ℝ) * ad + aM + aϑ + (1 + 1 / (mu : ℝ)) * aβ)))) ≤ d.gamma := by
  obtain ⟨C, hC, hCd⟩ := qbPoly_cDio_bound N mu rho tau c hN hmu hrho htau hc
  have hr : (0 : ℝ) < rho := by rcases hrho with h | h <;> simp [h]
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hmu0 : (0 : ℝ) < mu := by exact_mod_cast hmu
  set kA : ℝ := (1 / 2 : ℝ) * (N : ℝ) ^ (-(1 / 2 : ℝ)) * (c / 4) ^ (1 / (rho : ℝ)) with hkA
  set kB : ℝ := (c / C) ^ ((mu : ℝ) / rho) with hkB
  have hkApos : 0 < kA := by positivity
  have hkBpos : 0 < kB := by positivity
  refine ⟨min kA kB / 2, by positivity, ?_⟩
  intro aϑ aβ aε aM ad haϑ haβ haε haM had d hd hmu' hrho' htau' u hu hϑ hβ hε hM hdiam
  obtain ⟨hu0, hu1⟩ := hu
  obtain ⟨hcpos, hcle⟩ := hCd aϑ aβ aM ad haϑ haβ haM had d hd hmu' hrho' htau' u ⟨hu0, hu1⟩
    hϑ hβ hM hdiam
  set D := (N : ℝ) * ad + aM + aϑ + (1 + 1 / (mu : ℝ)) * aβ with hD
  have hcu : ∀ e : ℝ, 0 < c * u ^ e := fun e => mul_pos hc (Real.rpow_pos_of_pos hu0 e)
  have hupos : ∀ e : ℝ, 0 < u ^ e := fun e => Real.rpow_pos_of_pos hu0 e
  -- first entry
  have hA : kA * u ^ (aβ / rho) ≤ (1 / 2 : ℝ) * (N : ℝ) ^ (-(1 / 2 : ℝ)) *
      (d.beta / 4) ^ (1 / (rho : ℝ)) := by
    have h1 : (c * u ^ aβ / 4) ^ (1 / (rho : ℝ)) ≤ (d.beta / 4) ^ (1 / (rho : ℝ)) :=
      Real.rpow_le_rpow (by have := hcu aβ; positivity) (by linarith) (by positivity)
    have h2 : (c * u ^ aβ / 4) ^ (1 / (rho : ℝ)) = (c / 4) ^ (1 / (rho : ℝ)) * u ^ (aβ / rho) := by
      rw [show c * u ^ aβ / 4 = c / 4 * u ^ aβ by ring,
        Real.mul_rpow (by positivity) (hupos _).le, ← Real.rpow_mul hu0.le]
      congr 2; ring
    have hk : 0 ≤ (1 / 2 : ℝ) * (N : ℝ) ^ (-(1 / 2 : ℝ)) := by positivity
    calc kA * u ^ (aβ / rho)
        = (1 / 2 : ℝ) * (N : ℝ) ^ (-(1 / 2 : ℝ)) *
            ((c / 4) ^ (1 / (rho : ℝ)) * u ^ (aβ / rho)) := by rw [hkA]; ring
      _ ≤ _ := by rw [← h2]; exact mul_le_mul_of_nonneg_left h1 hk
  -- second entry
  have hB : kB * u ^ ((mu : ℝ) / rho * (aε + D)) ≤
      (d.epsLoss / d.cDio) ^ ((mu : ℝ) / rho) := by
    have h1 : c * u ^ aε / (C * u ^ (-D)) ≤ d.epsLoss / d.cDio := by
      calc c * u ^ aε / (C * u ^ (-D)) ≤ d.epsLoss / (C * u ^ (-D)) :=
            div_le_div_of_nonneg_right hε (by have := hupos (-D); positivity)
        _ ≤ d.epsLoss / d.cDio := by
            have hε0 : 0 ≤ d.epsLoss := (mul_pos hc (hupos aε)).le.trans hε
            exact div_le_div_of_nonneg_left hε0 hcpos hcle
    have h2 : c * u ^ aε / (C * u ^ (-D)) = (c / C) * u ^ (aε + D) := by
      rw [Real.rpow_add hu0, Real.rpow_neg hu0.le D]
      have := hupos D
      field_simp
    have hex : (0 : ℝ) ≤ (mu : ℝ) / rho := by positivity
    have h3 := Real.rpow_le_rpow (by rw [h2]; have := hupos (aε + D); positivity) h1 hex
    rw [h2, Real.mul_rpow (by positivity) (hupos _).le, ← Real.rpow_mul hu0.le] at h3
    rw [hkB]
    refine le_trans (le_of_eq ?_) h3
    congr 2; ring
  -- combine
  have hmax1 : u ^ (max (aβ / rho) ((mu : ℝ) / rho * (aε + D))) ≤ u ^ (aβ / rho) :=
    qbPoly_pow_anti hu0 hu1 (le_max_left _ _)
  have hmax2 : u ^ (max (aβ / rho) ((mu : ℝ) / rho * (aε + D))) ≤
      u ^ ((mu : ℝ) / rho * (aε + D)) :=
    qbPoly_pow_anti hu0 hu1 (le_max_right _ _)
  have hm0 : 0 ≤ u ^ (max (aβ / rho) ((mu : ℝ) / rho * (aε + D))) := (hupos _).le
  unfold QuantitativeData.gamma
  rw [hrho', hmu']
  have hgam : min kA kB * u ^ (max (aβ / rho) ((mu : ℝ) / rho * (aε + D))) ≤
      min ((1 / 2 : ℝ) * (N : ℝ) ^ (-(1 / 2 : ℝ)) * (d.beta / 4) ^ (1 / (rho : ℝ)))
        ((d.epsLoss / d.cDio) ^ ((mu : ℝ) / rho)) := by
    refine le_min ?_ ?_
    · exact (mul_le_mul (min_le_left _ _) hmax1 hm0 hkApos.le).trans hA
    · exact (mul_le_mul (min_le_right _ _) hmax2 hm0 hkBpos.le).trans hB
  rw [show min kA kB / 2 * u ^ (max (aβ / rho) ((mu : ℝ) / rho * (aε + D))) =
    (min kA kB * u ^ (max (aβ / rho) ((mu : ℝ) / rho * (aε + D)))) / 2 by ring]
  exact div_le_div_of_nonneg_right hgam (by norm_num)

end KAM.Planetary
