/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Quantitative.Thresholds
public import KAM.Planetary.Quantitative.BudgetPower.Positivity
public import KAM.Planetary.Quantitative.BudgetPower.Rates
public import KAM.Planetary.Quantitative.BudgetPower.Gamma
public import KAM.Planetary.Quantitative.BudgetPower.Collar

/-!
# Polynomial budget for the quantitative threshold (P11C-Q3)

The rate structure `BudgetRates`, the exact exponent `BudgetRates.exponent`, the predicate
`RateBounds` and `qb_poly` (`bpP:p11a:bu-poly`): `thresholds d ≥ c' u^B` whenever the data obey the
polynomial rates, with `c'` chosen before the other rates and the family, depending only on
`(N, mu, rho, tau, c)` and the strip rate `a_s`. The fragments `ab_gamma`, `ab_T0`, `ab_t0`,
`ab_lam` are proved locally in `BudgetPower/*` and here (`qbPoly_*`); `adm_budget` itself is not
used.
-/

@[expose] public noncomputable section
open Set Metric Real MeasureTheory Function
open scoped ContDiff Topology
namespace KAM.Planetary

structure BudgetRates where
  vartheta : ℝ
  s : ℝ
  beta : ℝ
  loss : ℝ
  M : ℝ
  M0 : ℝ
  C1 : ℝ
  diam : ℝ

def BudgetRates.Valid (a : BudgetRates) : Prop :=
  0 ≤ a.vartheta ∧ 0 ≤ a.s ∧ 0 ≤ a.beta ∧ 0 ≤ a.loss ∧ 0 ≤ a.M ∧ 0 ≤ a.M0 ∧ 0 ≤ a.C1 ∧ 0 ≤ a.diam

def BudgetRates.exponent (N mu rho : ℕ) (tau : ℝ) (a : BudgetRates) : ℝ :=
  let D := N * a.diam + a.M + a.vartheta + (1 + 1 / (mu : ℝ)) * a.beta
  let G := max (a.beta / rho) ((mu : ℝ) / rho * (a.loss + D))
  let L := if 0 < a.s then a.s + 1 else 0
  let J := max a.vartheta (G + (tau + 1) * L + a.C1)
  let X := max J L
  let H := max (max J (G + (N + 1) * a.s + tau * L + X)) (a.beta + a.M0 + mu * J)
  2 * H + a.C1

def RateBounds {N : ℕ} (a : BudgetRates) (c u : ℝ) (d : QuantitativeData N) : Prop :=
  c * u ^ a.vartheta ≤ d.vartheta ∧ c * u ^ a.s ≤ d.s ∧ c * u ^ a.beta ≤ d.beta ∧
  c * u ^ a.loss ≤ d.epsLoss ∧ d.M ≤ c⁻¹ * u ^ (-a.M) ∧ d.M0 ≤ c⁻¹ * u ^ (-a.M0) ∧
  d.C1 ≤ c⁻¹ * u ^ (-a.C1) ∧ d.diameter ≤ c⁻¹ * u ^ (-a.diam)

/-! ### The named pieces `D, G, L, J, X, H` of the exponent -/

/-- The entry `D` of the exponent. -/
def BudgetRates.rateD (N mu : ℕ) (a : BudgetRates) : ℝ :=
  N * a.diam + a.M + a.vartheta + (1 + 1 / (mu : ℝ)) * a.beta

/-- The entry `G` of the exponent. -/
def BudgetRates.rateG (N mu rho : ℕ) (a : BudgetRates) : ℝ :=
  max (a.beta / rho) ((mu : ℝ) / rho * (a.loss + a.rateD N mu))

/-- The entry `L` of the exponent (the two cases `a_s = 0`, `a_s > 0`). -/
def BudgetRates.rateL (a : BudgetRates) : ℝ := if 0 < a.s then a.s + 1 else 0

/-- The entry `J` of the exponent. -/
def BudgetRates.rateJ (N mu rho : ℕ) (tau : ℝ) (a : BudgetRates) : ℝ :=
  max a.vartheta (a.rateG N mu rho + (tau + 1) * a.rateL + a.C1)

/-- The entry `X` of the exponent. -/
def BudgetRates.rateX (N mu rho : ℕ) (tau : ℝ) (a : BudgetRates) : ℝ :=
  max (a.rateJ N mu rho tau) a.rateL

/-- The entry `H` of the exponent. -/
def BudgetRates.rateH (N mu rho : ℕ) (tau : ℝ) (a : BudgetRates) : ℝ :=
  max (max (a.rateJ N mu rho tau) (a.rateG N mu rho + (N + 1) * a.s + tau * a.rateL +
    a.rateX N mu rho tau)) (a.beta + a.M0 + mu * a.rateJ N mu rho tau)

theorem BudgetRates.exponent_eq (N mu rho : ℕ) (tau : ℝ) (a : BudgetRates) :
    a.exponent N mu rho tau = 2 * a.rateH N mu rho tau + a.C1 := rfl

/-! ### Collar: `tbar`, `tflat` (`stepP:p11a:ab-T0`, `stepP:p11a:ab-t0`) -/

theorem qbPoly_collar (N mu rho : ℕ) (tau c asRate : ℝ) (hN : 1 ≤ N) (hmu : 1 ≤ mu)
    (hrho : rho = 1 ∨ rho = 2) (htau : (N : ℝ) * mu / rho - 1 < tau) (htau0 : 0 ≤ tau)
    (hc : 0 < c) (hc1 : c ≤ 1) (has : 0 ≤ asRate) :
    ∃ Ct k : ℝ, 0 < Ct ∧ 0 < k ∧ ∀ a : BudgetRates, a.Valid → a.s = asRate →
      ∀ d : QuantitativeData N, d.NumericalValid → d.mu = mu → d.rho = rho → d.tau = tau →
        ∀ u ∈ Ioc (0 : ℝ) 1, RateBounds a c u d →
          (1 ≤ d.tbar ∧ d.tbar ≤ Ct * u ^ (-a.rateL)) ∧
          k * u ^ (a.rateJ N mu rho tau) ≤ d.tflat := by
  obtain ⟨Ct, hCt, hT⟩ := qbPoly_tbar_bound N mu tau c asRate hN hc hc1 has
  obtain ⟨k2, hk2, hG⟩ := qbPoly_gamma_lower N mu rho tau c hN hmu hrho htau hc
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hsN : 0 < √(N : ℝ) := Real.sqrt_pos.mpr hN0
  refine ⟨Ct, min (c / √(N : ℝ)) (k2 * Ct ^ (-(tau + 1)) * (c / 4)), hCt, by positivity, ?_⟩
  intro a hv hs d hd hmu' hrho' htau' u hu rb
  obtain ⟨hu0, hu1⟩ := hu
  have hupos : ∀ e : ℝ, 0 < u ^ e := fun e => Real.rpow_pos_of_pos hu0 e
  obtain ⟨hϑ, hs', hβ, hε, hM, hM0, hC1, hdiam⟩ := rb
  obtain ⟨ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8⟩ := hv
  have hd' := hd
  obtain ⟨-, -, -, -, -, hϑ0, hϑ1, hs0, hs1, hC1one, -, -, -, -, -, -⟩ := hd
  have hL : a.rateL = if 0 < asRate then asRate + 1 else 0 := by
    unfold BudgetRates.rateL; rw [hs]
  have hscu : c * u ^ asRate ≤ d.s := by rw [← hs]; exact hs'
  obtain ⟨ht1, ht2⟩ := hT d hmu' htau' hs0 hs1 u ⟨hu0, hu1⟩ hscu
  rw [← hL] at ht2
  refine ⟨⟨ht1, ht2⟩, ?_⟩
  have hg : k2 * u ^ (a.rateG N mu rho) ≤ d.gamma :=
    hG a.vartheta a.beta a.loss a.M a.diam ha1 ha3 ha4 ha5 ha8 d hd' hmu' hrho' htau' u
      ⟨hu0, hu1⟩ hϑ hβ hε hM hdiam
  have hJ1 : a.vartheta ≤ a.rateJ N mu rho tau := le_max_left _ _
  have hJ2 : a.rateG N mu rho + (tau + 1) * a.rateL + a.C1 ≤ a.rateJ N mu rho tau :=
    le_max_right _ _
  unfold QuantitativeData.tflat
  refine le_min ?_ ?_
  · -- first branch: `vartheta / sqrt N`
    have h1 : c * u ^ a.rateJ N mu rho tau ≤ d.vartheta :=
      (mul_le_mul_of_nonneg_left (qbPoly_pow_anti hu0 hu1 hJ1) hc.le).trans hϑ
    calc min (c / √(N : ℝ)) (k2 * Ct ^ (-(tau + 1)) * (c / 4)) * u ^ a.rateJ N mu rho tau
        ≤ (c / √(N : ℝ)) * u ^ a.rateJ N mu rho tau :=
          mul_le_mul_of_nonneg_right (min_le_left _ _) (hupos _).le
      _ = (c * u ^ a.rateJ N mu rho tau) / √(N : ℝ) := by ring
      _ ≤ d.vartheta / √(N : ℝ) := div_le_div_of_nonneg_right h1 hsN.le
  · -- second branch
    rw [htau']
    have hpos1 : 0 < d.tbar := lt_of_lt_of_le one_pos ht1
    have hT1 : Ct ^ (-(tau + 1)) * u ^ (a.rateL * (tau + 1)) ≤ d.tbar ^ (-tau - 1) := by
      have h1 : d.tbar ^ (tau + 1) ≤ (Ct * u ^ (-a.rateL)) ^ (tau + 1) :=
        Real.rpow_le_rpow hpos1.le ht2 (by linarith)
      have h2 : (Ct * u ^ (-a.rateL)) ^ (tau + 1) =
          Ct ^ (tau + 1) * u ^ (-(a.rateL * (tau + 1))) := by
        rw [Real.mul_rpow hCt.le (hupos _).le, ← Real.rpow_mul hu0.le]
        congr 2; ring
      have h3 := inv_anti₀ (Real.rpow_pos_of_pos hpos1 _) h1
      rw [h2, mul_inv, ← Real.rpow_neg hCt.le, ← Real.rpow_neg hu0.le,
        neg_neg] at h3
      rw [show -tau - 1 = -(tau + 1) by ring, Real.rpow_neg hpos1.le]
      exact h3
    have hC1pos : 0 < d.C1 := by linarith
    have hC1' : c / 4 * u ^ a.C1 ≤ 1 / (4 * d.C1) := by
      have h1 : 4 * d.C1 ≤ 4 * (c⁻¹ * u ^ (-a.C1)) := by linarith
      have h2 := one_div_le_one_div_of_le (by positivity) h1
      have h3 : 1 / (4 * (c⁻¹ * u ^ (-a.C1))) = c / 4 * u ^ a.C1 := by
        rw [Real.rpow_neg hu0.le]; have := hupos a.C1; field_simp
      linarith
    have hprod := qbPoly_lb_mul (by positivity) (by positivity) hC1' hT1
    have hprod2 := qbPoly_lb_mul (by positivity) (by positivity) hg hprod
    have hexp : u ^ (a.rateG N mu rho) * (u ^ a.C1 * u ^ (a.rateL * (tau + 1))) =
        u ^ (a.rateG N mu rho + (a.C1 + a.rateL * (tau + 1))) := by
      rw [← Real.rpow_add hu0, ← Real.rpow_add hu0]
    have hle : u ^ (a.rateJ N mu rho tau) ≤
        u ^ (a.rateG N mu rho + (a.C1 + a.rateL * (tau + 1))) :=
      qbPoly_pow_anti hu0 hu1 (by linarith)
    have hkk : min (c / √(N : ℝ)) (k2 * Ct ^ (-(tau + 1)) * (c / 4)) ≤
        k2 * (c / 4 * Ct ^ (-(tau + 1))) :=
      (min_le_right _ _).trans (le_of_eq (by ring))
    calc min (c / √(N : ℝ)) (k2 * Ct ^ (-(tau + 1)) * (c / 4)) * u ^ a.rateJ N mu rho tau
        ≤ (k2 * (c / 4 * Ct ^ (-(tau + 1)))) * u ^ a.rateJ N mu rho tau :=
          mul_le_mul_of_nonneg_right hkk (hupos _).le
      _ ≤ (k2 * (c / 4 * Ct ^ (-(tau + 1)))) *
            u ^ (a.rateG N mu rho + (a.C1 + a.rateL * (tau + 1))) :=
          mul_le_mul_of_nonneg_left hle (by positivity)
      _ = (k2 * (c / 4 * Ct ^ (-(tau + 1)))) *
            (u ^ (a.rateG N mu rho) * (u ^ a.C1 * u ^ (a.rateL * (tau + 1)))) := by rw [hexp]
      _ ≤ d.gamma * (1 / (4 * d.C1) * d.tbar ^ (-tau - 1)) := by
          exact hprod2
      _ = d.gamma * d.tbar ^ (-tau - 1) / (4 * d.C1) := by ring

/-! ### The strip bound `xibar` (`stepP:p11a:ab-t0`) -/

theorem BudgetRates.rateJ_nonneg (N mu rho : ℕ) (tau : ℝ) (a : BudgetRates) (hv : a.Valid) :
    0 ≤ a.rateJ N mu rho tau :=
  hv.1.trans (le_max_left _ _)

theorem BudgetRates.s_le_rateL (a : BudgetRates) (hv : a.Valid) : a.s ≤ a.rateL := by
  unfold BudgetRates.rateL
  split_ifs with h
  · linarith
  · exact not_lt.mp h

theorem BudgetRates.rateL_le_rateX (N mu rho : ℕ) (tau : ℝ) (a : BudgetRates) :
    a.rateL ≤ a.rateX N mu rho tau := le_max_right _ _

theorem BudgetRates.rateJ_le_rateX (N mu rho : ℕ) (tau : ℝ) (a : BudgetRates) :
    a.rateJ N mu rho tau ≤ a.rateX N mu rho tau := le_max_left _ _

theorem qbPoly_xibar_upper {N : ℕ} (mu rho : ℕ) (tau c Ct kt : ℝ) (hc : 0 < c) (hCt : 0 < Ct)
    (hkt : 0 < kt) (a : BudgetRates) (hv : a.Valid) (d : QuantitativeData N)
    (hd : d.NumericalValid) (htau' : d.tau = tau) (u : ℝ) (hu0 : 0 < u) (hu1 : u ≤ 1)
    (hs : c * u ^ a.s ≤ d.s) (ht : 1 ≤ d.tbar ∧ d.tbar ≤ Ct * u ^ (-a.rateL))
    (hf : kt * u ^ (a.rateJ N mu rho tau) ≤ d.tflat) :
    d.xibar ≤ (2 : ℝ) ^ (tau + 1) * (1 + 24 / c + 1 / kt + Ct) *
      u ^ (-(a.rateX N mu rho tau)) := by
  obtain ⟨-, -, -, -, -, hϑ0, hϑ1, hs0, hs1, -, -, -, -, -, -, -⟩ := hd
  have hupos : ∀ e : ℝ, 0 < u ^ e := fun e => Real.rpow_pos_of_pos hu0 e
  have hJ0 := a.rateJ_nonneg N mu rho tau hv
  have hX0 : 0 ≤ a.rateX N mu rho tau := hJ0.trans (a.rateJ_le_rateX N mu rho tau)
  set X := a.rateX N mu rho tau with hX
  have hE : 1 ≤ u ^ (-X) := qbPoly_negpow_ge_one hu0 hu1 hX0
  have hft : 0 < d.tflat := lt_of_lt_of_le (mul_pos hkt (hupos _)) hf
  have t2 : 1 / (d.s / 24) ≤ 24 / c * u ^ (-X) := by
    have h1 : 1 / (d.s / 24) ≤ 1 / (c * u ^ a.s / 24) :=
      one_div_le_one_div_of_le (by have := hupos a.s; positivity) (by linarith)
    have h2 : 1 / (c * u ^ a.s / 24) = 24 / c * u ^ (-a.s) := by
      rw [Real.rpow_neg hu0.le]; have := hupos a.s; field_simp
    have h3 : u ^ (-a.s) ≤ u ^ (-X) :=
      qbPoly_negpow_mono hu0 hu1 ((a.s_le_rateL hv).trans
        ((a.rateL_le_rateX N mu rho tau)))
    calc 1 / (d.s / 24) ≤ 24 / c * u ^ (-a.s) := by linarith
      _ ≤ 24 / c * u ^ (-X) := mul_le_mul_of_nonneg_left h3 (by positivity)
  have t3 : 1 / d.tflat ≤ 1 / kt * u ^ (-X) := by
    have h1 : 1 / d.tflat ≤ 1 / (kt * u ^ (a.rateJ N mu rho tau)) :=
      one_div_le_one_div_of_le (mul_pos hkt (hupos _)) hf
    have h2 : 1 / (kt * u ^ (a.rateJ N mu rho tau)) = 1 / kt * u ^ (-(a.rateJ N mu rho tau)) := by
      rw [Real.rpow_neg hu0.le]; have := hupos (a.rateJ N mu rho tau); field_simp
    have h3 : u ^ (-(a.rateJ N mu rho tau)) ≤ u ^ (-X) :=
      qbPoly_negpow_mono hu0 hu1 (a.rateJ_le_rateX N mu rho tau)
    calc 1 / d.tflat ≤ 1 / kt * u ^ (-(a.rateJ N mu rho tau)) := by linarith
      _ ≤ 1 / kt * u ^ (-X) := mul_le_mul_of_nonneg_left h3 (by positivity)
  have t4 : d.tbar * (d.s / 24) ≤ Ct * u ^ (-X) := by
    have h3 : u ^ (-a.rateL) ≤ u ^ (-X) :=
      qbPoly_negpow_mono hu0 hu1 (a.rateL_le_rateX N mu rho tau)
    calc d.tbar * (d.s / 24) ≤ d.tbar * 1 :=
          mul_le_mul_of_nonneg_left (by linarith) (by linarith [ht.1])
      _ ≤ Ct * u ^ (-a.rateL) := by linarith [ht.2]
      _ ≤ Ct * u ^ (-X) := mul_le_mul_of_nonneg_left h3 hCt.le
  unfold QuantitativeData.xibar
  rw [htau', mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  calc 1 + 1 / (d.s / 24) + 1 / d.tflat + d.tbar * (d.s / 24)
      ≤ 1 * u ^ (-X) + 24 / c * u ^ (-X) + 1 / kt * u ^ (-X) + Ct * u ^ (-X) :=
        add_le_add (add_le_add (add_le_add (by linarith) t2) t3) t4
    _ = _ := by ring

/-! ### The quadratic branch (`stepP:p11a:ab-lam`, second term) -/

theorem qbPoly_second_lower {N : ℕ} (mu rho : ℕ) (hN : 1 ≤ N) (tau c Ct k2 : ℝ) (hc : 0 < c)
    (hCt : 0 < Ct) (hk2 : 0 < k2) (htau0 : 0 ≤ tau) (a : BudgetRates) (d : QuantitativeData N)
    (htau' : d.tau = tau) (u : ℝ) (hu0 : 0 < u) (hu1 : u ≤ 1)
    (hg : k2 * u ^ (a.rateG N mu rho) ≤ d.gamma) (hs : c * u ^ a.s ≤ d.s) (hs0 : 0 < d.s)
    (ht : 1 ≤ d.tbar ∧ d.tbar ≤ Ct * u ^ (-a.rateL)) :
    π * k2 * (c / 24) ^ (N + 1) / (18 * N * (4 * N + 5) * 2 ^ N * Ct ^ tau) *
        u ^ (a.rateG N mu rho + (N + 1) * a.s + tau * a.rateL) ≤
      π * d.gamma * (d.s / 24) ^ (N + 1) / (18 * N * (4 * N + 5) * 2 ^ N * d.tbar ^ d.tau) := by
  have hupos : ∀ e : ℝ, 0 < u ^ e := fun e => Real.rpow_pos_of_pos hu0 e
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hpi := Real.pi_pos
  have hden0 : (0 : ℝ) < 18 * N * (4 * N + 5) * 2 ^ N := by positivity
  have hgpos : 0 < d.gamma := lt_of_lt_of_le (mul_pos hk2 (hupos _)) hg
  have hs24 : (c / 24) ^ (N + 1) * u ^ (a.s * ((N : ℝ) + 1)) ≤ (d.s / 24) ^ (N + 1) := by
    have h1 : (c / 24 * u ^ a.s) ^ (N + 1) ≤ (d.s / 24) ^ (N + 1) :=
      pow_le_pow_left₀ (by have := hupos a.s; positivity) (by linarith) _
    have h2 : (c / 24 * u ^ a.s) ^ (N + 1) = (c / 24) ^ (N + 1) * u ^ (a.s * ((N : ℝ) + 1)) := by
      have h3 : (u ^ a.s) ^ (N + 1) = u ^ (a.s * ((N : ℝ) + 1)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hu0.le]; push_cast; rfl
      rw [mul_pow, h3]
    linarith
  have hnum : π * (k2 * (c / 24) ^ (N + 1)) * u ^ (a.rateG N mu rho + a.s * ((N : ℝ) + 1)) ≤
      π * d.gamma * (d.s / 24) ^ (N + 1) := by
    have h := mul_le_mul hg hs24 (by have := hupos (a.s * ((N : ℝ) + 1)); positivity) hgpos.le
    calc π * (k2 * (c / 24) ^ (N + 1)) * u ^ (a.rateG N mu rho + a.s * ((N : ℝ) + 1))
        = π * ((k2 * u ^ (a.rateG N mu rho)) *
            ((c / 24) ^ (N + 1) * u ^ (a.s * ((N : ℝ) + 1)))) := by
          rw [Real.rpow_add hu0]; ring
      _ ≤ π * (d.gamma * (d.s / 24) ^ (N + 1)) := mul_le_mul_of_nonneg_left h hpi.le
      _ = _ := by ring
  have htb0 : 0 < d.tbar := lt_of_lt_of_le one_pos ht.1
  have hden : d.tbar ^ d.tau ≤ Ct ^ tau * u ^ (-(a.rateL * tau)) := by
    rw [htau']
    calc d.tbar ^ tau ≤ (Ct * u ^ (-a.rateL)) ^ tau := Real.rpow_le_rpow htb0.le ht.2 htau0
      _ = _ := by
        rw [Real.mul_rpow hCt.le (hupos _).le, ← Real.rpow_mul hu0.le]
        congr 2; ring
  have htbp : 0 < d.tbar ^ d.tau := Real.rpow_pos_of_pos htb0 _
  have hmain : π * (k2 * (c / 24) ^ (N + 1)) * u ^ (a.rateG N mu rho + a.s * ((N : ℝ) + 1)) /
      (18 * N * (4 * N + 5) * 2 ^ N * (Ct ^ tau * u ^ (-(a.rateL * tau)))) ≤
      π * d.gamma * (d.s / 24) ^ (N + 1) / (18 * N * (4 * N + 5) * 2 ^ N * d.tbar ^ d.tau) := by
    refine div_le_div₀ (by positivity) hnum (by positivity) ?_
    exact mul_le_mul_of_nonneg_left hden hden0.le
  refine le_trans (le_of_eq ?_) hmain
  have hE : u ^ (a.rateG N mu rho + (N + 1) * a.s + tau * a.rateL) =
      u ^ (a.rateG N mu rho + a.s * ((N : ℝ) + 1)) * u ^ (a.rateL * tau) := by
    rw [← Real.rpow_add hu0]; congr 1; ring
  rw [hE, Real.rpow_neg hu0.le]
  have := hupos (a.rateL * tau)
  have := Real.rpow_pos_of_pos hCt tau
  field_simp

/-! ### The flat radius `lambdaFlat ≥ k u^H` (`stepP:p11a:ab-lam`) -/

theorem qbPoly_lambda_lower (N mu rho : ℕ) (tau c asRate : ℝ) (hN : 1 ≤ N) (hmu : 1 ≤ mu)
    (hrho : rho = 1 ∨ rho = 2) (htau : (N : ℝ) * mu / rho - 1 < tau) (htau0 : 0 ≤ tau)
    (hc : 0 < c) (hc1 : c ≤ 1) (has : 0 ≤ asRate) :
    ∃ k : ℝ, 0 < k ∧ ∀ a : BudgetRates, a.Valid → a.s = asRate →
      ∀ d : QuantitativeData N, d.NumericalValid → d.mu = mu → d.rho = rho → d.tau = tau →
        ∀ u ∈ Ioc (0 : ℝ) 1, RateBounds a c u d →
          k * u ^ (a.rateH N mu rho tau) ≤ d.lambdaFlat := by
  obtain ⟨Ct, kt, hCt, hkt, hcol⟩ := qbPoly_collar N mu rho tau c asRate hN hmu hrho htau htau0
    hc hc1 has
  obtain ⟨k2, hk2, hG⟩ := qbPoly_gamma_lower N mu rho tau c hN hmu hrho htau hc
  have hCC := qbPoly_cutoffConstant_pos N mu hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hpi := Real.pi_pos
  set vp : ℝ := (2 : ℝ) ^ (-(2 * (2 * (tau + 1) * ((mu : ℝ) + 1) + N + 4))) with hvp
  set Cx : ℝ := (2 : ℝ) ^ (tau + 1) * (1 + 24 / c + 1 / kt + Ct) with hCx
  have hCxpos : 0 < Cx := by positivity
  set kmid : ℝ := min (vp / 2) ((2 : ℝ) ^ (-10 : ℤ) / Cx) with hkmid
  set kgam : ℝ := π * k2 * (c / 24) ^ (N + 1) / (18 * N * (4 * N + 5) * 2 ^ N * Ct ^ tau)
    with hkgam
  set kthird : ℝ := c ^ 2 / 2 ^ (mu + 3) * kt ^ mu / (4 * p11c_cutoffConstant N mu)
    with hkthird
  have hkmidpos : 0 < kmid := by positivity
  have hkgampos : 0 < kgam := by positivity
  have hkthirdpos : 0 < kthird := by positivity
  refine ⟨min (min (kt / 8) (kmid * kgam)) kthird, by positivity, ?_⟩
  intro a hv hs d hd hmu' hrho' htau' u hu rb
  obtain ⟨hu0, hu1⟩ := hu
  have hupos : ∀ e : ℝ, 0 < u ^ e := fun e => Real.rpow_pos_of_pos hu0 e
  have hd' := hd
  obtain ⟨-, -, -, -, -, hϑ0, hϑ1, hs0, hs1, hC1one, hM00, hβ0, -, -, -, -⟩ := hd
  obtain ⟨ht, hf⟩ := hcol a hv hs d hd' hmu' hrho' htau' u ⟨hu0, hu1⟩ rb
  obtain ⟨hϑ, hs', hβ, hε, hM, hM0, hC1, hdiam⟩ := rb
  obtain ⟨ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8⟩ := hv
  have hv' : a.Valid := ⟨ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8⟩
  have hg : k2 * u ^ (a.rateG N mu rho) ≤ d.gamma :=
    hG a.vartheta a.beta a.loss a.M a.diam ha1 ha3 ha4 ha5 ha8 d hd' hmu' hrho' htau' u
      ⟨hu0, hu1⟩ hϑ hβ hε hM hdiam
  have hxi := qbPoly_xibar_upper mu rho tau c Ct kt hc hCt hkt a hv' d hd' htau' u hu0 hu1 hs' ht hf
  have hsec := qbPoly_second_lower mu rho hN tau c Ct k2 hc hCt hk2 htau0 a d htau' u hu0 hu1 hg
    hs' hs0 ht
  have hth := qbPoly_thetaMax_lower N mu rho c hrho hc hc1 a.beta a.M0 ha3 ha6 d hmu' hrho' hβ0
    hM00 u ⟨hu0, hu1⟩ hβ hM0
  have hH1 : a.rateJ N mu rho tau ≤ a.rateH N mu rho tau :=
    (le_max_left _ _).trans (le_max_left _ _)
  have hH2 : a.rateG N mu rho + (N + 1) * a.s + tau * a.rateL + a.rateX N mu rho tau ≤
      a.rateH N mu rho tau := (le_max_right _ _).trans (le_max_left _ _)
  have hH3 : a.beta + a.M0 + mu * a.rateJ N mu rho tau ≤ a.rateH N mu rho tau :=
    le_max_right _ _
  have hX0 : 0 ≤ a.rateX N mu rho tau :=
    (a.rateJ_nonneg N mu rho tau hv').trans (a.rateJ_le_rateX N mu rho tau)
  have hftpos : 0 < d.tflat := lt_of_lt_of_le (mul_pos hkt (hupos _)) hf
  have hxipos : 0 < d.xibar := by
    unfold QuantitativeData.xibar
    have := ht.1
    have : 0 < d.tbar * (d.s / 24) := by positivity
    positivity
  have hvarpi : d.varpi = vp := by
    unfold QuantitativeData.varpi; rw [htau', hmu']
  unfold QuantitativeData.lambdaFlat
  rw [hmu', hvarpi]
  refine le_min (le_min ?_ ?_) ?_
  · -- first term
    have h1 : u ^ (a.rateH N mu rho tau) ≤ u ^ (a.rateJ N mu rho tau) := qbPoly_pow_anti hu0 hu1 hH1
    calc min (min (kt / 8) (kmid * kgam)) kthird * u ^ (a.rateH N mu rho tau)
        ≤ (kt / 8) * u ^ (a.rateJ N mu rho tau) :=
          mul_le_mul ((min_le_left _ _).trans (min_le_left _ _)) h1 (hupos _).le (by positivity)
      _ ≤ d.tflat / 8 := by linarith
  · -- second term
    have hmid : kmid * u ^ (a.rateX N mu rho tau) ≤
        min (vp / 2) ((2 : ℝ) ^ (-10 : ℤ) / d.xibar) := by
      refine le_min ?_ ?_
      · calc kmid * u ^ (a.rateX N mu rho tau) ≤ kmid * 1 :=
              mul_le_mul_of_nonneg_left (qbPoly_pow_le_one hu0 hu1 hX0) hkmidpos.le
          _ ≤ vp / 2 := by rw [mul_one]; exact min_le_left _ _
      · have h1 : (2 : ℝ) ^ (-10 : ℤ) / (Cx * u ^ (-(a.rateX N mu rho tau))) ≤
            (2 : ℝ) ^ (-10 : ℤ) / d.xibar :=
          div_le_div_of_nonneg_left (by positivity) hxipos hxi
        have h2 : (2 : ℝ) ^ (-10 : ℤ) / (Cx * u ^ (-(a.rateX N mu rho tau))) =
            (2 : ℝ) ^ (-10 : ℤ) / Cx * u ^ (a.rateX N mu rho tau) := by
          rw [Real.rpow_neg hu0.le]; have := hupos (a.rateX N mu rho tau); field_simp
        have h3 : kmid * u ^ (a.rateX N mu rho tau) ≤
            (2 : ℝ) ^ (-10 : ℤ) / Cx * u ^ (a.rateX N mu rho tau) :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) (hupos _).le
        linarith
    have hprod := qbPoly_lb_mul (by positivity) (by positivity) hmid hsec
    rw [← Real.rpow_add hu0] at hprod
    have h1 : u ^ (a.rateH N mu rho tau) ≤
        u ^ (a.rateX N mu rho tau + (a.rateG N mu rho + (N + 1) * a.s + tau * a.rateL)) :=
      qbPoly_pow_anti hu0 hu1 (by linarith)
    calc min (min (kt / 8) (kmid * kgam)) kthird * u ^ (a.rateH N mu rho tau)
        ≤ (kmid * kgam) * u ^ (a.rateX N mu rho tau +
            (a.rateG N mu rho + (N + 1) * a.s + tau * a.rateL)) :=
          mul_le_mul ((min_le_left _ _).trans (min_le_right _ _)) h1 (hupos _).le (by positivity)
      _ ≤ _ := hprod
  · -- third term
    have hpow : (kt * u ^ (a.rateJ N mu rho tau)) ^ mu ≤ d.tflat ^ mu :=
      pow_le_pow_left₀ (by have := hupos (a.rateJ N mu rho tau); positivity) hf _
    have hpow2 : (kt * u ^ (a.rateJ N mu rho tau)) ^ mu =
        kt ^ mu * u ^ (mu * a.rateJ N mu rho tau) := by
      have h3 : (u ^ (a.rateJ N mu rho tau)) ^ mu = u ^ (mu * a.rateJ N mu rho tau) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hu0.le]; congr 1; ring
      rw [mul_pow, h3]
    have hprod := qbPoly_lb_mul (by positivity) (by positivity) hth
      (hpow2 ▸ hpow : kt ^ mu * u ^ (mu * a.rateJ N mu rho tau) ≤ d.tflat ^ mu)
    rw [← Real.rpow_add hu0] at hprod
    have h1 : u ^ (a.rateH N mu rho tau) ≤
        u ^ (a.beta + a.M0 + mu * a.rateJ N mu rho tau) := qbPoly_pow_anti hu0 hu1 hH3
    have hcc : (0 : ℝ) < 4 * p11c_cutoffConstant N mu := by positivity
    rw [le_div_iff₀ hcc]
    calc min (min (kt / 8) (kmid * kgam)) kthird * u ^ (a.rateH N mu rho tau) *
          (4 * p11c_cutoffConstant N mu)
        ≤ kthird * u ^ (a.beta + a.M0 + mu * a.rateJ N mu rho tau) *
          (4 * p11c_cutoffConstant N mu) := by
          gcongr
          exact min_le_right _ _
      _ = (c ^ 2 / 2 ^ (mu + 3) * kt ^ mu) *
          u ^ (a.beta + a.M0 + mu * a.rateJ N mu rho tau) := by
          rw [hkthird]; field_simp
      _ ≤ _ := hprod

/-- c' chosen before all other rates and before the family, with only a_s fixed. -/
theorem qb_poly (N mu rho : ℕ) (tau c asRate : ℝ) (hN : 1 ≤ N) (hmu : 1 ≤ mu)
    (hrho : rho = 1 ∨ rho = 2) (htau : (N : ℝ) * mu / rho - 1 < tau) (htau0 : 0 ≤ tau)
    (hc : 0 < c) (hc1 : c ≤ 1) (has : 0 ≤ asRate) :
    ∃ c' : ℝ, 0 < c' ∧ ∀ a : BudgetRates, a.Valid → a.s = asRate →
      ∀ d : QuantitativeData N, d.NumericalValid → d.mu = mu → d.rho = rho → d.tau = tau →
        ∀ u ∈ Ioc (0 : ℝ) 1, RateBounds a c u d →
          c' * u ^ a.exponent N mu rho tau ≤ thresholds d := by
  obtain ⟨k, hk, hlam⟩ := qbPoly_lambda_lower N mu rho tau c asRate hN hmu hrho htau htau0 hc hc1
    has
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  refine ⟨k ^ 2 * c / (2 * N), by positivity, ?_⟩
  intro a hv hs d hd hmu' hrho' htau' u hu rb
  obtain ⟨hu0, hu1⟩ := hu
  have hupos : ∀ e : ℝ, 0 < u ^ e := fun e => Real.rpow_pos_of_pos hu0 e
  have hl := hlam a hv hs d hd hmu' hrho' htau' u ⟨hu0, hu1⟩ rb
  obtain ⟨-, -, -, -, -, hϑ0, hϑ1, hs0, hs1, hC1one, hM00, hβ0, -, -, -, -⟩ := hd
  obtain ⟨-, -, -, -, -, -, hC1, -⟩ := rb
  have hC1pos : 0 < d.C1 := by linarith
  have hC1' : c * u ^ a.C1 ≤ 1 / d.C1 := by
    have h2 := one_div_le_one_div_of_le hC1pos hC1
    have h3 : 1 / (c⁻¹ * u ^ (-a.C1)) = c * u ^ a.C1 := by
      rw [Real.rpow_neg hu0.le]; have := hupos a.C1; field_simp
    linarith
  have hH0 : 0 ≤ a.rateH N mu rho tau := by
    refine le_trans ?_ ((le_max_left _ _).trans (le_max_left _ _))
    exact a.rateJ_nonneg N mu rho tau hv
  rw [BudgetRates.exponent_eq]
  have hexp : u ^ (2 * a.rateH N mu rho tau + a.C1) =
      u ^ (a.rateH N mu rho tau) * u ^ (a.rateH N mu rho tau) * u ^ a.C1 := by
    rw [show 2 * a.rateH N mu rho tau + a.C1 = (a.rateH N mu rho tau + a.rateH N mu rho tau) +
      a.C1 by ring, Real.rpow_add hu0, Real.rpow_add hu0]
  have hsq : (k * u ^ (a.rateH N mu rho tau)) ^ 2 ≤ d.lambdaFlat ^ 2 :=
    pow_le_pow_left₀ (by have := hupos (a.rateH N mu rho tau); positivity) hl 2
  have hprod : (k * u ^ (a.rateH N mu rho tau)) ^ 2 * (c * u ^ a.C1) ≤
      d.lambdaFlat ^ 2 * (1 / d.C1) :=
    mul_le_mul hsq hC1' (by have := hupos a.C1; positivity) (by positivity)
  unfold thresholds
  rw [hexp]
  calc k ^ 2 * c / (2 * N) *
        (u ^ (a.rateH N mu rho tau) * u ^ (a.rateH N mu rho tau) * u ^ a.C1)
      = (k * u ^ (a.rateH N mu rho tau)) ^ 2 * (c * u ^ a.C1) / (2 * N) := by ring
    _ ≤ d.lambdaFlat ^ 2 * (1 / d.C1) / (2 * N) :=
        div_le_div_of_nonneg_right hprod (by positivity)
    _ = d.lambdaFlat ^ 2 / (2 * N * d.C1) := by field_simp

end KAM.Planetary
