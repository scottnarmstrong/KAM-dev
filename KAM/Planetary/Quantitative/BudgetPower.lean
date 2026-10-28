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

end KAM.Planetary
