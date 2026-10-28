/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Quantitative.BudgetPositivity

/-!
# Quantitative budget: comparison and monotonicity of thresholds (P11C-Q2)

`qb_comp` (the data-only threshold is positive and below the old threshold's numerical
projection) and `qb_mono` (`gamma` and `thresholds` are monotone for `BudgetOrder`).

-/

@[expose] public noncomputable section
open Set Metric Real MeasureTheory Function
open scoped ContDiff Topology
namespace KAM.Planetary
/-- The shape shared by `lambdaFlat` and the old threshold's inner minimum. -/
noncomputable def qbcLam (N mu : ℕ) (tau a1 vp xi g s tb thM tp cc : ℝ) : ℝ :=
  min (min a1 (min (vp / 2) ((2 : ℝ) ^ (-10 : ℤ) / xi) *
    (π * g * (s / 24) ^ (N + 1) / (18 * N * (4 * N + 5) * 2 ^ N * tb ^ tau))))
    (thM * tp ^ mu / (4 * cc))

theorem qbc_lambdaFlat_eq {N : ℕ} (d : QuantitativeData N) :
    d.lambdaFlat = qbcLam N d.mu d.tau (d.tflat / 8) d.varpi d.xibar d.gamma d.s d.tbar
      d.thetaMax d.tflat (p11c_cutoffConstant N d.mu) := rfl

theorem qbcLam_mono {N mu : ℕ} {tau a1 a1' vp xi xi' g g' s s' tb tb' thM thM' tp tp' cc : ℝ}
    (hN : 0 < N) (ha : a1 ≤ a1') (hxi' : 0 < xi') (hxi : xi' ≤ xi) (hg : 0 ≤ g) (hgg : g ≤ g')
    (hs : 0 ≤ s) (hss : s ≤ s') (htb' : 0 < tb') (htb : tb' ≤ tb) (htau : 0 ≤ tau)
    (hth : 0 ≤ thM) (hthh : thM ≤ thM') (htp : 0 ≤ tp) (htpp : tp ≤ tp') (hcc : 0 < cc)
    (hvp : 0 ≤ vp) :
    qbcLam N mu tau a1 vp xi g s tb thM tp cc ≤
      qbcLam N mu tau a1' vp xi' g' s' tb' thM' tp' cc := by
  unfold qbcLam
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hg' : 0 ≤ g' := hg.trans hgg
  have hs' : 0 ≤ s' := hs.trans hss
  have hp1 : tb' ^ tau ≤ tb ^ tau := Real.rpow_le_rpow htb'.le htb htau
  have hp2 : 0 < tb' ^ tau := Real.rpow_pos_of_pos htb' _
  have hden : 0 < 18 * (N : ℝ) * (4 * N + 5) * 2 ^ N * tb' ^ tau := by positivity
  have hQ : π * g * (s / 24) ^ (N + 1) / (18 * N * (4 * N + 5) * 2 ^ N * tb ^ tau) ≤
      π * g' * (s' / 24) ^ (N + 1) / (18 * N * (4 * N + 5) * 2 ^ N * tb' ^ tau) := by
    have hnum : π * g * (s / 24) ^ (N + 1) ≤ π * g' * (s' / 24) ^ (N + 1) := by gcongr
    refine div_le_div₀ (by positivity) hnum hden ?_
    gcongr
  have hQ0 : 0 ≤ π * g * (s / 24) ^ (N + 1) / (18 * N * (4 * N + 5) * 2 ^ N * tb ^ tau) := by
    have : 0 < tb ^ tau := Real.rpow_pos_of_pos (htb'.trans_le htb) _
    positivity
  have hX : (2 : ℝ) ^ (-10 : ℤ) / xi ≤ (2 : ℝ) ^ (-10 : ℤ) / xi' :=
    div_le_div_of_nonneg_left (by positivity) hxi' hxi
  refine min_le_min (min_le_min ha ?_) ?_
  · exact mul_le_mul (min_le_min le_rfl hX) hQ hQ0 (le_min (by positivity) (by positivity))
  · have h1 : thM * tp ^ mu ≤ thM' * tp' ^ mu :=
      mul_le_mul hthh (pow_le_pow_left₀ htp htpp mu) (by positivity) (hth.trans hthh)
    exact div_le_div_of_nonneg_right h1 (by positivity)

theorem qbc_thetaMax_mono {N : ℕ} {d d' : QuantitativeData N} (hmu : d.mu = d'.mu)
    (hrho : d.rho = d'.rho) (hβ0 : 0 < d.beta) (hβ : d.beta ≤ d'.beta) (hM0' : 0 < d'.M0)
    (hM0 : d'.M0 ≤ d.M0) : d.thetaMax ≤ d'.thetaMax := by
  unfold QuantitativeData.thetaMax
  rw [← hmu, ← hrho]
  split_ifs
  · exact div_le_div_of_nonneg_right hβ (by norm_num)
  · refine min_le_min hβ ?_
    have hc : (0 : ℝ) < 2 ^ (d.mu + 1) := by positivity
    have hM : 0 < d.M0 := hM0'.trans_le hM0
    have h1 : 0 < 2 ^ (d.mu + 1) * (2 * d.M0 + d.beta) := by positivity
    have h2 : 0 < 2 ^ (d.mu + 1) * (2 * d'.M0 + d'.beta) := by
      have := hβ0.trans_le hβ; positivity
    rw [div_le_div_iff₀ h1 h2]
    have : d.beta * d'.M0 ≤ d'.beta * d.M0 :=
      mul_le_mul hβ hM0 hM0'.le (hβ0.le.trans hβ)
    nlinarith [mul_le_mul_of_nonneg_left this hc.le]

theorem qbc_varpi_eq {N : ℕ} {d d' : QuantitativeData N} (hmu : d.mu = d'.mu)
    (htau : d.tau = d'.tau) : d.varpi = d'.varpi := by
  unfold QuantitativeData.varpi; rw [hmu, htau]

theorem qbc_tbar_sum_nonneg {N : ℕ} {d : QuantitativeData N} (hd : d.NumericalValid) :
    0 ≤ |d.A0| + N * log (32 * N / d.s) := by
  have := qbc_log_term_nonneg hd; positivity

theorem qbc_s_mul_tbar {N : ℕ} {d : QuantitativeData N} (hd : d.NumericalValid) :
    d.s * d.tbar = d.s + 16 / π * (|d.A0| + N * log (32 * N / d.s)) := by
  have hs0 : d.s ≠ 0 := hd.2.2.2.2.2.2.2.1.ne'
  unfold QuantitativeData.tbar
  field_simp

theorem qbc_s_tbar_anti {N : ℕ} {d d' : QuantitativeData N} (hd : d.NumericalValid)
    (hd' : d'.NumericalValid) (hmu : d.mu = d'.mu) (htau : d.tau = d'.tau)
    (hs : d.s ≤ d'.s) : d'.s * d'.tbar ≤ d.s * d.tbar := by
  rw [qbc_s_mul_tbar hd, qbc_s_mul_tbar hd']
  have hA : d.A0 = d'.A0 := by
    unfold QuantitativeData.A0; rw [qbc_varpi_eq hmu htau]
  rw [hA]
  have hs0 : 0 < d.s := hd.2.2.2.2.2.2.2.1
  have hs1 : d'.s ≤ 1 := hd'.2.2.2.2.2.2.2.2.1
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast hd.1
  have hs0' : 0 < d'.s := hs0.trans_le hs
  have hlog : 1 - d.s / d'.s ≤ log (32 * N / d.s) - log (32 * N / d'.s) := by
    have hq := Real.one_sub_inv_le_log_of_pos (x := d'.s / d.s) (div_pos hs0' hs0)
    rw [inv_div] at hq
    rw [← Real.log_div (by positivity) (by positivity)]
    have : 32 * (N : ℝ) / d.s / (32 * N / d'.s) = d'.s / d.s := by field_simp
    rw [this]; exact hq
  have hπ : π < 16 := by linarith [Real.pi_lt_four]
  have hπ0 := Real.pi_pos
  have key : d'.s - d.s ≤ 16 / π * N * (1 - d.s / d'.s) := by
    have h1 : 1 - d.s / d'.s = (d'.s - d.s) / d'.s := by field_simp
    rw [h1]
    have h2 : 1 ≤ 16 / π * N / d'.s := by
      rw [le_div_iff₀ hs0']
      have : 1 ≤ 16 / π := by rw [le_div_iff₀ hπ0]; linarith
      nlinarith
    have h3 : 0 ≤ d'.s - d.s := by linarith
    calc d'.s - d.s = (d'.s - d.s) * 1 := by ring
      _ ≤ (d'.s - d.s) * (16 / π * N / d'.s) := mul_le_mul_of_nonneg_left h2 h3
      _ = 16 / π * N * ((d'.s - d.s) / d'.s) := by ring
  have h4 : 16 / π * N * (1 - d.s / d'.s) ≤ 16 / π * N *
      (log (32 * N / d.s) - log (32 * N / d'.s)) :=
    mul_le_mul_of_nonneg_left hlog (by positivity)
  have h5 : 16 / π * (|d'.A0| + N * log (32 * N / d.s)) -
      16 / π * (|d'.A0| + N * log (32 * N / d'.s)) =
      16 / π * N * (log (32 * N / d.s) - log (32 * N / d'.s)) := by ring
  linarith

/-- Product order on the numerical entries: d' has no worse data. K is compared by diameter. -/
def BudgetOrder {N : ℕ} (d d' : QuantitativeData N) : Prop :=
  d.mu = d'.mu ∧ d.rho = d'.rho ∧ d.tau = d'.tau ∧
  d.beta ≤ d'.beta ∧ d.vartheta ≤ d'.vartheta ∧ d.s ≤ d'.s ∧ d.epsLoss ≤ d'.epsLoss ∧
  d'.M ≤ d.M ∧ d'.diameter ≤ d.diameter ∧ d'.M0 ≤ d.M0 ∧ d'.C1 ≤ d.C1

theorem qbc_cDio_anti {N : ℕ} {d d' : QuantitativeData N} (hd : d.NumericalValid)
    (hd' : d'.NumericalValid) (h : BudgetOrder d d') : d'.cDio ≤ d.cDio := by
  obtain ⟨hmu, hrho, htau, hβ, hϑ, hs, hε, hM, hdiam, hM0, hC1⟩ := h
  have hdp := qbc_diameter_pos hd'
  have hdp0 := qbc_diameter_pos hd
  have hden := qbc_denom_pos hd
  obtain ⟨hN, hmu1, -, -, -, hϑ0, -, -, -, -, -, hβ0, hβM, -⟩ := hd
  obtain ⟨-, -, -, -, -, hϑ0', -, -, -, -, -, hβ0', hβM', -⟩ := hd'
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hmu' : (0 : ℝ) < d.mu := by exact_mod_cast hmu1
  have hM' : 0 < d'.M := lt_of_lt_of_le hβ0' hβM'
  unfold QuantitativeData.cDio
  rw [← hmu, ← hrho, ← htau]
  have hq : d'.M / d'.beta ≤ d.M / d.beta := div_le_div₀ (by linarith) hM hβ0 hβ
  have hp : d'.beta ^ (-(1 / (d.mu : ℝ))) ≤ d.beta ^ (-(1 / (d.mu : ℝ))) :=
    Real.rpow_le_rpow_of_nonpos hβ0 hβ (neg_nonpos.mpr (by positivity))
  have hr : 1 + (4 + 1 / d'.vartheta) * √N * d'.diameter ≤
      1 + (4 + 1 / d.vartheta) * √N * d.diameter := by
    have : 1 / d'.vartheta ≤ 1 / d.vartheta := one_div_le_one_div_of_le hϑ0 hϑ
    gcongr
  have hpw : (√N * d'.diameter) ^ (N - 1) ≤ (√N * d.diameter) ^ (N - 1) := by gcongr
  have hlast : 0 < 1 + 1 / ((d.rho : ℝ) * (d.tau + 1) / d.mu - N) := by
    have := one_div_pos.mpr hden; linarith
  have hM1 : 0 < d.M := hβ0.trans_le hβM
  have hr0 : 0 < 1 + (4 + 1 / d'.vartheta) * √N * d'.diameter := by positivity
  gcongr

theorem qbc_gamma_mono {N : ℕ} {d d' : QuantitativeData N} (hd : d.NumericalValid)
    (hd' : d'.NumericalValid) (h : BudgetOrder d d') : d.gamma ≤ d'.gamma := by
  have hc := qbc_cDio_anti hd hd' h
  have hc' := qbc_cDio_pos hd'
  have hc0 := qbc_cDio_pos hd
  have hrho' := qbc_rho_pos hd.2.2.1
  have hε0 : 0 < d.epsLoss := hd.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨hmu, hrho, htau, hβ, hϑ, hs, hε, hM, hdiam, hM0, hC1⟩ := h
  unfold QuantitativeData.gamma
  rw [← hmu, ← hrho]
  have hN' : (0 : ℝ) < N := by exact_mod_cast hd.1
  refine div_le_div_of_nonneg_right (min_le_min ?_ ?_) (by norm_num)
  · have := hd.2.2.2.2.2.2.2.2.2.2.2.1
    gcongr
  · have hcd : d.epsLoss / d.cDio ≤ d'.epsLoss / d'.cDio :=
      div_le_div₀ (hε0.le.trans hε) hε hc' hc
    exact Real.rpow_le_rpow (by positivity) hcd (by positivity)

theorem qbc_tbar_anti {N : ℕ} {d d' : QuantitativeData N} (hd : d.NumericalValid)
    (hd' : d'.NumericalValid) (h : BudgetOrder d d') : d'.tbar ≤ d.tbar := by
  obtain ⟨hmu, -, htau, -, -, hs, -⟩ := h
  have hA : d.A0 = d'.A0 := by
    unfold QuantitativeData.A0; rw [qbc_varpi_eq hmu htau]
  have hs0 : 0 < d.s := hd.2.2.2.2.2.2.2.1
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast hd.1
  have hs0' : 0 < d'.s := hs0.trans_le hs
  have hsum := qbc_tbar_sum_nonneg hd'
  unfold QuantitativeData.tbar
  rw [← hA] at hsum ⊢
  have hl : log (32 * N / d'.s) ≤ log (32 * N / d.s) :=
    Real.log_le_log (div_pos (by linarith) hs0') (div_le_div_of_nonneg_left (by linarith) hs0 hs)
  have h2 : |d.A0| + N * log (32 * N / d'.s) ≤ |d.A0| + N * log (32 * N / d.s) := by
    have := mul_le_mul_of_nonneg_left hl (by linarith : (0 : ℝ) ≤ N); linarith
  have h1 : 16 / (π * d'.s) ≤ 16 / (π * d.s) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) (by gcongr)
  have := mul_le_mul h1 h2 hsum (by positivity)
  linarith

theorem qbc_tflat_mono {N : ℕ} {d d' : QuantitativeData N} (hd : d.NumericalValid)
    (hd' : d'.NumericalValid) (h : BudgetOrder d d') : d.tflat ≤ d'.tflat := by
  have hg := qbc_gamma_mono hd hd' h
  have hg0 := qbc_gamma_pos hd
  have htb := qbc_tbar_anti hd hd' h
  have htb0 := qbc_tbar_pos hd'
  have hC1' : 1 ≤ d'.C1 := hd'.2.2.2.2.2.2.2.2.2.1
  obtain ⟨hmu, hrho, htau, hβ, hϑ, hs, hε, hM, hdiam, hM0, hC1⟩ := h
  unfold QuantitativeData.tflat
  refine min_le_min (div_le_div_of_nonneg_right hϑ (Real.sqrt_nonneg _)) ?_
  have hp : d.tbar ^ (-d.tau - 1) ≤ d'.tbar ^ (-d.tau - 1) :=
    Real.rpow_le_rpow_of_nonpos htb0 htb (by linarith [hd.2.2.2.2.1])
  have hp0 : 0 < d.tbar ^ (-d.tau - 1) := Real.rpow_pos_of_pos (htb0.trans_le htb) _
  rw [← htau]
  have := mul_le_mul hg hp hp0.le (hg0.le.trans hg)
  exact div_le_div₀ (hg0.le.trans hg |>.trans' (by positivity) |> fun _ => by positivity) this
    (by positivity) (by linarith)

theorem qbc_xibar_anti {N : ℕ} {d d' : QuantitativeData N} (hd : d.NumericalValid)
    (hd' : d'.NumericalValid) (h : BudgetOrder d d') : d'.xibar ≤ d.xibar := by
  have hf := qbc_tflat_mono hd hd' h
  have hf0 := qbc_tflat_pos hd
  have hst := qbc_s_tbar_anti hd hd' h.1 h.2.2.1 h.2.2.2.2.2.1
  have hs0 : 0 < d.s := hd.2.2.2.2.2.2.2.1
  have hs0' : 0 < d'.s := hs0.trans_le h.2.2.2.2.2.1
  obtain ⟨hmu, hrho, htau, hβ, hϑ, hs, hε, hM, hdiam, hM0, hC1⟩ := h
  unfold QuantitativeData.xibar
  rw [← htau]
  have h1 : 1 / (d'.s / 24) ≤ 1 / (d.s / 24) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  have h2 : 1 / d'.tflat ≤ 1 / d.tflat := one_div_le_one_div_of_le hf0 hf
  have h3 : d'.tbar * (d'.s / 24) ≤ d.tbar * (d.s / 24) := by linarith
  gcongr

theorem qb_mono {N : ℕ} (d d' : QuantitativeData N) (hd : d.NumericalValid)
    (hd' : d'.NumericalValid) (h : BudgetOrder d d') :
    d.gamma ≤ d'.gamma ∧ thresholds d ≤ thresholds d' := by
  refine ⟨qbc_gamma_mono hd hd' h, ?_⟩
  have hl := qbc_lambdaFlat_pos hd
  have hN : 0 < N := hd.1
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hC : 0 < d'.C1 := by have := hd'.2.2.2.2.2.2.2.2.2.1; linarith
  have hlam : d.lambdaFlat ≤ d'.lambdaFlat := by
    have h0 := h
    obtain ⟨hmu, hrho, htau, hβ, hϑ, hs, hε, hM, hdiam, hM0, hC1⟩ := h
    rw [qbc_lambdaFlat_eq, qbc_lambdaFlat_eq d', ← hmu, ← htau, ← qbc_varpi_eq hmu htau]
    refine qbcLam_mono hN ?_ (qbc_xibar_pos hd') (qbc_xibar_anti hd hd' h0)
      (qbc_gamma_pos hd).le (qbc_gamma_mono hd hd' h0) (hd.2.2.2.2.2.2.2.1.le) hs
      (qbc_tbar_pos hd') (qbc_tbar_anti hd hd' h0) hd.2.2.2.2.1
      (qbc_thetaMax_pos hd).le (qbc_thetaMax_mono hmu hrho hd.2.2.2.2.2.2.2.2.2.2.2.1 hβ
        hd'.2.2.2.2.2.2.2.2.2.2.1 hM0)
      (qbc_tflat_pos hd).le (qbc_tflat_mono hd hd' h0) (qbc_cutoffConstant_pos hd.1 d.mu)
      (qbc_varpi_pos d).le
    exact div_le_div_of_nonneg_right (qbc_tflat_mono hd hd' h0) (by norm_num)
  unfold thresholds
  have hC0 : 0 < d.C1 := by have := hd.2.2.2.2.2.2.2.2.2.1; linarith
  exact div_le_div₀ (by positivity) (pow_le_pow_left₀ hl.le hlam 2) (by positivity)
    (by gcongr; exact h.2.2.2.2.2.2.2.2.2.2)

/-- The old threshold's numerical projection, with its three auxiliary quantities named. -/
noncomputable def qbcOldT {N : ℕ} (d : QuantitativeData N) : ℝ :=
  max 1 (16 / (π * d.s) * (d.A0 + N * log (32 * N / d.s)))

noncomputable def qbcOldt {N : ℕ} (d : QuantitativeData N) : ℝ :=
  min (d.vartheta / sqrt N) (d.gamma * qbcOldT d ^ (-d.tau - 1) / (4 * d.C1))

noncomputable def qbcOldX {N : ℕ} (d : QuantitativeData N) : ℝ :=
  (2 : ℝ) ^ (d.tau + 1) * (1 + qbcOldt d / (d.s / 24) + (d.s / 24) / qbcOldt d +
    qbcOldT d * (d.s / 24))

theorem qbc_old_eq {N : ℕ} (d : QuantitativeData N) :
    p11c_oldThreshold d = (qbcLam N d.mu d.tau (d.C1 * qbcOldt d / 8) d.varpi (qbcOldX d)
      d.gamma d.s (qbcOldT d) d.thetaMax (qbcOldt d) (p11c_cutoffConstant N d.mu)) ^ 2 /
      (2 * N * d.C1) := rfl

theorem qbc_oldT_bounds {N : ℕ} {d : QuantitativeData N} (hd : d.NumericalValid) :
    1 ≤ qbcOldT d ∧ qbcOldT d ≤ d.tbar := by
  have hs0 : 0 < d.s := hd.2.2.2.2.2.2.2.1
  have h := qbc_log_term_nonneg hd
  have hA : d.A0 ≤ |d.A0| := le_abs_self _
  refine ⟨le_max_left _ _, max_le (qbc_tbar_ge_one hd) ?_⟩
  unfold QuantitativeData.tbar
  have h0 : 0 ≤ 16 / (π * d.s) := by positivity
  have h1 := mul_le_mul_of_nonneg_left (by linarith : d.A0 + N * log (32 * N / d.s) ≤
    |d.A0| + N * log (32 * N / d.s)) h0
  linarith

theorem qbc_oldt_bounds {N : ℕ} {d : QuantitativeData N} (hd : d.NumericalValid) :
    0 < qbcOldt d ∧ d.tflat ≤ qbcOldt d ∧ qbcOldt d ≤ 1 := by
  obtain ⟨hT1, hT⟩ := qbc_oldT_bounds hd
  have hg := qbc_gamma_pos hd
  have hC : 0 < d.C1 := by have := hd.2.2.2.2.2.2.2.2.2.1; linarith
  have hN' : (0 : ℝ) < N := by exact_mod_cast hd.1
  have hT0 : 0 < qbcOldT d := by linarith
  have htau : 0 ≤ d.tau := hd.2.2.2.2.1
  have hp : d.tbar ^ (-d.tau - 1) ≤ qbcOldT d ^ (-d.tau - 1) :=
    Real.rpow_le_rpow_of_nonpos hT0 hT (by linarith)
  have hfirst : d.vartheta / √N ≤ 1 := by
    rw [div_le_one (Real.sqrt_pos.mpr hN')]
    exact hd.2.2.2.2.2.2.1.trans
      (by simpa using Real.one_le_sqrt.mpr (show (1 : ℝ) ≤ N by exact_mod_cast hd.1))
  refine ⟨?_, ?_, (min_le_left _ _).trans hfirst⟩
  · unfold qbcOldt
    refine lt_min (by have := hd.2.2.2.2.2.1; positivity) (by positivity)
  · unfold QuantitativeData.tflat qbcOldt
    refine min_le_min le_rfl ?_
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hp hg.le) (by positivity)

theorem qbc_oldX_bounds {N : ℕ} {d : QuantitativeData N} (hd : d.NumericalValid) :
    0 < qbcOldX d ∧ qbcOldX d ≤ d.xibar := by
  obtain ⟨hT1, hT⟩ := qbc_oldT_bounds hd
  obtain ⟨ht0, htf, ht1⟩ := qbc_oldt_bounds hd
  have hf0 := qbc_tflat_pos hd
  have hs0 : 0 < d.s := hd.2.2.2.2.2.2.2.1
  have hs1 : d.s ≤ 1 := hd.2.2.2.2.2.2.2.2.1
  refine ⟨?_, ?_⟩
  · unfold qbcOldX
    have : 0 < qbcOldT d := by linarith
    positivity
  · unfold qbcOldX QuantitativeData.xibar
    have h1 : qbcOldt d / (d.s / 24) ≤ 1 / (d.s / 24) :=
      div_le_div_of_nonneg_right ht1 (by positivity)
    have h2 : (d.s / 24) / qbcOldt d ≤ 1 / d.tflat := by
      calc (d.s / 24) / qbcOldt d ≤ 1 / qbcOldt d :=
            div_le_div_of_nonneg_right (by linarith) ht0.le
        _ ≤ 1 / d.tflat := one_div_le_one_div_of_le hf0 htf
    have h3 : qbcOldT d * (d.s / 24) ≤ d.tbar * (d.s / 24) :=
      mul_le_mul_of_nonneg_right hT (by positivity)
    gcongr

theorem qb_comp {N : ℕ} (d : QuantitativeData N) (hd : d.NumericalValid) (M0' : ℝ)
    (h0 : 0 < M0') (hM : M0' ≤ d.M0) :
    0 < thresholds d ∧ thresholds d ≤ p11c_oldThreshold { d with M0 := M0' } := by
  refine ⟨qbc_thresholds_pos hd, ?_⟩
  obtain ⟨hT1, hT⟩ := qbc_oldT_bounds hd
  obtain ⟨ht0, htf, ht1⟩ := qbc_oldt_bounds hd
  obtain ⟨hX0, hX⟩ := qbc_oldX_bounds hd
  have hl := qbc_lambdaFlat_pos hd
  have hN : 0 < N := hd.1
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hC1 : 1 ≤ d.C1 := hd.2.2.2.2.2.2.2.2.2.1
  have hC : 0 < d.C1 := by linarith
  rw [qbc_old_eq]
  have hlam : d.lambdaFlat ≤ qbcLam N d.mu d.tau (d.C1 * qbcOldt d / 8) d.varpi (qbcOldX d)
      d.gamma d.s (qbcOldT d) ({ d with M0 := M0' } : QuantitativeData N).thetaMax (qbcOldt d)
      (p11c_cutoffConstant N d.mu) := by
    rw [qbc_lambdaFlat_eq]
    refine qbcLam_mono hN ?_ hX0 hX (qbc_gamma_pos hd).le le_rfl hd.2.2.2.2.2.2.2.1.le le_rfl
      (by linarith) hT hd.2.2.2.2.1 (qbc_thetaMax_pos hd).le ?_ (qbc_tflat_pos hd).le htf
      (qbc_cutoffConstant_pos hd.1 d.mu) (qbc_varpi_pos d).le
    · have : d.tflat ≤ d.C1 * qbcOldt d := htf.trans (by nlinarith)
      linarith
    · exact qbc_thetaMax_mono (d' := ({ d with M0 := M0' } : QuantitativeData N)) rfl rfl
        hd.2.2.2.2.2.2.2.2.2.2.2.1 le_rfl h0 hM
  unfold thresholds
  exact div_le_div_of_nonneg_right (pow_le_pow_left₀ hl.le hlam 2) (by positivity)

end KAM.Planetary
