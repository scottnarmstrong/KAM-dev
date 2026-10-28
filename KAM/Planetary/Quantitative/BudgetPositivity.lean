/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Quantitative.Thresholds

/-!
# Quantitative budget: positivity of the threshold data (P11C-Q2 helper)

Positivity of the cutoff constant, the Diophantine constant, `gamma`, `tbar`, `tflat`, `xibar`,
`thetaMax`, `lambdaFlat` and `thresholds` for numerically valid data.

-/

@[expose] public noncomputable section
open Set Metric Real MeasureTheory Function
open scoped ContDiff Topology
namespace KAM.Planetary


theorem qbc_bump_cont (mu : ℕ) : Continuous (p11c_bump mu) := by
  unfold p11c_bump; fun_prop

theorem qbc_bump_integral_pos (mu : ℕ) : 0 < ∫ y : ℝ, p11c_bump mu y := by
  have hc : HasCompactSupport (p11c_bump mu) := by
    refine HasCompactSupport.intro (isCompact_Icc (a := (-1 : ℝ)) (b := 1)) ?_
    intro x hx
    have : 1 < x ^ 2 := by
      simp only [mem_Icc, not_and_or, not_le] at hx
      rcases hx with h | h <;> nlinarith
    unfold p11c_bump
    rw [max_eq_left (by linarith)]; simp
  refine (qbc_bump_cont mu).integral_pos_of_hasCompactSupport_nonneg_nonzero hc
    (fun x => by unfold p11c_bump; positivity) (x := 0) ?_
  unfold p11c_bump; simp

theorem qbc_mollifierMass_zero (mu : ℕ) : p11c_mollifierMass mu 0 = 1 := by
  have hp := (qbc_bump_integral_pos mu).ne'
  unfold p11c_mollifierMass
  simp only [iteratedDeriv_zero]
  have : ∀ x, |p11c_mollifier mu x| = p11c_bump mu x / ∫ y : ℝ, p11c_bump mu y := by
    intro x
    unfold p11c_mollifier
    rw [abs_of_nonneg]
    exact div_nonneg (by unfold p11c_bump; positivity) (qbc_bump_integral_pos mu).le
  simp_rw [this]
  rw [integral_div]
  exact div_self hp

theorem qbc_cutoffDerivative_zero (N mu : ℕ) : p11c_cutoffDerivative N mu 0 = 1 := by
  unfold p11c_cutoffDerivative
  have : {v : ℝ | ∃ a : Fin N → ℕ, (∑ i, a i) = 0 ∧
      v = ∏ i, p11c_mollifierMass mu (a i)} = {1} := by
    ext v
    simp only [Set.mem_ofPred_eq, mem_singleton_iff]
    constructor
    · rintro ⟨a, ha, rfl⟩
      have : ∀ i, a i = 0 := fun i => by
        have := (Finset.sum_eq_zero_iff.mp ha) i (Finset.mem_univ i); exact this
      simp [this, qbc_mollifierMass_zero]
    · rintro rfl
      exact ⟨fun _ => 0, by simp, by simp [qbc_mollifierMass_zero]⟩
  rw [this, csSup_singleton]; simp

theorem qbc_cutoffConstant_pos {N : ℕ} (hN : 1 ≤ N) (mu : ℕ) : 0 < p11c_cutoffConstant N mu := by
  unfold p11c_cutoffConstant
  refine mul_pos (Real.sqrt_pos.mpr (by exact_mod_cast hN)) ?_
  set f : ℕ → ℝ := fun k => (4 : ℝ) ^ k *
    ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) * p11c_cutoffDerivative N mu j *
      ((k - j : ℕ) : ℝ) ^ (k - j) with hf
  have hS : {v : ℝ | ∃ k ≤ mu, v = f k} = f '' Set.Iic mu := by
    ext v; simp [eq_comm]
  rw [hS]
  have hb : BddAbove (f '' Set.Iic mu) := ((Set.finite_Iic mu).image f).bddAbove
  have h0 : f 0 ∈ f '' Set.Iic mu := ⟨0, by simp, rfl⟩
  have : f 0 = 1 := by simp [hf, qbc_cutoffDerivative_zero]
  have := le_csSup hb h0
  linarith
theorem qbc_diameter_pos {N : ℕ} {d : QuantitativeData N} (hd : d.NumericalValid) :
    0 < d.diameter := by
  obtain ⟨hN, -, -, -, -, -, -, -, -, -, -, -, -, hK, -, hvol⟩ := hd
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  unfold QuantitativeData.diameter
  by_cases hn : d.K.Nontrivial
  · exact Metric.diam_pos hn hK.isBounded
  · have hs : d.K.Subsingleton := Set.not_nontrivial_iff.mp hn
    have := hs.measure_zero (μ := (volume : Measure (Fin N → ℝ)))
    rw [this] at hvol
    exact absurd hvol not_lt_zero

theorem qbc_rho_pos {N : ℕ} {d : QuantitativeData N} (h : d.rho = 1 ∨ d.rho = 2) :
    (0 : ℝ) < d.rho := by
  rcases h with h | h <;> simp [h]

theorem qbc_denom_pos {N : ℕ} {d : QuantitativeData N} (hd : d.NumericalValid) :
    0 < (d.rho : ℝ) * (d.tau + 1) / d.mu - N := by
  obtain ⟨-, hmu, hrho, htau1, -⟩ := hd
  have hmu' : (0 : ℝ) < d.mu := by exact_mod_cast hmu
  have hrho' := qbc_rho_pos hrho
  have h1 : (N : ℝ) * d.mu / d.rho < d.tau + 1 := by linarith
  rw [div_lt_iff₀ hrho'] at h1
  rw [sub_pos, lt_div_iff₀ hmu']
  linarith

theorem qbc_cDio_pos {N : ℕ} {d : QuantitativeData N} (hd : d.NumericalValid) :
    0 < d.cDio := by
  have hdiam := qbc_diameter_pos hd
  have hden := qbc_denom_pos hd
  obtain ⟨hN, hmu, hrho, htau1, htau0, hϑ0, hϑ1, hs0, hs1, hC1, hM0, hβ, hβM, hK, hε, hvol⟩ := hd
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hmu' : (0 : ℝ) < d.mu := by exact_mod_cast hmu
  have hM : 0 < d.M := lt_of_lt_of_le hβ hβM
  have hlast : 0 < 1 + 1 / ((d.rho : ℝ) * (d.tau + 1) / d.mu - N) := by
    have := one_div_pos.mpr hden; linarith
  unfold QuantitativeData.cDio
  have := hlast
  positivity

theorem qbc_gamma_pos {N : ℕ} {d : QuantitativeData N} (hd : d.NumericalValid) :
    0 < d.gamma := by
  have hc := qbc_cDio_pos hd
  have hrho' := qbc_rho_pos hd.2.2.1
  obtain ⟨hN, hmu, hrho, htau1, htau0, hϑ0, hϑ1, hs0, hs1, hC1, hM0, hβ, hβM, hK, hε, hvol⟩ := hd
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  unfold QuantitativeData.gamma
  positivity

theorem qbc_log_term_nonneg {N : ℕ} {d : QuantitativeData N} (hd : d.NumericalValid) :
    0 ≤ (N : ℝ) * log (32 * N / d.s) := by
  obtain ⟨hN, -, -, -, -, -, -, hs0, hs1, -⟩ := hd
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  refine mul_nonneg (by linarith) (Real.log_nonneg ?_)
  rw [one_le_div hs0]; linarith

theorem qbc_tbar_ge_one {N : ℕ} {d : QuantitativeData N} (hd : d.NumericalValid) :
    1 ≤ d.tbar := by
  have h := qbc_log_term_nonneg hd
  have hs0 : 0 < d.s := hd.2.2.2.2.2.2.2.1
  unfold QuantitativeData.tbar
  have : 0 ≤ 16 / (π * d.s) * (|d.A0| + N * log (32 * N / d.s)) := by positivity
  linarith

theorem qbc_tbar_pos {N : ℕ} {d : QuantitativeData N} (hd : d.NumericalValid) : 0 < d.tbar :=
  lt_of_lt_of_le one_pos (qbc_tbar_ge_one hd)

theorem qbc_varpi_pos {N : ℕ} (d : QuantitativeData N) : 0 < d.varpi := by
  unfold QuantitativeData.varpi; positivity

theorem qbc_tflat_pos {N : ℕ} {d : QuantitativeData N} (hd : d.NumericalValid) :
    0 < d.tflat := by
  have hg := qbc_gamma_pos hd
  have ht := qbc_tbar_pos hd
  obtain ⟨hN, hmu, hrho, htau1, htau0, hϑ0, hϑ1, hs0, hs1, hC1, hM0, hβ, hβM, hK, hε, hvol⟩ := hd
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hC : 0 < d.C1 := by linarith
  unfold QuantitativeData.tflat
  refine lt_min (by positivity) (by positivity)

theorem qbc_tflat_le_one {N : ℕ} {d : QuantitativeData N} (hd : d.NumericalValid) :
    d.tflat ≤ 1 := by
  obtain ⟨hN, hmu, hrho, htau1, htau0, hϑ0, hϑ1, hs0, hs1, hC1, hM0, hβ, hβM, hK, hε, hvol⟩ := hd
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  unfold QuantitativeData.tflat
  refine (min_le_left _ _).trans ?_
  rw [div_le_one (Real.sqrt_pos.mpr (by linarith))]
  exact hϑ1.trans (by simpa using Real.one_le_sqrt.mpr hN')

theorem qbc_xibar_pos {N : ℕ} {d : QuantitativeData N} (hd : d.NumericalValid) :
    0 < d.xibar := by
  have hf := qbc_tflat_pos hd
  have ht := qbc_tbar_pos hd
  have hs0 : 0 < d.s := hd.2.2.2.2.2.2.2.1
  unfold QuantitativeData.xibar; positivity

theorem qbc_thetaMax_pos {N : ℕ} {d : QuantitativeData N} (hd : d.NumericalValid) :
    0 < d.thetaMax := by
  obtain ⟨hN, hmu, hrho, htau1, htau0, hϑ0, hϑ1, hs0, hs1, hC1, hM0, hβ, hβM, hK, hε, hvol⟩ := hd
  unfold QuantitativeData.thetaMax
  split_ifs
  · positivity
  · exact lt_min hβ (by positivity)

theorem qbc_lambdaFlat_pos {N : ℕ} {d : QuantitativeData N} (hd : d.NumericalValid) :
    0 < d.lambdaFlat := by
  have hf := qbc_tflat_pos hd
  have ht := qbc_tbar_pos hd
  have hx := qbc_xibar_pos hd
  have hg := qbc_gamma_pos hd
  have hth := qbc_thetaMax_pos hd
  have hv := qbc_varpi_pos d
  have hcc := qbc_cutoffConstant_pos hd.1 d.mu
  have hs0 : 0 < d.s := hd.2.2.2.2.2.2.2.1
  have hN' : (0 : ℝ) < N := by exact_mod_cast hd.1
  unfold QuantitativeData.lambdaFlat
  refine lt_min (lt_min (by positivity) (mul_pos (lt_min (by positivity) (by positivity))
    (by positivity))) (by positivity)

theorem qbc_thresholds_pos {N : ℕ} {d : QuantitativeData N} (hd : d.NumericalValid) :
    0 < thresholds d := by
  have hl := qbc_lambdaFlat_pos hd
  have hN' : (0 : ℝ) < N := by exact_mod_cast hd.1
  have hC : 0 < d.C1 := by have := hd.2.2.2.2.2.2.2.2.2.1; linarith
  unfold thresholds; positivity

end KAM.Planetary
