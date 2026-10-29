/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Quantitative.Thresholds

/-!
# Positivity of the explicit cutoff constant and of the diameter (P11C-Q3)

Fragments for `qb_poly`: the explicit cutoff constant `p11c_cutoffConstant N mu` is strictly
positive for `1 ≤ N`, and a valid datum has positive diameter (its compact set has positive
volume).
-/

@[expose] public noncomputable section
open Set Metric Real MeasureTheory Function
namespace KAM.Planetary

theorem qbPoly_bump_nonneg (mu : ℕ) (x : ℝ) : 0 ≤ p11c_bump mu x := by
  unfold p11c_bump; positivity

theorem qbPoly_bump_continuous (mu : ℕ) : Continuous (p11c_bump mu) := by
  unfold p11c_bump; fun_prop

theorem qbPoly_bump_zero (mu : ℕ) : p11c_bump mu 0 = 1 := by
  simp [p11c_bump]

theorem qbPoly_bump_integral_pos (mu : ℕ) : 0 < ∫ y : ℝ, p11c_bump mu y := by
  have hc : HasCompactSupport (p11c_bump mu) := by
    refine HasCompactSupport.intro (isCompact_Icc (a := (-1 : ℝ)) (b := 1)) ?_
    intro x hx
    have : 1 < x ^ 2 := by
      simp only [mem_Icc, not_and_or, not_le] at hx
      rcases hx with h | h <;> nlinarith
    simp [p11c_bump, max_eq_left (by linarith : 1 - x ^ 2 ≤ 0)]
  have hint : Integrable (p11c_bump mu) :=
    (qbPoly_bump_continuous mu).integrable_of_hasCompactSupport hc
  rw [integral_pos_iff_support_of_nonneg (qbPoly_bump_nonneg mu) hint]
  refine (qbPoly_bump_continuous mu).isOpen_support.measure_pos volume ⟨0, ?_⟩
  simp [Function.mem_support, qbPoly_bump_zero]

theorem qbPoly_diameter_pos {N : ℕ} (d : QuantitativeData N) (hd : d.NumericalValid) :
    0 < d.diameter := by
  obtain ⟨hN, -, -, -, -, -, -, -, -, -, -, -, -, hK, hε, hvol⟩ := hd
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  unfold QuantitativeData.diameter
  refine Metric.diam_pos ?_ hK.isBounded
  by_contra hns
  have hsub : d.K.Subsingleton := Set.not_nontrivial_iff.mp hns
  rcases hsub.eq_empty_or_singleton with h | ⟨x, h⟩
  · simp [h] at hvol
  · rw [h, measure_singleton] at hvol
    simp at hvol

theorem qbPoly_mollifierMass_zero (mu : ℕ) : p11c_mollifierMass mu 0 = 1 := by
  have hI := qbPoly_bump_integral_pos mu
  unfold p11c_mollifierMass
  simp only [iteratedDeriv_zero]
  have h : ∀ x, |p11c_mollifier mu x| = p11c_bump mu x / ∫ y, p11c_bump mu y := by
    intro x
    unfold p11c_mollifier
    rw [abs_of_nonneg (div_nonneg (qbPoly_bump_nonneg mu x) hI.le)]
  simp_rw [h]
  rw [integral_div]
  exact div_self hI.ne'

theorem qbPoly_cutoffDerivative_zero (N mu : ℕ) : p11c_cutoffDerivative N mu 0 = 1 := by
  unfold p11c_cutoffDerivative
  have : {v : ℝ | ∃ a : Fin N → ℕ, (∑ i, a i) = 0 ∧ v = ∏ i, p11c_mollifierMass mu (a i)} =
      {1} := by
    ext v
    simp only [mem_ofPred_eq, mem_singleton_iff]
    constructor
    · rintro ⟨a, ha, rfl⟩
      have h0 : ∀ i, a i = 0 := fun i => by
        have := (Finset.sum_eq_zero_iff.mp ha) i (Finset.mem_univ i)
        exact this
      simp [h0, qbPoly_mollifierMass_zero]
    · rintro rfl
      exact ⟨0, by simp, by simp [qbPoly_mollifierMass_zero]⟩
  rw [this, csSup_singleton]
  simp

theorem qbPoly_cutoffConstant_pos (N mu : ℕ) (hN : 1 ≤ N) : 0 < p11c_cutoffConstant N mu := by
  unfold p11c_cutoffConstant
  refine mul_pos (Real.sqrt_pos.mpr (by exact_mod_cast hN)) ?_
  set f : ℕ → ℝ := fun k => (4 : ℝ) ^ k *
    ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) * p11c_cutoffDerivative N mu j *
      ((k - j : ℕ) : ℝ) ^ (k - j) with hf
  have hfin : {v : ℝ | ∃ k ≤ mu, v = f k}.Finite :=
    ((Set.finite_Iic mu).image f).subset (by rintro v ⟨k, hk, rfl⟩; exact ⟨k, hk, rfl⟩)
  have h0 : f 0 ≤ sSup {v : ℝ | ∃ k ≤ mu, v = f k} :=
    le_csSup hfin.bddAbove ⟨0, Nat.zero_le _, rfl⟩
  have hf0 : f 0 = 1 := by
    simp [hf, qbPoly_cutoffDerivative_zero]
  linarith

end KAM.Planetary
