/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PlanarTorsion.LaplaceReduction
public import KAM.Planetary.PlanarTorsion.PairCoefficients.Series
public import KAM.Planetary.SecularForm.LaplaceIdentities

/-!
# Planar quartic torsion: `b_{1/2}^{(k)}` as a power series on `(-1, 1)` (P11C, package T4)

The adapter `p11c_laplace (1/2) k` agrees on all of `(-1, 1)` with the even/odd power series
`a ^ k * ∑ halfCoef k q (a ^ 2) ^ q` of Part 8, hence is analytic there, and its Taylor head is an
explicit polynomial with a remainder that vanishes to order `8`.
-/

@[expose] public noncomputable section
open Set Filter Topology Real MeasureTheory
namespace KAM.Planetary

/-- The Part-8 power series of `b_{1/2}^{(k)}`, written in `a ^ k` and `a ^ 2`. -/
def p11cHalf (k : ℕ) (a : ℝ) : ℝ := a ^ k * p11cSeries (SecularForm.halfCoef k) (a ^ 2)

theorem p11cHalf_good (k : ℕ) : P11cGood (SecularForm.halfCoef k) :=
  P11cGood.of_bound fun q => by simpa using SecularForm.halfCoef_abs_le k q

theorem p11c_laplace_neg (s : ℝ) (k : ℕ) (a : ℝ) :
    p11c_laplace s k (-a) = (-1) ^ k * p11c_laplace s k a := by
  set F : ℝ → ℝ := fun t => cos ((k : ℝ) * t) / (1 + a ^ 2 - 2 * a * cos t) ^ s with hF
  have hper : Function.Periodic F (2 * π) := fun t => by
    simp only [hF]
    rw [show (k : ℝ) * (t + 2 * π) = k * t + (k : ℕ) * (2 * π) by ring, cos_add_nat_mul_two_pi,
      cos_add_two_pi]
  have h1 : ∫ t in (0 : ℝ)..(2 * π), F t = ∫ t in (0 : ℝ)..(2 * π), F (t + π) := by
    rw [intervalIntegral.integral_comp_add_right, ← zero_add (2 * π),
      hper.intervalIntegral_add_eq 0 π]
    simp only [zero_add]
    rw [show 2 * π + π = π + 2 * π by ring]
  have h2 : ∀ t, F (t + π) = (-1) ^ k * (cos ((k : ℝ) * t) /
      (1 + (-a) ^ 2 - 2 * (-a) * cos t) ^ s) := fun t => by
    simp only [hF]
    rw [mul_add, cos_add_nat_mul_pi, cos_add_pi]
    ring_nf
  have key : ∫ t in (0 : ℝ)..(2 * π), F t = (-1) ^ k * ∫ t in (0 : ℝ)..(2 * π),
      cos ((k : ℝ) * t) / (1 + (-a) ^ 2 - 2 * (-a) * cos t) ^ s := by
    rw [h1]; simp only [h2]; exact intervalIntegral.integral_const_mul _ _
  simp only [p11c_laplace, Int.cast_natCast]
  simp only [hF] at key
  rw [key]
  have h3 : ((-1 : ℝ) ^ k) * (-1) ^ k = 1 := by rw [← mul_pow]; simp
  linear_combination (-(2 * π)⁻¹ * ∫ t in (0 : ℝ)..(2 * π),
    cos ((k : ℝ) * t) / (1 + (-a) ^ 2 - 2 * (-a) * cos t) ^ s) * h3

theorem p11c_laplace_half_nonneg (k : ℕ) {a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1) :
    p11c_laplace (1 / 2) k a = p11cHalf k a := by
  have h : p11c_laplace (1 / 2) k a = SecularForm.laplace_def (1 / 2) k a := by
    unfold p11c_laplace SecularForm.laplace_def
    congr 1
    refine intervalIntegral.integral_congr fun t _ => ?_
    have hk : 0 ≤ 1 + a ^ 2 - 2 * a * cos t := by nlinarith [cos_le_one t, sq_nonneg (1 - a)]
    simp only [Int.cast_natCast]
    rw [Real.rpow_neg hk, div_eq_mul_inv]
  rw [h, ← (SecularForm.hasSum_laplaceTerm (by norm_num) ha ha1 k).tsum_eq]
  unfold p11cHalf p11cSeries
  rw [← tsum_mul_left]
  refine tsum_congr fun q => ?_
  rw [SecularForm.laplaceTerm_half, pow_add, pow_mul]
  ring

theorem p11c_laplace_half (k : ℕ) {a : ℝ} (ha : |a| < 1) :
    p11c_laplace (1 / 2) k a = p11cHalf k a := by
  rcases le_or_gt 0 a with h0 | h0
  · exact p11c_laplace_half_nonneg k h0 (abs_lt.1 ha).2
  · have h1 := p11c_laplace_neg (1 / 2) k (-a)
    rw [neg_neg] at h1
    rw [h1, p11c_laplace_half_nonneg k (by linarith) (by linarith [(abs_lt.1 ha).1])]
    unfold p11cHalf
    rw [neg_sq, neg_pow a k]
    have h2 : ((-1 : ℝ) ^ k) * (-1) ^ k = 1 := by rw [← mul_pow]; simp
    linear_combination (a ^ k * p11cSeries (SecularForm.halfCoef k) (a ^ 2)) * h2

theorem p11cHalf_analyticAt (k : ℕ) {a : ℝ} (ha : |a| < 1) : AnalyticAt ℝ (p11cHalf k) a := by
  have h1 : AnalyticAt ℝ (p11cSeries (SecularForm.halfCoef k)) (a ^ 2) :=
    (p11cHalf_good k).analyticAt (by rw [abs_pow]; nlinarith [abs_nonneg a])
  exact (by fun_prop : AnalyticAt ℝ (fun x : ℝ => x ^ k) a).mul
    (h1.comp (f := fun x : ℝ => x ^ 2) (by fun_prop))

/-- The Taylor head of `p11cHalf k` of length four in `a ^ 2`. -/
def p11cHead (k : ℕ) (a : ℝ) : ℝ :=
  a ^ k * ∑ q ∈ Finset.range 4, SecularForm.halfCoef k q * (a ^ 2) ^ q

/-- The remainder factor of `p11cHalf k`. -/
def p11cTail (k : ℕ) (a : ℝ) : ℝ :=
  a ^ k * p11cSeries (fun q => SecularForm.halfCoef k (q + 4)) (a ^ 2)

theorem p11cHalf_eq_head_add (k : ℕ) {a : ℝ} (ha : |a| < 1) :
    p11cHalf k a = p11cHead k a + a ^ 8 * p11cTail k a := by
  have := (p11cHalf_good k).split (x := a ^ 2) (by rw [abs_pow]; nlinarith [abs_nonneg a]) 4
  unfold p11cHalf p11cHead p11cTail
  rw [this]
  ring

theorem p11cTail_analyticAt (k : ℕ) {a : ℝ} (ha : |a| < 1) : AnalyticAt ℝ (p11cTail k) a := by
  have h1 : AnalyticAt ℝ (p11cSeries (fun q => SecularForm.halfCoef k (q + 4))) (a ^ 2) :=
    ((p11cHalf_good k).shift 4).analyticAt (by rw [abs_pow]; nlinarith [abs_nonneg a])
  exact (by fun_prop : AnalyticAt ℝ (fun x : ℝ => x ^ k) a).mul
    (h1.comp (f := fun x : ℝ => x ^ 2) (by fun_prop))

theorem pcoef_half_values :
    SecularForm.pcoef (1 / 2) 0 = 1 ∧ SecularForm.pcoef (1 / 2) 1 = 1 / 2 ∧
    SecularForm.pcoef (1 / 2) 2 = 3 / 8 ∧ SecularForm.pcoef (1 / 2) 3 = 5 / 16 ∧
    SecularForm.pcoef (1 / 2) 4 = 35 / 128 := by
  simp only [SecularForm.pcoef, SecularForm.poch, Finset.prod_range_succ, Finset.prod_range_zero]
  norm_num [Nat.factorial]

theorem p11cHead_zero (a : ℝ) :
    p11cHead 0 a = 1 + a ^ 2 / 4 + 9 / 64 * a ^ 4 + 25 / 256 * a ^ 6 := by
  obtain ⟨h0, h1, h2, h3, -⟩ := pcoef_half_values
  simp only [p11cHead, Finset.sum_range_succ, Finset.sum_range_zero, SecularForm.halfCoef,
    h0, h1, h2, h3]
  ring

theorem p11cHead_one (a : ℝ) :
    p11cHead 1 a = a / 2 + 3 / 16 * a ^ 3 + 15 / 128 * a ^ 5 + 175 / 2048 * a ^ 7 := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := pcoef_half_values
  simp only [p11cHead, Finset.sum_range_succ, Finset.sum_range_zero, SecularForm.halfCoef,
    zero_add, Nat.reduceAdd, h0, h1, h2, h3, h4]
  ring

end KAM.Planetary
