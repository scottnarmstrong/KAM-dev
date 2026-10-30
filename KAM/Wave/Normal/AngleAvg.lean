/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.Pi

/-!
# Angle averages of products of cosines (for blueprint `bpW:w0n:AB`)

Off the frontier: source-faithful infrastructure used by several nodes. The dependency graph is
still being built.

`angleMeasure` is the normalized Lebesgue measure on `[0, 2π]`, and `KAM.Wave.angleAvg N F` is the
average of `F : (Fin N → ℝ) → ℝ` over the torus of angles `φ ∈ [0, 2π]ᴺ` (the product
probability measure). The main results are the moments `E cos^m` (`m ≤ 4`) and the four-fold
product formula
`E[cos φ_i cos φ_j cos φ_k cos φ_l] = ¼([i=j][k=l] + [i=k][j=l] + [i=l][j=k]) - ⅜[i=j=k=l]`
(blueprint Step `stepW:w0n:moments`).
-/

@[expose] public noncomputable section

open MeasureTheory Real

namespace KAM.Wave

/-- The normalized Lebesgue measure on `[0, 2π]`. -/
def angleMeasure : Measure ℝ :=
  (ENNReal.ofReal (2 * π))⁻¹ • volume.restrict (Set.Icc (0 : ℝ) (2 * π))

instance : IsProbabilityMeasure angleMeasure := by
  refine ⟨?_⟩
  simp only [angleMeasure, Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ,
    Set.univ_inter, Real.volume_Icc, smul_eq_mul, sub_zero]
  exact ENNReal.inv_mul_cancel (by simp [Real.pi_pos]) ENNReal.ofReal_ne_top

/-- The average over the torus of angles `[0, 2π]ᴺ`. -/
def angleAvg (N : ℕ) (F : (Fin N → ℝ) → ℝ) : ℝ :=
  ∫ φ, F φ ∂(Measure.pi fun _ : Fin N => angleMeasure)

theorem integral_angleMeasure (f : ℝ → ℝ) :
    ∫ x, f x ∂angleMeasure = (2 * π)⁻¹ * ∫ x in (0 : ℝ)..(2 * π), f x := by
  unfold angleMeasure
  rw [integral_smul_measure, intervalIntegral.integral_of_le (by positivity),
    ← integral_Icc_eq_integral_Ioc]
  simp [ENNReal.toReal_inv, Real.pi_pos.le]

/-- The moments `E cos^m φ` for `m = 0, …, 4`: `1, 0, ½, 0, ⅜`. -/
def cosMoment : ℕ → ℝ
  | 0 => 1
  | 2 => 1 / 2
  | 4 => 3 / 8
  | _ => 0

theorem integral_angleMeasure_cos_pow (m : ℕ) (hm : m ≤ 4) :
    ∫ x, Real.cos x ^ m ∂angleMeasure = cosMoment m := by
  rw [integral_angleMeasure]
  have h2 : ∫ x in (0 : ℝ)..(2 * π), Real.cos x ^ 2 = π := by
    rw [integral_cos_sq]; simp
  have h1 : ∫ x in (0 : ℝ)..(2 * π), Real.cos x = 0 := by simp
  interval_cases m
  · simp [cosMoment]; field_simp
  · simp [cosMoment, h1]
  · simp only [cosMoment, h2]; field_simp
  · have := integral_cos_pow (a := 0) (b := 2 * π) (n := 1)
    simp only [cosMoment, Nat.reduceAdd] at this ⊢
    simp [h1] at this
    simp
  · have := integral_cos_pow (a := 0) (b := 2 * π) (n := 2)
    simp only [Nat.reduceAdd] at this
    simp [cosMoment, h2] at this ⊢
    rw [this]; field_simp; norm_num

/-- Average of a product of powers of cosines of distinct coordinates (powers at most `4`). -/
theorem angleAvg_prod_cos_pow (N : ℕ) (m : Fin N → ℕ) (hm : ∀ t, m t ≤ 4) :
    angleAvg N (fun φ => ∏ t, Real.cos (φ t) ^ m t) = ∏ t, cosMoment (m t) := by
  unfold angleAvg
  rw [integral_fintype_prod_eq_prod (μ := fun _ : Fin N => angleMeasure)
    (fun t x => Real.cos x ^ m t)]
  exact Finset.prod_congr rfl fun t _ => integral_angleMeasure_cos_pow _ (hm t)

/-- Multiplicity of the value `t` among four indices. -/
def idxCount {N : ℕ} (i j k l t : Fin N) : ℕ :=
  (if i = t then 1 else 0) + (if j = t then 1 else 0) + (if k = t then 1 else 0)
    + (if l = t then 1 else 0)

theorem cos_mul_four_eq_prod {N : ℕ} (i j k l : Fin N) (φ : Fin N → ℝ) :
    Real.cos (φ i) * Real.cos (φ j) * Real.cos (φ k) * Real.cos (φ l)
      = ∏ t, Real.cos (φ t) ^ idxCount i j k l t := by
  unfold idxCount
  simp only [pow_add, Finset.prod_mul_distrib, pow_ite, pow_one, pow_zero, Finset.prod_ite_eq,
    Finset.mem_univ, ite_true]

theorem idxCount_le {N : ℕ} (i j k l t : Fin N) : idxCount i j k l t ≤ 4 := by
  unfold idxCount
  split_ifs <;> omega

theorem prod_cosMoment_all {N : ℕ} (i : Fin N) :
    ∏ t, cosMoment (idxCount i i i i t) = 3 / 8 := by
  rw [Finset.prod_eq_single i]
  · simp [idxCount, cosMoment]
  · intro t _ ht
    simp [idxCount, Ne.symm ht, cosMoment]
  · simp

theorem prod_cosMoment_pair {N : ℕ} (i k : Fin N) (hik : i ≠ k) :
    ∏ t, cosMoment (idxCount i i k k t) = 1 / 4 := by
  rw [Finset.prod_eq_mul i k hik]
  · simp [idxCount, cosMoment, hik, Ne.symm hik]; norm_num
  · intro t _ ht
    simp [idxCount, Ne.symm ht.1, Ne.symm ht.2, cosMoment]
  · simp
  · simp

theorem prod_cosMoment_zero {N : ℕ} (i j k l t : Fin N)
    (h : idxCount i j k l t = 1 ∨ idxCount i j k l t = 3) :
    ∏ s, cosMoment (idxCount i j k l s) = 0 := by
  refine Finset.prod_eq_zero (Finset.mem_univ t) ?_
  rcases h with h | h <;> simp [h, cosMoment]

theorem prod_cosMoment_pair_a {N : ℕ} (a b : Fin N) (hab : a ≠ b) (c d e f : Fin N) (h1 : c = a)
    (h2 : d = a) (h3 : e = b) (h4 : f = b) :
    ∏ t, cosMoment (idxCount c d e f t) = 1 / 4 := by
  rw [h1, h2, h3, h4]; exact prod_cosMoment_pair a b hab

theorem prod_cosMoment_pair_b {N : ℕ} (a b : Fin N) (hab : a ≠ b) (c d e f : Fin N) (h1 : c = a)
    (h2 : d = b) (h3 : e = a) (h4 : f = b) :
    ∏ t, cosMoment (idxCount c d e f t) = 1 / 4 := by
  rw [← prod_cosMoment_pair a b hab]
  exact Finset.prod_congr rfl fun t _ => by
    rw [h1, h2, h3, h4]; unfold idxCount; congr 1; omega

theorem prod_cosMoment_pair_c {N : ℕ} (a b : Fin N) (hab : a ≠ b) (c d e f : Fin N) (h1 : c = a)
    (h2 : d = b) (h3 : e = b) (h4 : f = a) :
    ∏ t, cosMoment (idxCount c d e f t) = 1 / 4 := by
  rw [← prod_cosMoment_pair a b hab]
  exact Finset.prod_congr rfl fun t _ => by
    rw [h1, h2, h3, h4]; unfold idxCount; congr 1; omega

/-- The average of the product, as a product of moments, in closed form. -/
theorem prod_cosMoment_idxCount {N : ℕ} (i j k l : Fin N) :
    ∏ t, cosMoment (idxCount i j k l t) =
      (1 / 4) * ((if i = j ∧ k = l then 1 else 0) + (if i = k ∧ j = l then 1 else 0)
        + (if i = l ∧ j = k then 1 else 0)) - (3 / 8) * (if i = j ∧ j = k ∧ k = l then 1 else 0) :=
            by
  by_cases h1 : i = j
  · by_cases h2 : k = l
    · by_cases h3 : i = k
      · subst h1; subst h3; subst h2
        rw [prod_cosMoment_all]; norm_num
      · rw [prod_cosMoment_pair_a i k h3 i j k l rfl h1.symm rfl h2.symm]
        simp_all
    · rw [prod_cosMoment_zero i j k l (if k = i then l else k)]
      · split_ifs <;> grind
      · by_cases hki : k = i
        · left; unfold idxCount; split_ifs <;> grind
        · left; unfold idxCount; split_ifs <;> grind
  · by_cases h2 : k = i
    · by_cases h3 : l = j
      · rw [prod_cosMoment_pair_b i j h1 i j k l rfl rfl h2 h3]
        simp_all
      · rw [prod_cosMoment_zero i j k l (if l = i then i else j)]
        · split_ifs <;> grind
        · by_cases hli : l = i
          · right; unfold idxCount; split_ifs <;> grind
          · left; unfold idxCount; split_ifs <;> grind
    · by_cases h3 : k = j
      · by_cases h4 : l = i
        · rw [prod_cosMoment_pair_c i j h1 i j k l rfl rfl h3 h4]
          simp_all
        · by_cases h5 : l = j
          · rw [prod_cosMoment_zero i j k l j]
            · split_ifs <;> grind
            · right; unfold idxCount; split_ifs <;> grind
          · rw [prod_cosMoment_zero i j k l i]
            · split_ifs <;> grind
            · left; unfold idxCount; split_ifs <;> grind
      · by_cases h4 : l = k
        · rw [prod_cosMoment_zero i j k l i]
          · split_ifs <;> grind
          · left; unfold idxCount; split_ifs <;> grind
        · rw [prod_cosMoment_zero i j k l k]
          · split_ifs <;> grind
          · left; unfold idxCount; split_ifs <;> grind

/-- Four-fold product formula for the angle average (blueprint Step `stepW:w0n:moments`):
`E[cos φ_i cos φ_j cos φ_k cos φ_l] = ¼([i=j][k=l] + [i=k][j=l] + [i=l][j=k]) - ⅜[i=j=k=l]`. -/
theorem angleAvg_cos_four (N : ℕ) (i j k l : Fin N) :
    angleAvg N (fun φ => Real.cos (φ i) * Real.cos (φ j) * Real.cos (φ k) * Real.cos (φ l)) =
      (1 / 4) * ((if i = j ∧ k = l then 1 else 0) + (if i = k ∧ j = l then 1 else 0)
        + (if i = l ∧ j = k then 1 else 0)) - (3 / 8) * (if i = j ∧ j = k ∧ k = l then 1 else 0) :=
            by
  simp_rw [cos_mul_four_eq_prod]
  rw [angleAvg_prod_cos_pow N _ (fun t => idxCount_le i j k l t)]
  exact prod_cosMoment_idxCount i j k l

theorem integrable_cos_four (N : ℕ) (i j k l : Fin N) :
    Integrable (fun φ : Fin N → ℝ =>
      Real.cos (φ i) * Real.cos (φ j) * Real.cos (φ k) * Real.cos (φ l))
      (Measure.pi fun _ : Fin N => angleMeasure) := by
  refine Integrable.of_bound (by fun_prop) 1 (Filter.Eventually.of_forall fun φ => ?_)
  simp only [norm_mul, Real.norm_eq_abs]
  have h1 := Real.abs_cos_le_one (φ i)
  have h2 := Real.abs_cos_le_one (φ j)
  have h3 := Real.abs_cos_le_one (φ k)
  have h4 := Real.abs_cos_le_one (φ l)
  calc |Real.cos (φ i)| * |Real.cos (φ j)| * |Real.cos (φ k)| * |Real.cos (φ l)|
      ≤ 1 * 1 * 1 * 1 := by gcongr
    _ = 1 := by norm_num

/-- The angle average of a quadruple sum of constant multiples of products of four cosines. -/
theorem angleAvg_sum_cos_four (N : ℕ) (c : Fin N → Fin N → Fin N → Fin N → ℝ) :
    angleAvg N (fun φ => ∑ i, ∑ j, ∑ k, ∑ l,
        c i j k l * (Real.cos (φ i) * Real.cos (φ j) * Real.cos (φ k) * Real.cos (φ l))) =
      ∑ i, ∑ j, ∑ k, ∑ l, c i j k l *
        angleAvg N (fun φ => Real.cos (φ i) * Real.cos (φ j) * Real.cos (φ k) * Real.cos (φ l)) :=
            by
  unfold angleAvg
  have hI := integrable_cos_four N
  rw [integral_finsetSum _ fun i _ => ?_]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ fun j _ => ?_]
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [integral_finsetSum _ fun k _ => ?_]
      · refine Finset.sum_congr rfl fun k _ => ?_
        rw [integral_finsetSum _ fun l _ => (hI i j k l).const_mul (c i j k l)]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [integral_const_mul]
      · exact integrable_finsetSum _ fun l _ => (hI i j k l).const_mul (c i j k l)
    · exact integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ =>
        (hI i j k l).const_mul (c i j k l)
  · exact integrable_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ =>
      integrable_finsetSum _ fun l _ => (hI i j k l).const_mul (c i j k l)

end KAM.Wave

end
