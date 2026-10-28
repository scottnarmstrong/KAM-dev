/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PlanarTorsion.AsymptoticEntries.Calculus

/-!
# Planar quartic torsion: leading terms of the pair coefficients (P11C, package T18)

Blueprint P, Part 11b (`bpP:p11b:asymptotics`, steps `as-in`, `as-c`): each pair coefficient
`A, B, p₁, …, p₆` equals its leading monomial up to a relative `O(a ^ 2)` error as `a → 0⁺`
(`p11cAe_A` … `p11cAe_p6`), and the Laplace coefficients `b_{3/2}^{(1)}, b_{3/2}^{(2)}` have the
leading terms `3 a / 2` and `15 a ^ 2 / 8` (`p11cAe_b1`, `p11cAe_b2`).
-/

@[expose] public noncomputable section
open Set Filter Asymptotics Real
open scoped Topology
namespace KAM.Planetary

theorem p11cAe_npow_le {m n : ℕ} (h : n ≤ m) :
    (fun a : ℝ => a ^ m) =O[𝓝[>] 0] fun a : ℝ => a ^ n := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1)] with a ha
  rw [Real.norm_of_nonneg (pow_nonneg ha.1.le _), Real.norm_of_nonneg (pow_nonneg ha.1.le _),
    one_mul]
  exact pow_le_pow_of_le_one ha.1.le ha.2.le h

/-- A pair coefficient is its leading monomial up to `O(a ^ (n + 2))`. -/
theorem p11cAe_pair_lead (i : Fin 8) (c : ℝ) (n m : ℕ) (hm : m = n + 2) (hm7 : m ≤ 7)
    (h : ℝ → ℝ) (hh : AnalyticAt ℝ h 0)
    (hj : ∀ a, p11c_pairSeriesJet a i = c * a ^ n + a ^ m * h a) :
    (fun a => p11c_pairCoeffs a i - c * a ^ n) =O[𝓝[>] 0] fun a : ℝ => a ^ (m : ℝ) := by
  rw [← p11cAe_natPow m]
  have h1 := (p11cAe_pair i).trans (p11cAe_npow_le hm7)
  have h2 := p11cAe_pow_mul_isBigO (m := m) hh
  refine (h1.add h2).congr_left fun a => ?_
  rw [hj a]; ring

theorem p11cAe_A : (fun a => p11c_pairCoeffs a 0 - 3 / 8 * a ^ 2) =O[𝓝[>] 0]
    fun a : ℝ => a ^ (4 : ℝ) := by
  simpa using p11cAe_pair_lead 0 (3 / 8) 2 4 rfl (by norm_num)
    (fun a => 45 / 64 + 525 / 512 * a ^ 2) (by fun_prop)
    (fun a => by simp [p11c_pairSeriesJet]; ring)

theorem p11cAe_B : (fun a => p11c_pairCoeffs a 1 + 15 / 16 * a ^ 3) =O[𝓝[>] 0]
    fun a : ℝ => a ^ (5 : ℝ) := by
  have := p11cAe_pair_lead 1 (-15 / 16) 3 5 rfl (by norm_num)
    (fun a => -105 / 64 - 4725 / 2048 * a ^ 2) (by fun_prop)
    (fun a => by simp [p11c_pairSeriesJet]; ring)
  simpa [sub_eq_add_neg, neg_div] using this

theorem p11cAe_p1 : (fun a => p11c_pairCoeffs a 2 - 135 / 512 * a ^ 4) =O[𝓝[>] 0]
    fun a : ℝ => a ^ (6 : ℝ) := by
  simpa using p11cAe_pair_lead 2 (135 / 512) 4 6 rfl (by norm_num)
    (fun _ => 2625 / 2048) (by fun_prop)
    (fun a => by simp [p11c_pairSeriesJet]; ring)

theorem p11cAe_p2 : (fun a => p11c_pairCoeffs a 3 - 15 / 32 * a ^ 2) =O[𝓝[>] 0]
    fun a : ℝ => a ^ (4 : ℝ) := by
  simpa using p11cAe_pair_lead 3 (15 / 32) 2 4 rfl (by norm_num)
    (fun a => 945 / 512 + 4725 / 1024 * a ^ 2) (by fun_prop)
    (fun a => by simp [p11c_pairSeriesJet]; ring)

theorem p11cAe_p3 : (fun a => p11c_pairCoeffs a 4 - 9 / 16 * a ^ 2) =O[𝓝[>] 0]
    fun a : ℝ => a ^ (4 : ℝ) := by
  simpa using p11cAe_pair_lead 4 (9 / 16) 2 4 rfl (by norm_num)
    (fun a => 585 / 256 + 1575 / 256 * a ^ 2) (by fun_prop)
    (fun a => by simp [p11c_pairSeriesJet]; ring)

theorem p11cAe_p4 : (fun a => p11c_pairCoeffs a 5 - 315 / 128 * a ^ 4) =O[𝓝[>] 0]
    fun a : ℝ => a ^ (6 : ℝ) := by
  simpa using p11cAe_pair_lead 5 (315 / 128) 4 6 rfl (by norm_num)
    (fun _ => 4725 / 512) (by fun_prop)
    (fun a => by simp [p11c_pairSeriesJet]; ring)

theorem p11cAe_p5 : (fun a => p11c_pairCoeffs a 6 + 45 / 64 * a ^ 3) =O[𝓝[>] 0]
    fun a : ℝ => a ^ (5 : ℝ) := by
  have := p11cAe_pair_lead 6 (-45 / 64) 3 5 rfl (by norm_num)
    (fun _ => -525 / 128) (by fun_prop)
    (fun a => by simp [p11c_pairSeriesJet]; ring)
  simpa [sub_eq_add_neg, neg_div] using this

theorem p11cAe_p6 : (fun a => p11c_pairCoeffs a 7 + 75 / 32 * a ^ 3) =O[𝓝[>] 0]
    fun a : ℝ => a ^ (5 : ℝ) := by
  have := p11cAe_pair_lead 7 (-75 / 32) 3 5 rfl (by norm_num)
    (fun _ => -2205 / 256) (by fun_prop)
    (fun a => by simp [p11c_pairSeriesJet]; ring)
  simpa [sub_eq_add_neg, neg_div] using this

/-- `b_{3/2}^{(1)}(a) = 3 a / 2 + O(a ^ 3)`. -/
theorem p11cAe_b1 : (fun a => p11c_laplace (3 / 2) 1 a - 3 / 2 * a) =O[𝓝[>] 0]
    fun a : ℝ => a ^ (3 : ℝ) := by
  have h := (p11cAe_div (f := fun a => p11c_pairCoeffs a 0 - 3 / 8 * a ^ 2) (r := 3)
    (by rw [show (3 : ℝ) + 1 = 4 by norm_num]; exact p11cAe_A)).const_mul_left 4
  refine h.congr' ?_ EventuallyEq.rfl
  filter_upwards [p11cAe_pos, p11cAe_lt_one] with a h0 h1
  have := (pair_quadratic_consistency a ⟨h0, h1⟩).1
  simp only [this]
  field_simp
  ring

/-- `b_{3/2}^{(2)}(a) = 15 a ^ 2 / 8 + O(a ^ 4)`. -/
theorem p11cAe_b2 : (fun a => p11c_laplace (3 / 2) 2 a - 15 / 8 * a ^ 2) =O[𝓝[>] 0]
    fun a : ℝ => a ^ (4 : ℝ) := by
  have h := (p11cAe_div (f := fun a => p11c_pairCoeffs a 1 + 15 / 16 * a ^ 3) (r := 4)
    (by rw [show (4 : ℝ) + 1 = 5 by norm_num]; exact p11cAe_B)).const_mul_left (-2)
  refine h.congr' ?_ EventuallyEq.rfl
  filter_upwards [p11cAe_pos, p11cAe_lt_one] with a h0 h1
  have := (pair_quadratic_consistency a ⟨h0, h1⟩).2
  simp only [this]
  field_simp
  ring

end KAM.Planetary

end
