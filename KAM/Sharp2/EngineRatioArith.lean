/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The arithmetic of the engine with ratio `a` and decay bound `ȳ`

The generalisation of `KAM/Sharp2/EngineArith.lean` (`a = 2`, `ȳ = 1/2`): the normalised errors
`X_{s+1} = a^p Q_s X_s²`, the tail decay `X_s ≤ X_k ȳ^{s-k}` from `a^p Q_∞ X_k ≤ ȳ`, and the
critical sums `∑_{t<n} a_t X_t ≤ ∑_{t<k} a_t X_t + A X_k/(1-ȳ)`. Pure real arithmetic.
-/

@[expose] public noncomputable section

namespace KAM.Sharp2

/-- `X_{s+1} = a^p Q_s X_s²`. -/
def xSeqR (a p : ℝ) (Q : ℕ → ℝ) (X0 : ℝ) : ℕ → ℝ
  | 0 => X0
  | s + 1 => a ^ p * Q s * xSeqR a p Q X0 s ^ 2

theorem xSeqR_nonneg {a p : ℝ} {Q : ℕ → ℝ} {X0 : ℝ} (ha : 0 < a) (hQ : ∀ s, 0 ≤ Q s)
    (hX0 : 0 ≤ X0) (s : ℕ) : 0 ≤ xSeqR a p Q X0 s := by
  induction s with
  | zero => exact hX0
  | succ s ih =>
    simp only [xSeqR]
    have := Real.rpow_nonneg ha.le p
    have := hQ s
    positivity

/-- The tail decay `X_s ≤ X_k ȳ^{s-k}`. -/
theorem xSeqR_tail {a p : ℝ} {Q : ℕ → ℝ} {X0 Qt ybar : ℝ} {k : ℕ} (ha : 0 < a)
    (hy0 : 0 ≤ ybar) (hy1 : ybar ≤ 1) (hQ : ∀ s, 0 ≤ Q s)
    (hX0 : 0 ≤ X0) (hQt : ∀ s, k ≤ s → Q s ≤ Qt)
    (hJ2 : a ^ p * Qt * xSeqR a p Q X0 k ≤ ybar) :
    ∀ s, k ≤ s → xSeqR a p Q X0 s ≤ xSeqR a p Q X0 k * ybar ^ (s - k) := by
  intro s hs
  induction s, hs using Nat.le_induction with
  | base => simp
  | succ s hks ih =>
    have hXs := xSeqR_nonneg (p := p) ha hQ hX0 s
    have hXk := xSeqR_nonneg (p := p) ha hQ hX0 k
    have h2 : (0 : ℝ) ≤ a ^ p := Real.rpow_nonneg ha.le _
    have hQt0 : 0 ≤ Qt := (hQ k).trans (hQt k le_rfl)
    have hZ : a ^ p * Qt * xSeqR a p Q X0 s ≤ ybar := by
      have : xSeqR a p Q X0 s ≤ xSeqR a p Q X0 k :=
        ih.trans (mul_le_of_le_one_right hXk (pow_le_one₀ hy0 hy1))
      calc _ ≤ a ^ p * Qt * xSeqR a p Q X0 k :=
            mul_le_mul_of_nonneg_left this (by positivity)
        _ ≤ ybar := hJ2
    have hstep : xSeqR a p Q X0 (s + 1) ≤ a ^ p * Qt * xSeqR a p Q X0 s ^ 2 := by
      simp only [xSeqR]
      have := hQt s hks
      have : a ^ p * Q s ≤ a ^ p * Qt := mul_le_mul_of_nonneg_left this h2
      nlinarith [sq_nonneg (xSeqR a p Q X0 s)]
    have hy : xSeqR a p Q X0 (s + 1) ≤ ybar * xSeqR a p Q X0 s := by
      calc _ ≤ (a ^ p * Qt * xSeqR a p Q X0 s) * xSeqR a p Q X0 s := by nlinarith
        _ ≤ ybar * xSeqR a p Q X0 s := mul_le_mul_of_nonneg_right hZ hXs
    calc xSeqR a p Q X0 (s + 1) ≤ ybar * xSeqR a p Q X0 s := hy
      _ ≤ ybar * (xSeqR a p Q X0 k * ybar ^ (s - k)) := by gcongr
      _ = xSeqR a p Q X0 k * ybar ^ (s + 1 - k) := by
        rw [show s + 1 - k = (s - k) + 1 by omega, pow_succ]; ring

/-- The critical sums: `∑_{t<n} a_t X_t ≤ ∑_{t<k} a_t X_t + A X_k/(1-ȳ)`. -/
theorem partial_sum_leR {a X : ℕ → ℝ} {A ybar : ℝ} {k : ℕ} (n : ℕ) (hy0 : 0 ≤ ybar)
    (hy1 : ybar < 1) (ha0 : ∀ t, 0 ≤ a t)
    (hX0 : ∀ t, 0 ≤ X t) (hXd : ∀ t, k ≤ t → X t ≤ X k * ybar ^ (t - k))
    (haA : ∀ t, k ≤ t → a t ≤ A) :
    ∑ t ∈ Finset.range n, a t * X t ≤
      ∑ t ∈ Finset.range k, a t * X t + A * X k / (1 - ybar) := by
  have hA0 : 0 ≤ A := (ha0 k).trans (haA k le_rfl)
  have hXk := hX0 k
  have h1y : 0 < 1 - ybar := by linarith
  have hnn : 0 ≤ A * X k / (1 - ybar) := by positivity
  by_cases hn : n ≤ k
  · have h1 : ∑ t ∈ Finset.range n, a t * X t ≤ ∑ t ∈ Finset.range k, a t * X t :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hn)
        (fun t _ _ => mul_nonneg (ha0 t) (hX0 t))
    linarith
  · have hn := not_le.mp hn
    rw [← Finset.sum_range_add_sum_Ico _ hn.le]
    have hI : ∑ t ∈ Finset.Ico k n, a t * X t ≤ A * X k / (1 - ybar) := by
      rw [Finset.sum_Ico_eq_sum_range]
      calc ∑ j ∈ Finset.range (n - k), a (k + j) * X (k + j)
          ≤ ∑ j ∈ Finset.range (n - k), A * X k * ybar ^ j := by
            refine Finset.sum_le_sum fun j _ => ?_
            have h1 := hXd (k + j) (by omega)
            rw [show k + j - k = j by omega] at h1
            have h2 : a (k + j) * X (k + j) ≤ A * X (k + j) :=
              mul_le_mul_of_nonneg_right (haA _ (by omega)) (hX0 _)
            calc a (k + j) * X (k + j) ≤ A * X (k + j) := h2
              _ ≤ A * (X k * ybar ^ j) := mul_le_mul_of_nonneg_left h1 hA0
              _ = A * X k * ybar ^ j := by ring
        _ = A * X k * ∑ j ∈ Finset.range (n - k), ybar ^ j := by rw [Finset.mul_sum]
        _ ≤ A * X k * (1 - ybar)⁻¹ := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            rw [← tsum_geometric_of_lt_one hy0 hy1]
            exact (summable_geometric_of_lt_one hy0 hy1).sum_le_tsum _
              (fun j _ => pow_nonneg hy0 j)
        _ = A * X k / (1 - ybar) := by rw [div_eq_mul_inv]
    linarith

/-- Summability of `a_t X_t` under the same hypotheses. -/
theorem summable_mul_decayR {a X : ℕ → ℝ} {A ybar : ℝ} {k : ℕ} (hy0 : 0 ≤ ybar)
    (hy1 : ybar < 1) (ha0 : ∀ t, 0 ≤ a t)
    (hX0 : ∀ t, 0 ≤ X t) (hXd : ∀ t, k ≤ t → X t ≤ X k * ybar ^ (t - k))
    (haA : ∀ t, k ≤ t → a t ≤ A) : Summable fun t => a t * X t := by
  have hA0 : 0 ≤ A := (ha0 k).trans (haA k le_rfl)
  rw [← summable_nat_add_iff k]
  refine Summable.of_nonneg_of_le (fun j => mul_nonneg (ha0 _) (hX0 _)) (fun j => ?_)
    ((summable_geometric_of_lt_one hy0 hy1).mul_left (A * X k))
  have h1 := hXd (j + k) (by omega)
  rw [show j + k - k = j by omega] at h1
  calc a (j + k) * X (j + k) ≤ A * X (j + k) :=
        mul_le_mul_of_nonneg_right (haA _ (by omega)) (hX0 _)
    _ ≤ A * (X k * ybar ^ j) := mul_le_mul_of_nonneg_left h1 hA0
    _ = A * X k * ybar ^ j := by ring

end KAM.Sharp2

end
