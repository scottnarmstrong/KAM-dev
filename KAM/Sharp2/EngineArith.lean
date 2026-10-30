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
# The arithmetic of the stage-dependent engine (`bp:p2s2:engine`)

The normalised errors `X_{s+1} = 2^{κ+1} Q_s X_s²` of the prefix and the tail
(`bp:p2s2:engine`, steps `step:p2s2:en-pre`, `step:p2s2:en-tail`): nonnegativity, the tail decay
`X_s ≤ X_k / 2^{s-k}` from `2^{κ+1} Q_∞ X_k ≤ 1/2`, and the critical sums
`∑_{t<n} a_t X_t ≤ ∑_{t<k} a_t X_t + 2 A X_k`. Pure real arithmetic, no scheme.
-/

@[expose] public noncomputable section

namespace KAM.Sharp2

/-- The normalised errors of the prefix: `X_{s+1} = 2^{κ+1} Q_s X_s²`. -/
def xSeq (κ : ℝ) (Q : ℕ → ℝ) (X0 : ℝ) : ℕ → ℝ
  | 0 => X0
  | s + 1 => 2 ^ (κ + 1) * Q s * xSeq κ Q X0 s ^ 2

theorem xSeq_nonneg {κ : ℝ} {Q : ℕ → ℝ} {X0 : ℝ} (hQ : ∀ s, 0 ≤ Q s) (hX0 : 0 ≤ X0) (s : ℕ) :
    0 ≤ xSeq κ Q X0 s := by
  induction s with
  | zero => exact hX0
  | succ s ih =>
    simp only [xSeq]
    have := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (κ + 1)
    have := hQ s
    positivity

/-- The tail decay `X_s ≤ X_k/2^{s-k}` (`step:p2s2:en-tail`). -/
theorem xSeq_tail {κ : ℝ} {Q : ℕ → ℝ} {X0 Qt : ℝ} {k : ℕ} (hQ : ∀ s, 0 ≤ Q s)
    (hX0 : 0 ≤ X0) (hQt : ∀ s, k ≤ s → Q s ≤ Qt)
    (hJ2 : 2 ^ (κ + 1) * Qt * xSeq κ Q X0 k ≤ 1 / 2) :
    ∀ s, k ≤ s → xSeq κ Q X0 s ≤ xSeq κ Q X0 k / 2 ^ (s - k) := by
  intro s hs
  induction s, hs using Nat.le_induction with
  | base => simp
  | succ s hks ih =>
    have hXs := xSeq_nonneg (κ := κ) hQ hX0 s
    have hXk := xSeq_nonneg (κ := κ) hQ hX0 k
    have h2 : (0 : ℝ) ≤ 2 ^ (κ + 1) := Real.rpow_nonneg (by norm_num) _
    have hQt0 : 0 ≤ Qt := (hQ k).trans (hQt k le_rfl)
    -- `Z_s = 2^{κ+1} Qt X_s ≤ 1/2`
    have hZ : 2 ^ (κ + 1) * Qt * xSeq κ Q X0 s ≤ 1 / 2 := by
      have : xSeq κ Q X0 s ≤ xSeq κ Q X0 k := ih.trans (div_le_self hXk (one_le_pow₀ (by norm_num)))
      calc _ ≤ 2 ^ (κ + 1) * Qt * xSeq κ Q X0 k :=
            mul_le_mul_of_nonneg_left this (by positivity)
        _ ≤ 1 / 2 := hJ2
    have hstep : xSeq κ Q X0 (s + 1) ≤ 2 ^ (κ + 1) * Qt * xSeq κ Q X0 s ^ 2 := by
      simp only [xSeq]
      have := hQt s hks
      have : 2 ^ (κ + 1) * Q s ≤ 2 ^ (κ + 1) * Qt := mul_le_mul_of_nonneg_left this h2
      nlinarith [sq_nonneg (xSeq κ Q X0 s)]
    have hhalf : xSeq κ Q X0 (s + 1) ≤ xSeq κ Q X0 s / 2 := by
      calc _ ≤ (2 ^ (κ + 1) * Qt * xSeq κ Q X0 s) * xSeq κ Q X0 s := by nlinarith
        _ ≤ 1 / 2 * xSeq κ Q X0 s := mul_le_mul_of_nonneg_right hZ hXs
        _ = _ := by ring
    calc xSeq κ Q X0 (s + 1) ≤ xSeq κ Q X0 s / 2 := hhalf
      _ ≤ xSeq κ Q X0 k / 2 ^ (s - k) / 2 := by gcongr
      _ = xSeq κ Q X0 k / 2 ^ (s + 1 - k) := by
        rw [show s + 1 - k = (s - k) + 1 by omega, pow_succ]; ring

/-- The critical sums: `∑_{t<n} a_t X_t ≤ ∑_{t<k} a_t X_t + 2 A X_k` for `0 ≤ a_t ≤ A` (`t ≥ k`)
and `X_t ≥ 0`, `X_t ≤ X_k/2^{t-k}` (`t ≥ k`). -/
theorem partial_sum_le {a X : ℕ → ℝ} {A : ℝ} {k : ℕ} (n : ℕ) (ha0 : ∀ t, 0 ≤ a t)
    (hX0 : ∀ t, 0 ≤ X t) (hXd : ∀ t, k ≤ t → X t ≤ X k / 2 ^ (t - k))
    (haA : ∀ t, k ≤ t → a t ≤ A) :
    ∑ t ∈ Finset.range n, a t * X t ≤ ∑ t ∈ Finset.range k, a t * X t + 2 * A * X k := by
  have hA0 : 0 ≤ A := (ha0 k).trans (haA k le_rfl)
  have hXk := hX0 k
  by_cases hn : n ≤ k
  · have h1 : ∑ t ∈ Finset.range n, a t * X t ≤ ∑ t ∈ Finset.range k, a t * X t :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hn)
        (fun t _ _ => mul_nonneg (ha0 t) (hX0 t))
    have : 0 ≤ 2 * A * X k := by positivity
    linarith
  · have hn := not_le.mp hn
    rw [← Finset.sum_range_add_sum_Ico _ hn.le]
    have hI : ∑ t ∈ Finset.Ico k n, a t * X t ≤ 2 * A * X k := by
      rw [Finset.sum_Ico_eq_sum_range]
      calc ∑ j ∈ Finset.range (n - k), a (k + j) * X (k + j)
          ≤ ∑ j ∈ Finset.range (n - k), A * X k * (1 / 2) ^ j := by
            refine Finset.sum_le_sum fun j _ => ?_
            have h1 := hXd (k + j) (by omega)
            rw [show k + j - k = j by omega] at h1
            have h2 : a (k + j) * X (k + j) ≤ A * X (k + j) :=
              mul_le_mul_of_nonneg_right (haA _ (by omega)) (hX0 _)
            calc a (k + j) * X (k + j) ≤ A * X (k + j) := h2
              _ ≤ A * (X k / 2 ^ j) := mul_le_mul_of_nonneg_left h1 hA0
              _ = A * X k * (1 / 2) ^ j := by rw [one_div, inv_pow]; ring
        _ = A * X k * ∑ j ∈ Finset.range (n - k), (1 / 2 : ℝ) ^ j := by rw [Finset.mul_sum]
        _ ≤ A * X k * 2 := mul_le_mul_of_nonneg_left (sum_geometric_two_le _) (by positivity)
        _ = 2 * A * X k := by ring
    linarith

/-- Summability of `a_t X_t` under the same hypotheses. -/
theorem summable_mul_decay {a X : ℕ → ℝ} {A : ℝ} {k : ℕ} (ha0 : ∀ t, 0 ≤ a t)
    (hX0 : ∀ t, 0 ≤ X t) (hXd : ∀ t, k ≤ t → X t ≤ X k / 2 ^ (t - k))
    (haA : ∀ t, k ≤ t → a t ≤ A) : Summable fun t => a t * X t := by
  have hA0 : 0 ≤ A := (ha0 k).trans (haA k le_rfl)
  rw [← summable_nat_add_iff k]
  refine Summable.of_nonneg_of_le (fun j => mul_nonneg (ha0 _) (hX0 _)) (fun j => ?_)
    (summable_geometric_two.mul_left (A * X k))
  have h1 := hXd (j + k) (by omega)
  rw [show j + k - k = j by omega] at h1
  calc a (j + k) * X (j + k) ≤ A * X (j + k) :=
        mul_le_mul_of_nonneg_right (haA _ (by omega)) (hX0 _)
    _ ≤ A * (X k / 2 ^ j) := mul_le_mul_of_nonneg_left h1 hA0
    _ = A * X k * (1 / 2) ^ j := by rw [one_div, inv_pow]; ring

end KAM.Sharp2

end
