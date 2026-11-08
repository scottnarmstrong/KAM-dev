/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The majorant sequence of the Lie series (blueprint-W `bpW:w3:leibniz`, norms)

Package W3-FLOW, blueprint label `bpW:w3:leibniz`.

`birkLieM` is defined by `m₀ = 1`, `(k+1) m_{k+1} = Σ_{a+b+c=k} m_a m_b m_c` (the coefficients
of the
solution of `y' = y³`, `y(0) = 1`, i.e. `(1 - 2x)^{-1/2}`). Then `0 ≤ m_k ≤ 2^k`
(`birkLieM_le_pow`):
the series `Y = Σ m_k Xᵏ` satisfies `Y' = Y³`, so `(Y²)' = 2 (Y²)²` and `Y² = Σ 2ᵏ Xᵏ`.
-/

@[expose] public noncomputable section

open PowerSeries Finset

namespace KAM.Wave

/-- `m₀ = 1`, `(k+1) m_{k+1} = Σ_{a+b+c=k} m_a m_b m_c` (nested antidiagonals). -/
def birkLieM : ℕ → ℝ
  | 0 => 1
  | n + 1 => (1 / ((n : ℝ) + 1)) * ∑ p ∈ (antidiagonal n).attach, birkLieM p.1.1 *
      ∑ q ∈ (antidiagonal p.1.2).attach, birkLieM q.1.1 * birkLieM q.1.2
decreasing_by
  · have := mem_antidiagonal.1 p.2; omega
  · have := mem_antidiagonal.1 p.2; have := mem_antidiagonal.1 q.2; omega
  · have := mem_antidiagonal.1 p.2; have := mem_antidiagonal.1 q.2; omega

theorem birkLieM_succ (n : ℕ) :
    birkLieM (n + 1) = (1 / ((n : ℝ) + 1)) * ∑ p ∈ antidiagonal n, birkLieM p.1 *
      ∑ q ∈ antidiagonal p.2, birkLieM q.1 * birkLieM q.2 := by
  rw [birkLieM]
  simp only [sum_attach (antidiagonal n) (fun p => birkLieM p.1 *
    ∑ q ∈ (antidiagonal p.2).attach, birkLieM q.1.1 * birkLieM q.1.2)]
  congr 1
  refine sum_congr rfl fun p _ => ?_
  rw [sum_attach (antidiagonal p.2) (fun q => birkLieM q.1 * birkLieM q.2)]

theorem sum_nested_antidiag {M : Type*} [AddCommMonoid M] (n : ℕ) (F : ℕ → ℕ → ℕ → M) :
    ∑ p ∈ antidiagonal n, ∑ q ∈ antidiagonal p.2, F p.1 q.1 q.2 =
      ∑ x ∈ Finset.Nat.antidiagonalTuple 3 n, F (x 0) (x 1) (x 2) := by
  rw [Finset.sum_sigma']
  refine Finset.sum_bij' (fun s _ => ![s.1.1, s.2.1, s.2.2])
    (fun x _ => ⟨(x 0, x 1 + x 2), (x 1, x 2)⟩) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨p, q⟩ hs
    simp only [mem_sigma, HasAntidiagonal.mem_antidiagonal] at hs
    simp [Finset.Nat.mem_antidiagonalTuple, Fin.sum_univ_three]
    omega
  · intro x hx
    simp only [Finset.Nat.mem_antidiagonalTuple, Fin.sum_univ_three] at hx
    simp only [mem_sigma, HasAntidiagonal.mem_antidiagonal]
    exact ⟨by omega, trivial⟩
  · rintro ⟨p, q⟩ hs
    simp only [mem_sigma, HasAntidiagonal.mem_antidiagonal] at hs
    ext <;> simp <;> omega
  · intro x hx
    ext i; fin_cases i <;> simp
  · rintro ⟨p, q⟩ hs
    simp

/-- The generating series `Y = Σ m_k Xᵏ`. -/
def birkLieY : PowerSeries ℝ := PowerSeries.mk birkLieM

theorem birkLieY_deriv : d⁄dX birkLieY = birkLieY * (birkLieY * birkLieY) := by
  ext n
  rw [coeff_derivative, coeff_mul]
  simp only [birkLieY, coeff_mk, coeff_mul]
  rw [birkLieM_succ]
  have : ((n : ℝ) + 1) ≠ 0 := by positivity
  push_cast
  field_simp

theorem birkLieM_succ' (n : ℕ) :
    ((n : ℝ) + 1) * birkLieM (n + 1) =
      ∑ x ∈ Finset.Nat.antidiagonalTuple 3 n, birkLieM (x 0) * birkLieM (x 1) * birkLieM (x 2) := by
  rw [birkLieM_succ, ← mul_assoc, mul_one_div_cancel (by positivity), one_mul,
    ← sum_nested_antidiag n (fun a b c => birkLieM a * birkLieM b * birkLieM c)]
  refine sum_congr rfl fun p _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun q _ => ?_
  ring

theorem birkLieM_nonneg (n : ℕ) : 0 ≤ birkLieM n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    cases n with
    | zero => simp [birkLieM]
    | succ n =>
      rw [birkLieM_succ]
      refine mul_nonneg (by positivity) (sum_nonneg fun p hp => mul_nonneg
        (ih _ (by have := mem_antidiagonal.1 hp; omega)) (sum_nonneg fun q hq => mul_nonneg
        (ih _ (by have := mem_antidiagonal.1 hp; have := mem_antidiagonal.1 hq; omega))
        (ih _ (by have := mem_antidiagonal.1 hp; have := mem_antidiagonal.1 hq; omega))))

theorem two_eq_C : (2 : PowerSeries ℝ) = C (2 : ℝ) := (map_ofNat C 2).symm

/-- Uniqueness for `W' = 2 W²` with prescribed constant term. -/
theorem ode_sq_unique (W Z : PowerSeries ℝ) (h0 : coeff 0 W = coeff 0 Z)
    (hW : d⁄dX W = 2 * (W * W)) (hZ : d⁄dX Z = 2 * (Z * Z)) : W = Z := by
  have key : ∀ n, coeff n W = coeff n Z := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      cases n with
      | zero => exact h0
      | succ n =>
        have h1 := congrArg (coeff n) hW
        have h2 := congrArg (coeff n) hZ
        rw [coeff_derivative, two_eq_C, coeff_C_mul, coeff_mul] at h1 h2
        have hs : ∑ p ∈ antidiagonal n, coeff p.1 W * coeff p.2 W =
            ∑ p ∈ antidiagonal n, coeff p.1 Z * coeff p.2 Z :=
          sum_congr rfl fun p hp => by
            have := mem_antidiagonal.1 hp
            rw [ih p.1 (by omega), ih p.2 (by omega)]
        rw [hs, ← h2] at h1
        have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
        exact mul_right_cancel₀ hn h1
  ext n
  exact key n

/-- `Y² = Σ 2ᵏ Xᵏ`. -/
theorem birkLieY_sq : birkLieY * birkLieY = PowerSeries.mk fun k => (2 : ℝ) ^ k := by
  refine ode_sq_unique _ _ ?_ ?_ ?_
  · simp [birkLieY, birkLieM, coeff_mul]
  · rw [Derivation.leibniz, birkLieY_deriv]
    simp only [smul_eq_mul]
    ring
  · ext n
    rw [coeff_derivative, two_eq_C, coeff_C_mul, coeff_mul]
    simp only [coeff_mk]
    have : ∀ p ∈ antidiagonal n, (2 : ℝ) ^ p.1 * 2 ^ p.2 = 2 ^ n := fun p hp => by
      rw [← pow_add, mem_antidiagonal.1 hp]
    rw [sum_congr rfl this]
    simp only [sum_const, Nat.card_antidiagonal, nsmul_eq_mul]
    push_cast
    ring

theorem birkLieM_le_pow (n : ℕ) : birkLieM n ≤ 2 ^ n := by
  have h := congrArg (coeff n) birkLieY_sq
  rw [coeff_mul, coeff_mk] at h
  simp only [birkLieY, coeff_mk] at h
  cases n with
  | zero => simp [birkLieM]
  | succ n =>
    have h0 : birkLieM 0 = 1 := by simp [birkLieM]
    have hmem : ((0, n + 1) : ℕ × ℕ) ∈ antidiagonal (n + 1) := by simp
    have hle : birkLieM 0 * birkLieM (n + 1) ≤
        ∑ p ∈ antidiagonal (n + 1), birkLieM p.1 * birkLieM p.2 :=
      single_le_sum (f := fun p : ℕ × ℕ => birkLieM p.1 * birkLieM p.2)
        (fun p _ => mul_nonneg (birkLieM_nonneg _) (birkLieM_nonneg _)) hmem
    rw [h, h0, one_mul] at hle
    have : (0 : ℝ) < 2 ^ n := by positivity
    calc birkLieM (n + 1) ≤ 2 ^ (n + 1) := hle
      _ = 2 ^ (n + 1) := rfl

end KAM.Wave

end
