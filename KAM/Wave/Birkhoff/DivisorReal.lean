/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Birkhoff.QuartBarAlg

/-!
# Real-variable facts for the divisor bound (blueprint-W `bpW:w3:divisor`)

Off-frontier, source-faithful infrastructure used by several nodes; the dependency graph is still
being built. Package W3-DIVISOR-F, blueprint label `bpW:w3:divisor`.

`birkL m k = √(k² + m)` for `k : ℕ` (`lam m hm j = birkL m j`). With `Δ(k) = L(k+1) - L(k)`:
`birkL_second_diff` (`L(k) + L(k+2) - 2 L(k+1) ≥ m / L(k+2)³`, exact formula, no calculus),
`birkDelta_mono` (`Δ` nondecreasing), `birkDelta_ge` (`Δ(a) ≥ a / L(a)`), and the increment bounds
`birkL_incr_ge`, `birkL_incr_mono`, `birkL_incr_sub`.
-/

@[expose] public noncomputable section

namespace KAM.Wave

variable (m : ℝ) (hm : 0 < m)

/-- `L(k) = √(k² + m)` for natural `k`. -/
def birkL (m : ℝ) (k : ℕ) : ℝ := Real.sqrt ((k : ℝ) ^ 2 + m)

include hm

theorem lam_eq_birkL (j : ℕ+) : lam m hm j = birkL m (j : ℕ) := by
  simp [lam, birkL]

theorem birkL_sq (k : ℕ) : birkL m k ^ 2 = (k : ℝ) ^ 2 + m := by
  unfold birkL; rw [Real.sq_sqrt (by have := sq_nonneg (k : ℝ); linarith)]

theorem birkL_pos (k : ℕ) : 0 < birkL m k := Real.sqrt_pos.2 (by have := sq_nonneg (k : ℝ); linarith)

theorem birkL_mono {k l : ℕ} (h : k ≤ l) : birkL m k ≤ birkL m l := by
  unfold birkL
  apply Real.sqrt_le_sqrt
  have : (k : ℝ) ≤ l := by exact_mod_cast h
  nlinarith [Nat.cast_nonneg (α := ℝ) k]

theorem birkL_gt_self (k : ℕ) : (k : ℝ) < birkL m k := by
  refine lt_of_pow_lt_pow_left₀ 2 (birkL_pos m hm k).le ?_
  rw [birkL_sq m hm]; linarith

theorem one_le_birkL {k : ℕ} (hk : 1 ≤ k) : 1 ≤ birkL m k := by
  have : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have h := birkL_gt_self m hm k
  linarith

/-- The second difference, exactly:
`(p + r - 2q)·(p + r + 2q)·(pr + q² - 1) = 8m` for `p = L(k), q = L(k+1), r = L(k+2)`. -/
theorem birkL_second_diff (k : ℕ) :
    m / birkL m (k + 2) ^ 3 ≤ birkL m k + birkL m (k + 2) - 2 * birkL m (k + 1) := by
  set p := birkL m k with hp
  set q := birkL m (k + 1) with hq
  set r := birkL m (k + 2) with hr
  have hp2 := birkL_sq m hm k
  have hq2 := birkL_sq m hm (k + 1)
  have hr2 := birkL_sq m hm (k + 2)
  push_cast at hq2 hr2
  have p0 := birkL_pos m hm k
  have q0 := birkL_pos m hm (k + 1)
  have r0 := birkL_pos m hm (k + 2)
  have hpq : p ≤ q := birkL_mono m hm (Nat.le_succ k)
  have hqr : q ≤ r := birkL_mono m hm (Nat.le_succ _)
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  -- X = p r
  have hX2 : (p * r) ^ 2 = (q ^ 2 - 1) ^ 2 + 4 * m := by
    rw [mul_pow, hp2, hr2, hq2]; ring
  have hsum : p ^ 2 + r ^ 2 = 2 * q ^ 2 + 2 := by rw [hp2, hr2, hq2]; ring
  have hXle : p * r ≤ q ^ 2 + 1 := by nlinarith [sq_nonneg (p - r)]
  have hq1 : 0 ≤ q ^ 2 - 1 := by rw [hq2]; nlinarith
  have hB : 0 < p * r + q ^ 2 - 1 := by nlinarith [mul_pos p0 r0]
  have h1 : (p * r - (q ^ 2 - 1)) * (p * r + (q ^ 2 - 1)) = 4 * m := by nlinarith [hX2]
  have h2 : (p + r - 2 * q) * (p + r + 2 * q) = 2 * (p * r - (q ^ 2 - 1)) := by nlinarith [hsum]
  have hA : 0 < p + r + 2 * q := by positivity
  have key : (p + r - 2 * q) * (p + r + 2 * q) * (p * r + (q ^ 2 - 1)) = 8 * m := by
    rw [h2]; nlinarith [h1]
  have hB' : 0 < p * r + (q ^ 2 - 1) := by linarith
  have hS : 0 < p + r - 2 * q := by
    by_contra h
    push Not at h
    have e : (p + r - 2 * q) * ((p + r + 2 * q) * (p * r + (q ^ 2 - 1))) = 8 * m := by
      rw [← key]; ring
    nlinarith [mul_nonpos_of_nonpos_of_nonneg h (mul_pos hA hB').le]
  have hA4 : p + r + 2 * q ≤ 4 * r := by linarith
  have hB2 : p * r + (q ^ 2 - 1) ≤ 2 * q ^ 2 := by linarith
  have : 8 * m ≤ (p + r - 2 * q) * (4 * r) * (2 * q ^ 2) := by
    rw [← key]
    have := mul_le_mul hA4 hB2 hB'.le (by positivity)
    nlinarith [mul_le_mul_of_nonneg_left this hS.le]
  rw [div_le_iff₀ (by positivity)]
  have hq3 : q ^ 2 ≤ r ^ 2 := by nlinarith
  nlinarith [mul_pos hS r0, mul_nonneg hS.le r0.le, mul_le_mul_of_nonneg_left hq3 (mul_pos hS r0).le]

/-- The increment `Δ(k) = L(k+1) - L(k)`. -/
def birkDelta (m : ℝ) (k : ℕ) : ℝ := birkL m (k + 1) - birkL m k

theorem birkDelta_mono : Monotone (birkDelta m) := by
  refine monotone_nat_of_le_succ fun k => ?_
  have h := birkL_second_diff m hm k
  have : 0 ≤ m / birkL m (k + 2) ^ 3 := by have := birkL_pos m hm (k + 2); positivity
  unfold birkDelta
  linarith

/-- `Δ(a) ≥ a / L(a)`. -/
theorem birkDelta_ge (a : ℕ) : (a : ℝ) / birkL m a ≤ birkDelta m a := by
  have h0 := birkL_pos m hm a
  have h1 := birkL_pos m hm (a + 1)
  rw [div_le_iff₀ h0]
  unfold birkDelta
  have hpr : (a : ℝ) ^ 2 + a + m ≤ birkL m a * birkL m (a + 1) := by
    have := birkL_sq m hm a
    have h2 := birkL_sq m hm (a + 1)
    push_cast at h2
    have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
    refine le_of_sq_le_sq ?_ (by positivity)
    rw [mul_pow, this, h2]
    nlinarith
  nlinarith [birkL_sq m hm a]

theorem birkL_add_ge (k j : ℕ) : (j : ℝ) * birkDelta m k ≤ birkL m (k + j) - birkL m k := by
  induction j with
  | zero => simp
  | succ j ih =>
    have := birkDelta_mono m hm (Nat.le_add_right k j)
    have e : birkL m (k + (j + 1)) - birkL m (k + j) = birkDelta m (k + j) := by
      unfold birkDelta; rw [← add_assoc]
    push_cast
    nlinarith

theorem birkL_incr_mono {a c : ℕ} (h : a ≤ c) (j : ℕ) :
    birkL m (a + j) - birkL m a ≤ birkL m (c + j) - birkL m c := by
  induction j with
  | zero => simp
  | succ j ih =>
    have := birkDelta_mono m hm (Nat.add_le_add_right h j)
    have e1 : birkL m (a + (j + 1)) - birkL m (a + j) = birkDelta m (a + j) := by
      unfold birkDelta; rw [← add_assoc]
    have e2 : birkL m (c + (j + 1)) - birkL m (c + j) = birkDelta m (c + j) := by
      unfold birkDelta; rw [← add_assoc]
    linarith

/-- `L(c+t) - L(c) - (L(a+t) - L(a)) ≥ Δ(c) - Δ(a)` for `c ≥ a`, `t ≥ 1`. -/
theorem birkL_incr_sub {a c : ℕ} (h : a ≤ c) (t : ℕ) (ht : 1 ≤ t) :
    birkDelta m c - birkDelta m a ≤
      (birkL m (c + t) - birkL m c) - (birkL m (a + t) - birkL m a) := by
  induction t, ht using Nat.le_induction with
  | base => unfold birkDelta; simp
  | succ t ht ih =>
    have := birkDelta_mono m hm (Nat.add_le_add_right h t)
    have e1 : birkL m (a + (t + 1)) - birkL m (a + t) = birkDelta m (a + t) := by
      unfold birkDelta; rw [← add_assoc]
    have e2 : birkL m (c + (t + 1)) - birkL m (c + t) = birkDelta m (c + t) := by
      unfold birkDelta; rw [← add_assoc]
    linarith

end KAM.Wave

end
