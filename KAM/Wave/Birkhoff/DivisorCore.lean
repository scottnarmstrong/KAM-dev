/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Birkhoff.DivisorReal

/-!
# The divisor bound for sorted quadruples (blueprint-W `bpW:w3:divisor`, Steps 3-6)

Package W3-DIVISOR-F, blueprint label `bpW:w3:divisor`.

For naturals `1 ≤ a ≤ b ≤ c ≤ d` and `β = m/(27 L(a)³)`: no minus sign (`birkDiv_C0`),
one minus sign
(`birkDiv_C1`, needs `d ≤ a+b+c`), two minus signs, outer pairs (`birkDiv_C3`), `δ₂` (`birkDiv_C2`),
inner pair `δ₁` with `d + a = b + c` (`birkDiv_C1i`) and with `d = a + b + c` (`birkDiv_C1ii`).
-/

@[expose] public noncomputable section

namespace KAM.Wave

variable (m : ℝ) (hm : 0 < m)

include hm

theorem birkL_sub_self (k : ℕ) : birkL m k = k + m / (birkL m k + k) := by
  have h := birkL_sq m hm k
  have h0 := birkL_pos m hm k
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  field_simp
  nlinarith

/-- `β ≤ m/(2 L(a))`. -/
theorem birkBeta_le_half {a : ℕ} (ha : 1 ≤ a) :
    m / (27 * birkL m a ^ 3) ≤ m / (2 * birkL m a) := by
  have h1 := one_le_birkL m hm ha
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hL : birkL m a ≤ birkL m a ^ 3 := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ birkL m a) (by nlinarith : (0 : ℝ) ≤ birkL m a ^
        2 - 1)]
  have key : 2 * birkL m a ≤ 27 * birkL m a ^ 3 := by linarith
  nlinarith [mul_le_mul_of_nonneg_left key hm.le]

/-- `β ≤ a / L(a)`. -/
theorem birkBeta_le_ratio {a : ℕ} (ha : 1 ≤ a) :
    m / (27 * birkL m a ^ 3) ≤ (a : ℝ) / birkL m a := by
  have h0 := birkL_pos m hm a
  have h2 := birkL_sq m hm a
  have h1 : (1 : ℝ) ≤ a := by exact_mod_cast ha
  rw [div_le_div_iff₀ (by positivity) h0]
  have : m ≤ birkL m a ^ 2 := by rw [h2]; nlinarith
  nlinarith [mul_pos h0 h0, mul_nonneg (sq_nonneg (birkL m a)) (sub_nonneg.2 h1)]

theorem birkDiv_C0 {a b c d : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) (hd : 1 ≤ d) :
    m / (27 * birkL m a ^ 3) ≤ birkL m a + birkL m b + birkL m c + birkL m d := by
  have h1 := one_le_birkL m hm ha
  have h2 := one_le_birkL m hm hb
  have h3 := one_le_birkL m hm hc
  have h4 := one_le_birkL m hm hd
  have := birkBeta_le_ratio m hm ha
  have h5 : (a : ℝ) / birkL m a ≤ birkL m a := by
    rw [div_le_iff₀ (birkL_pos m hm a)]
    have h1 : (1 : ℝ) ≤ a := by exact_mod_cast ha
    nlinarith [birkL_sq m hm a, sq_nonneg (a : ℝ)]
  linarith

theorem birkDiv_C1 {a b c d : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d)
    (hd : d ≤ a + b + c) :
    m / (27 * birkL m a ^ 3) ≤ birkL m a + birkL m b + birkL m c - birkL m d := by
  have hbeta := birkBeta_le_half m hm ha
  have ea := birkL_sub_self m hm a
  have eb := birkL_sub_self m hm b
  have ec := birkL_sub_self m hm c
  have ed := birkL_sub_self m hm d
  have pa := birkL_pos m hm a
  have pb := birkL_pos m hm b
  have pc := birkL_pos m hm c
  have pd := birkL_pos m hm d
  have ga := birkL_gt_self m hm a
  have gb := birkL_gt_self m hm b
  have gc := birkL_gt_self m hm c
  have gd := birkL_gt_self m hm d
  have hd' : (d : ℝ) ≤ a + b + c := by exact_mod_cast hd
  have hcd' : birkL m c + c ≤ birkL m d + d := by
    have := birkL_mono m hm hcd
    have : (c : ℝ) ≤ d := by exact_mod_cast hcd
    linarith
  have hinv : m / (birkL m d + d) ≤ m / (birkL m c + c) :=
    div_le_div_of_nonneg_left hm.le (by linarith) hcd'
  have hb0 : 0 ≤ m / (birkL m b + b) := by positivity
  have hmain : m / (birkL m a + a) ≤ m / (birkL m a + a) := le_rfl
  have hhalf : m / (2 * birkL m a) ≤ m / (birkL m a + a) :=
    div_le_div_of_nonneg_left hm.le (by linarith) (by linarith)
  linarith

theorem birkDelta_pos {a : ℕ} (ha : 1 ≤ a) : 0 < birkDelta m a := by
  have h := birkDelta_ge m hm a
  have : (0 : ℝ) < a / birkL m a := by
    have : (0 : ℝ) < a := by exact_mod_cast ha
    exact div_pos this (birkL_pos m hm a)
  linarith

theorem birkL_step {a c : ℕ} (h : a ≤ c) :
    ((c : ℝ) - a) * birkDelta m a ≤ birkL m c - birkL m a := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
  have := birkL_add_ge m hm a j
  push_cast
  simpa using this

theorem birkDelta_ge_beta {a : ℕ} (ha : 1 ≤ a) :
    m / (27 * birkL m a ^ 3) ≤ birkDelta m a :=
  (birkBeta_le_ratio m hm ha).trans (birkDelta_ge m hm a)

/-- Outer pairs: `δ₃ = L c + L d - L a - L b ≥ β` unless `a = b = c = d`. -/
theorem birkDiv_C3 {a b c d : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d)
    (hne : ¬ (a = b ∧ b = c ∧ c = d)) :
    m / (27 * birkL m a ^ 3) ≤ birkL m c + birkL m d - birkL m a - birkL m b := by
  have s1 := birkL_step m hm (hab.trans hbc)
  have s2 := birkL_step m hm (hbc.trans hcd)
  have m1 := birkDelta_mono m hm hab
  have dp := birkDelta_pos m hm ha
  have hb := birkDelta_ge_beta m hm ha
  have hn : a + b + 1 ≤ c + d := by omega
  have hn' : (1 : ℝ) ≤ ((c : ℝ) - a) + ((d : ℝ) - b) := by
    have : ((a + b + 1 : ℕ) : ℝ) ≤ ((c + d : ℕ) : ℝ) := by exact_mod_cast hn
    push_cast at this; linarith
  have c0 : (0 : ℝ) ≤ (d : ℝ) - b := by
    have : (b : ℝ) ≤ d := by exact_mod_cast hbc.trans hcd
    linarith
  nlinarith [mul_le_mul_of_nonneg_left m1 c0]

/-- `δ₂ = L b + L d - L a - L c ≥ β` unless `a = b` and `c = d`. -/
theorem birkDiv_C2 {a b c d : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d)
    (hne : ¬ (a = b ∧ c = d)) :
    m / (27 * birkL m a ^ 3) ≤ birkL m b + birkL m d - birkL m a - birkL m c := by
  have s1 := birkL_step m hm hab
  have s2 := birkL_step m hm hcd
  have m1 := birkDelta_mono m hm (hab.trans hbc)
  have dp := birkDelta_pos m hm ha
  have hb := birkDelta_ge_beta m hm ha
  have hn : a + c + 1 ≤ b + d := by omega
  have hn' : (1 : ℝ) ≤ ((b : ℝ) - a) + ((d : ℝ) - c) := by
    have : ((a + c + 1 : ℕ) : ℝ) ≤ ((b + d : ℕ) : ℝ) := by exact_mod_cast hn
    push_cast at this; linarith
  have c0 : (0 : ℝ) ≤ (d : ℝ) - c := by
    have : (c : ℝ) ≤ d := by exact_mod_cast hcd
    linarith
  nlinarith [mul_le_mul_of_nonneg_left (birkDelta_mono m hm (hab.trans hbc)) c0]

/-- Inner pair, case `d + a = b + c`: `δ₁ = L a + L d - L b - L c ≥ β` unless `a = b`, `c = d`. -/
theorem birkDiv_C1i {a b c d : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d)
    (hsel : d + a = b + c) (hne : ¬ (a = b ∧ c = d)) :
    m / (27 * birkL m a ^ 3) ≤ birkL m a + birkL m d - birkL m b - birkL m c := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hab
  have ht : 1 ≤ t := by
    by_contra h
    have : t = 0 := by omega
    subst this
    exact hne ⟨by omega, by omega⟩
  have hd : d = c + t := by omega
  subst hd
  have h1 := birkL_incr_sub m hm (show a ≤ c by omega) t ht
  have h2 := birkDelta_mono m hm (show a + 1 ≤ c by omega)
  have h3 := birkL_second_diff m hm a
  have e1 : birkDelta m (a + 1) - birkDelta m a =
      birkL m (a + 2) - 2 * birkL m (a + 1) + birkL m a := by
    unfold birkDelta; ring_nf
  -- `L (a+2) ≤ 3 L a`
  have hL : birkL m (a + 2) ≤ 3 * birkL m a := by
    refine le_of_sq_le_sq ?_ (by have := birkL_pos m hm a; positivity)
    rw [birkL_sq m hm, mul_pow, birkL_sq m hm]
    have : (1 : ℝ) ≤ a := by exact_mod_cast ha
    push_cast; nlinarith
  have hcube : birkL m (a + 2) ^ 3 ≤ 27 * birkL m a ^ 3 := by
    have := birkL_pos m hm (a + 2)
    calc birkL m (a + 2) ^ 3 ≤ (3 * birkL m a) ^ 3 := pow_le_pow_left₀ this.le hL 3
      _ = 27 * birkL m a ^ 3 := by ring
  have hb : m / (27 * birkL m a ^ 3) ≤ m / birkL m (a + 2) ^ 3 :=
    div_le_div_of_nonneg_left hm.le (by have := birkL_pos m hm (a + 2); positivity) hcube
  linarith

/-- Inner pair, case `d = a + b + c`: `δ₁ ≥ β`. -/
theorem birkDiv_C1ii {a b c d : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) (hbc : b ≤ c)
    (hd : d = a + b + c) :
    m / (27 * birkL m a ^ 3) ≤ birkL m a + birkL m d - birkL m b - birkL m c := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hab
  have h1 := birkL_incr_mono m hm (show a ≤ c by omega) t
  have h2 := birkL_add_ge m hm (c + t) (2 * a)
  have h3 := birkDelta_mono m hm (show a ≤ c + t by omega)
  have hde : d = c + t + 2 * a := by omega
  subst hde
  have dp := birkDelta_pos m hm ha
  have hb := birkDelta_ge_beta m hm ha
  have h1a : (1 : ℝ) ≤ 2 * a := by
    have : (1 : ℝ) ≤ a := by exact_mod_cast ha
    linarith
  have : (2 * (a : ℝ)) * birkDelta m a ≤ (2 * (a : ℝ)) * birkDelta m (c + t) :=
    mul_le_mul_of_nonneg_left h3 (by linarith)
  push_cast at h2
  nlinarith

end KAM.Wave

end
