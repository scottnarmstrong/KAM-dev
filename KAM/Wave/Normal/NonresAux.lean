/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Frozen.Wave.Defs.Lam

/-!
# Analytic ingredients for quartic nonresonance (blueprint `bpW:w0n:nonres`)

Off the frontier: source-faithful infrastructure used by several nodes. The dependency graph is
still being built.

For `m > 0` the extension `lamExt m x = √(x² + m)` of the frozen `KAM.Wave.lam` to real arguments
is increasing on `[0, ∞)`, strictly subadditive on `(0, ∞)`, and convex (hence
`lamExt x + lamExt y ≤ lamExt (x+y) + lamExt 0` on `[0, ∞)`). From these we prove the three
"type" lemmas of the proof of `bpW:w0n:nonres`: the cases (1), (2), (3) of Step
`stepW:w0n:22` and the case of Step `stepW:w0n:31`.
-/

@[expose] public noncomputable section

namespace KAM.Wave

/-- The real extension `x ↦ √(x² + m)` of the frozen `lam`. -/
def lamExt (m x : ℝ) : ℝ := Real.sqrt (x ^ 2 + m)

theorem lam_eq_lamExt (m : ℝ) (hm : 0 < m) (j : ℕ+) : lam m hm j = lamExt m ((j : ℕ) : ℝ) := rfl

theorem lamExt_pos {m : ℝ} (hm : 0 < m) (x : ℝ) : 0 < lamExt m x :=
  Real.sqrt_pos.2 (by positivity)

theorem lamExt_sq (m x : ℝ) (hm : 0 < m) : lamExt m x ^ 2 = x ^ 2 + m :=
  Real.sq_sqrt (by positivity)

theorem lamExt_lt {m : ℝ} (hm : 0 < m) {x y : ℝ} (hx : 0 ≤ x) (hxy : x < y) : lamExt m x < lamExt m y := by
  unfold lamExt
  exact Real.sqrt_lt_sqrt (by positivity) (by nlinarith)

theorem lamExt_le {m : ℝ} (hm : 0 < m) {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) : lamExt m x ≤ lamExt m y := by
  rcases hxy.eq_or_lt with rfl | h
  · exact le_rfl
  · exact (lamExt_lt hm hx h).le

/-- `lamExt u * lamExt v ≥ u v + m`. -/
theorem lamExt_mul_ge {m : ℝ} (hm : 0 < m) (u v : ℝ) : u * v + m ≤ lamExt m u * lamExt m v := by
  unfold lamExt
  rw [← Real.sqrt_mul (by positivity)]
  refine le_trans (le_abs_self _) (Real.abs_le_sqrt ?_)
  nlinarith [sq_nonneg (u - v)]

/-- Strict subadditivity of `lamExt`. -/
theorem lamExt_add_lt {m : ℝ} (hm : 0 < m) (x y : ℝ) :
    lamExt m (x + y) < lamExt m x + lamExt m y := by
  have h := lamExt_mul_ge hm x y
  have hP := lamExt_sq m x hm
  have hQ := lamExt_sq m y hm
  have hpos := lamExt_pos hm x
  have hpos' := lamExt_pos hm y
  have hs := lamExt_sq m (x + y) hm
  have := lamExt_pos hm (x + y)
  nlinarith

theorem lamExt_le_of_sq {m w R : ℝ} (hR : 0 ≤ R) (h : w ^ 2 + m ≤ R ^ 2) : lamExt m w ≤ R :=
  Real.sqrt_le_iff.2 ⟨hR, h⟩

/-- Convexity of `lamExt` in the weighted form. -/
theorem lamExt_convex {m : ℝ} (hm : 0 < m) {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (u v : ℝ) :
    lamExt m (θ * u + (1 - θ) * v) ≤ θ * lamExt m u + (1 - θ) * lamExt m v := by
  have hP := lamExt_sq m u hm
  have hQ := lamExt_sq m v hm
  have h := lamExt_mul_ge hm u v
  have hP0 := (lamExt_pos hm u).le
  have hQ0 := (lamExt_pos hm v).le
  have h1' : 0 ≤ 1 - θ := sub_nonneg.2 h1
  refine lamExt_le_of_sq (by positivity) ?_
  have : 0 ≤ θ * (1 - θ) := mul_nonneg h0 h1'
  nlinarith [mul_nonneg this (sub_nonneg.2 h)]

/-- Supermodularity `f x + f y ≤ f (x + y) + f 0` on `[0, ∞)`. -/
theorem lamExt_super {m : ℝ} (hm : 0 < m) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    lamExt m x + lamExt m y ≤ lamExt m (x + y) + lamExt m 0 := by
  rcases hx.eq_or_lt with rfl | hx'
  · simp [add_comm]
  have hs : 0 < x + y := by linarith
  have h0 : 0 ≤ x / (x + y) := by positivity
  have h1 : x / (x + y) ≤ 1 := by rw [div_le_one hs]; linarith
  have e1 := lamExt_convex hm h0 h1 (x + y) 0
  have h0' : 0 ≤ y / (x + y) := by positivity
  have h1' : y / (x + y) ≤ 1 := by rw [div_le_one hs]; linarith
  have e2 := lamExt_convex hm h0' h1' (x + y) 0
  have a1 : x / (x + y) * (x + y) + (1 - x / (x + y)) * 0 = x := by field_simp; ring
  have a2 : y / (x + y) * (x + y) + (1 - y / (x + y)) * 0 = y := by field_simp; ring
  rw [a1] at e1
  rw [a2] at e2
  have hxy : y / (x + y) = 1 - x / (x + y) := by field_simp; ring
  rw [hxy] at e2
  have key : (x / (x + y) * lamExt m (x + y) + (1 - x / (x + y)) * lamExt m 0)
      + ((1 - x / (x + y)) * lamExt m (x + y) + (1 - (1 - x / (x + y))) * lamExt m 0)
      = lamExt m (x + y) + lamExt m 0 := by ring
  linarith

theorem lamExt_nat_lt {m : ℝ} (hm : 0 < m) {a b : ℕ} (h : a < b) :
    lamExt m (a : ℝ) < lamExt m (b : ℝ) :=
  lamExt_lt hm (Nat.cast_nonneg a) (by exact_mod_cast h)

theorem lamExt_nat_le {m : ℝ} (hm : 0 < m) {a b : ℕ} (h : a ≤ b) :
    lamExt m (a : ℝ) ≤ lamExt m (b : ℝ) :=
  lamExt_le hm (Nat.cast_nonneg a) (by exact_mod_cast h)

/-- Type (1): `a + b = c + d` and `λ_a + λ_b = λ_c + λ_d` force `{a, b} = {c, d}`. -/
theorem lamExt_pair_eq {m : ℝ} (hm : 0 < m) {a b c d : ℕ} (hs : a + b = c + d)
    (h : lamExt m a + lamExt m b = lamExt m c + lamExt m d) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  have hs' : (a : ℝ) + b = c + d := by exact_mod_cast hs
  set x : ℝ := (a : ℝ) with hxdef
  set y : ℝ := (b : ℝ) with hydef
  set z : ℝ := (c : ℝ) with hzdef
  set w : ℝ := (d : ℝ) with hwdef
  have hP := lamExt_sq m x hm
  have hQ := lamExt_sq m y hm
  have hR := lamExt_sq m z hm
  have hS := lamExt_sq m w hm
  have gxy := lamExt_mul_ge hm x y
  have gzw := lamExt_mul_ge hm z w
  set P := lamExt m x
  set Q := lamExt m y
  set R := lamExt m z
  set S := lamExt m w
  have e1 : P * Q - R * S = x * y - z * w := by
    have h2 : (P + Q) ^ 2 = (R + S) ^ 2 := by rw [h]
    nlinarith
  have e2 : (P * Q - R * S) * (P * Q + R * S) = (x * y - z * w) * (x * y + z * w - 2 * m) := by
    linear_combination Q ^ 2 * hP + (x ^ 2 + m) * hQ - S ^ 2 * hR - (z ^ 2 + m) * hS
      + m * (x + y + z + w) * hs'
  have hxy : x * y = z * w := by
    by_contra hne
    have hne' : x * y - z * w ≠ 0 := sub_ne_zero.2 hne
    rw [e1] at e2
    have := mul_left_cancel₀ hne' e2
    linarith
  have hfac : (x - z) * (x - w) = 0 := by nlinarith
  rcases mul_eq_zero.1 hfac with h1 | h1
  · left
    have : a = c := by
      have h1' := sub_eq_zero.1 h1
      rw [hxdef, hzdef] at h1'
      exact_mod_cast h1'
    exact ⟨this, by omega⟩
  · right
    have : a = d := by
      have h1' := sub_eq_zero.1 h1
      rw [hxdef, hwdef] at h1'
      exact_mod_cast h1'
    exact ⟨this, by omega⟩

/-- Type (2): `a + c = b + d` and `λ_a + λ_b = λ_c + λ_d` force `a = d`, `b = c`. -/
theorem lamExt_cross_eq {m : ℝ} (hm : 0 < m) {a b c d : ℕ} (hs : a + c = b + d)
    (h : lamExt m a + lamExt m b = lamExt m c + lamExt m d) : a = d ∧ b = c := by
  rcases lt_trichotomy a d with h1 | h1 | h1
  · exfalso
    have h2 : b < c := by omega
    have := lamExt_nat_lt hm h1
    have := lamExt_nat_lt hm h2
    linarith
  · exact ⟨h1, by omega⟩
  · exfalso
    have h2 : c < b := by omega
    have := lamExt_nat_lt hm h1
    have := lamExt_nat_lt hm h2
    linarith

/-- Type (3): if `X = Y + Z + W` with `Y ≥ 1` then `λ_Z + λ_W < λ_X + λ_Y`. -/
theorem lamExt_big_lt {m : ℝ} (hm : 0 < m) {X Y Z W : ℕ} (hY : 1 ≤ Y) (hX : X = Y + Z + W) :
    lamExt m Z + lamExt m W < lamExt m X + lamExt m Y := by
  have h1 := lamExt_super hm (Nat.cast_nonneg Z : (0 : ℝ) ≤ Z) (Nat.cast_nonneg W : (0 : ℝ) ≤ W)
  have h2 : lamExt m ((Z : ℝ) + W) ≤ lamExt m (X : ℝ) := by
    have := lamExt_nat_le hm (show Z + W ≤ X by omega)
    simpa using this
  have h3 : lamExt m 0 < lamExt m (Y : ℝ) := by
    have := lamExt_nat_lt hm (show 0 < Y by omega)
    simpa using this
  linarith

/-- Case of one sign against three: `λ_a + λ_b + λ_c = λ_d` is impossible when `d ≤ a + b + c`. -/
theorem lamExt_three_ne {m : ℝ} (hm : 0 < m) {a b c d : ℕ} (hd : d ≤ a + b + c) :
    lamExt m a + lamExt m b + lamExt m c ≠ lamExt m d := by
  intro h
  have h1 := lamExt_add_lt hm (a : ℝ) (b : ℝ)
  have h2 := lamExt_add_lt hm ((a : ℝ) + b) (c : ℝ)
  have h3 : lamExt m (d : ℝ) ≤ lamExt m ((a : ℝ) + b + c) := by
    have := lamExt_nat_le hm hd
    simpa using this
  linarith

end KAM.Wave

end
