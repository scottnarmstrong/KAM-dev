/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Certificate.Expr.BallRound
public import KAM.Certificate.Expr.Sqrt

/-!
# The ball of the total square root

`ballSqrt P c r` is the ball step of `SlpOp.sqrt` on the operand ball `(c, r)`. It fails
(`none`) unless `r < re c`, which puts the operand ball in the open right half-plane. It then
computes a positive dyadic anchor `s ≈ √(re c)` by rational Newton steps rounded to `P`
significant bits (`sqrtAnchor`; its accuracy is irrelevant to soundness), the bound
`R = |re c - s²| + |im c| + r ≥ |z - s²|` on the operand ball, checks `0 < s` and `R < s²`
(else `none`), and returns the ball `(s, R/s)` rounded outward (`ballRound`). Soundness is the
scalar rule `sqrtE_ball` (`ballSqrt_sound`); a successful step certifies `r < re c`
(`ballSqrt_lt_re`), whence every operand in the ball has positive real part
(`re_pos_of_mem_ballSqrt`).
-/

@[expose] public section

namespace KAM.Certificate

open CertArith

/-- `k` Newton steps `s ↦ (s + x/s)/2` for `√x`, each rounded up to a multiple of `1/S`. -/
def sqrtNewton (S x : ℚ) : ℕ → ℚ → ℚ
  | 0, s => s
  | k + 1, s => sqrtNewton S x k (dyUp S ((s + x / s) / 2))

/-- A dyadic approximation of `√x` (`x > 0`) to about `P` significant bits: nine rounded Newton
steps from `2^(⌊log₂ x⌋ / 2)`. Only its positivity is checked; soundness never uses its accuracy. -/
def sqrtAnchor (P : ℕ) (x : ℚ) : ℚ :=
  let e := ilog2Q x / 2
  sqrtNewton (dyScale ((P : ℤ) - e)) x 9 (dyScale e)

/-- The ball of `sqrtE` on the operand ball `(c, r)` (`none` unless certified in the right
half-plane with a positive anchor and `R < s²`), rounded outward to `P` bits. -/
def ballSqrt (P : ℕ) (c : CC ℚ) (r : ℚ) : Option (CC ℚ × ℚ) :=
  if r < c.re then
    let s := sqrtAnchor P c.re
    let R := |c.re - s * s| + |c.im| + r
    if 0 < s ∧ R < s * s then some (ballRound P (⟨s, 0⟩, R / s)) else none
  else none

/-- A successful square-root ball certifies the operand ball in the right half-plane. -/
theorem ballSqrt_lt_re {P : ℕ} {c : CC ℚ} {r : ℚ} {b : CC ℚ × ℚ}
    (h : ballSqrt P c r = some b) : r < c.re := by
  unfold ballSqrt at h
  split_ifs at h with h1
  exact h1

/-- Every point of a ball `(c, r)` with `r < re c` has positive real part. -/
theorem re_pos_of_ball {c : CC ℚ} {r : ℚ} (hr : r < c.re) {z : ℂ}
    (hz : ‖z - c.toC‖ ≤ (r : ℝ)) : 0 < z.re := by
  have h1 := (Complex.abs_re_le_norm (z - c.toC)).trans hz
  have hc : (c.toC).re = (c.re : ℝ) := by simp [CC.toC, CertArith.val]
  rw [Complex.sub_re, hc] at h1
  have hr' : (r : ℝ) < (c.re : ℝ) := by exact_mod_cast hr
  linarith [neg_abs_le (z.re - (c.re : ℝ))]

theorem re_pos_of_mem_ballSqrt {P : ℕ} {c : CC ℚ} {r : ℚ} {b : CC ℚ × ℚ}
    (h : ballSqrt P c r = some b) {z : ℂ} (hz : ‖z - c.toC‖ ≤ (r : ℝ)) : 0 < z.re :=
  re_pos_of_ball (ballSqrt_lt_re h) hz

/-- Soundness of the square-root ball. -/
theorem ballSqrt_sound (P : ℕ) {c : CC ℚ} {r : ℚ} {b : CC ℚ × ℚ}
    (h : ballSqrt P c r = some b) {z : ℂ} (hz : ‖z - c.toC‖ ≤ (r : ℝ)) :
    ‖sqrtE z - b.1.toC‖ ≤ (b.2 : ℝ) := by
  unfold ballSqrt at h
  simp only at h
  split_ifs at h with h1 h2
  simp only [Option.some.injEq] at h
  subst h
  refine ballRound_mem P ?_
  set s := sqrtAnchor P c.re
  set R := |c.re - s * s| + |c.im| + r
  have hs : (0 : ℝ) < (s : ℝ) := by exact_mod_cast h2.1
  have hR : (R : ℝ) < (s : ℝ) ^ 2 := by rw [sq]; exact_mod_cast h2.2
  have hcs : ‖c.toC - (s : ℂ) ^ 2‖ ≤ ((|c.re - s * s| + |c.im| : ℚ) : ℝ) := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans (le_of_eq ?_)
    simp [CC.toC, CertArith.val, sq]
  have hzs : ‖z - ((s : ℝ) : ℂ) ^ 2‖ ≤ (R : ℝ) := by
    have := norm_sub_le_norm_sub_add_norm_sub z c.toC ((s : ℂ) ^ 2)
    have e : (R : ℝ) = ((|c.re - s * s| + |c.im| : ℚ) : ℝ) + (r : ℝ) := by
      simp only [R]; push_cast; ring
    push_cast at this hcs ⊢
    rw [e]
    push_cast
    linarith
  obtain ⟨-, hb⟩ := sqrtE_ball hs hR hzs
  have e : CC.toC (⟨s, 0⟩ : CC ℚ) = ((s : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [CC.toC, CertArith.val]
  rw [e]
  have e2 : ((R / s : ℚ) : ℝ) = (R : ℝ) / (s : ℝ) := by push_cast; ring
  rw [e2]
  exact hb

end KAM.Certificate

end
