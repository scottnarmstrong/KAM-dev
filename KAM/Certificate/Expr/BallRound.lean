/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Certificate.Arith.ComplexExp
public import KAM.Certificate.Arith.Rat

/-!
# Dyadic outward rounding of rational balls

The slot balls of `Slp.balls` are rounded outward after every operation (`ballRound`) to `P`
significant bits relative to their magnitude `m = |re| + |im| + r`: with `e = ilog2Q m` (the
binary exponent of `m`, up to one), each centre coordinate is rounded down to a multiple of
`2^(e - P)`, the rounding error is added to the radius, and the radius is rounded up to the same
grid. This keeps the numerators and denominators of the exact rational ball arithmetic bounded
(about `P` bits of mantissa) instead of doubling at every product, and it keeps the relative
accuracy of small slots (a fixed absolute grid would erase slots below it, whose errors later
products amplify). A rounded ball contains every point of the original ball
(`ballRound_mem`): the containment only needs a positive scale. The default precision is
`slpBallPrec = 320` bits.

`ballExp` is the range-reduced exponential of `certCExpReduced` with the Taylor ball and every
squaring rounded the same way (`ballExp_sound`). Scales are natural-number powers of two and
exponents come from `Nat.log2`, which the kernel evaluates by GMP.
-/

@[expose] public section

namespace KAM.Certificate

open CertArith

/-- The relative working precision (bits) of the slot balls of `Slp.balls`: every slot ball is
rounded to `320` significant bits of its magnitude, the precision of the fixed-point backend of
the certificates, so the relative rounding error per slot (about `10^-96`) stays far below the
margins of the checked bounds. -/
def slpBallPrec : ℕ := 320

/-- The binary exponent of a rational, up to one: `log2 |num| - log2 den` (`0` for `0`). -/
def ilog2Q (q : ℚ) : ℤ := (Nat.log2 q.num.natAbs : ℤ) - (Nat.log2 q.den : ℤ)

/-- The dyadic scale `2^k` (`k : ℤ`) as a rational; the power is taken in `ℕ`. -/
def dyScale : ℤ → ℚ
  | .ofNat j => ((2 ^ j : ℕ) : ℚ)
  | .negSucc j => 1 / ((2 ^ (j + 1) : ℕ) : ℚ)

/-- `q` rounded down to a multiple of `1 / S`. -/
def dyDown (S q : ℚ) : ℚ := (⌊q * S⌋ : ℚ) / S

/-- `q` rounded up to a multiple of `1 / S`. -/
def dyUp (S q : ℚ) : ℚ := (⌈q * S⌉ : ℚ) / S

theorem dyScale_pos (k : ℤ) : 0 < dyScale k := by
  cases k <;> simp only [dyScale] <;> positivity

theorem dyDown_le {S : ℚ} (hS : 0 < S) (q : ℚ) : dyDown S q ≤ q := by
  unfold dyDown
  rw [div_le_iff₀ hS]
  exact Int.floor_le _

theorem le_dyUp {S : ℚ} (hS : 0 < S) (q : ℚ) : q ≤ dyUp S q := by
  unfold dyUp
  rw [le_div_iff₀ hS]
  exact Int.le_ceil _

/-- Outward rounding of a ball `(centre, radius)` to `P` significant bits of its magnitude
`|re| + |im| + r`: the grid is `2^(ilog2Q m - P)`. -/
def ballRound (P : ℕ) (b : CC ℚ × ℚ) : CC ℚ × ℚ :=
  match b with
  | (⟨re, im⟩, r) =>
    let S := dyScale ((P : ℤ) - ilog2Q (|re| + |im| + r))
    let re' := dyDown S re
    let im' := dyDown S im
    (⟨re', im'⟩, dyUp S (r + (re - re') + (im - im')))

/-- Containment survives outward rounding to any positive scale. -/
theorem ballRound_mem_aux {S : ℚ} (hS : 0 < S) {w : ℂ} {re im r : ℚ}
    (h : ‖w - CC.toC (⟨re, im⟩ : CC ℚ)‖ ≤ (r : ℝ)) :
    ‖w - CC.toC (⟨dyDown S re, dyDown S im⟩ : CC ℚ)‖ ≤
      ((dyUp S (r + (re - dyDown S re) + (im - dyDown S im)) : ℚ) : ℝ) := by
  have h1 := dyDown_le hS re
  have h2 := dyDown_le hS im
  have h3 := le_dyUp hS (r + (re - dyDown S re) + (im - dyDown S im))
  have hc : ‖(CC.toC (⟨re, im⟩ : CC ℚ)) - CC.toC (⟨dyDown S re, dyDown S im⟩ : CC ℚ)‖ ≤
      ((re - dyDown S re : ℚ) : ℝ) + ((im - dyDown S im : ℚ) : ℝ) := by
    apply norm_le_of_re_im
    · simp only [CC.toC, Complex.sub_re, CertArith.val, Rat.cast_sub]
      rw [abs_of_nonneg (by simpa using (show ((dyDown S re : ℚ) : ℝ) ≤ re by exact_mod_cast h1))]
    · simp only [CC.toC, Complex.sub_im, CertArith.val, Rat.cast_sub]
      rw [abs_of_nonneg (by simpa using (show ((dyDown S im : ℚ) : ℝ) ≤ im by exact_mod_cast h2))]
  have h3' : ((r + (re - dyDown S re) + (im - dyDown S im) : ℚ) : ℝ) ≤
      ((dyUp S (r + (re - dyDown S re) + (im - dyDown S im)) : ℚ) : ℝ) := by exact_mod_cast h3
  have htri := norm_sub_le_norm_sub_add_norm_sub w (CC.toC (⟨re, im⟩ : CC ℚ))
    (CC.toC (⟨dyDown S re, dyDown S im⟩ : CC ℚ))
  push_cast at h3' hc h ⊢
  linarith

/-- Containment survives outward rounding. -/
theorem ballRound_mem (P : ℕ) {w : ℂ} {b : CC ℚ × ℚ} (h : ‖w - b.1.toC‖ ≤ (b.2 : ℝ)) :
    ‖w - (ballRound P b).1.toC‖ ≤ ((ballRound P b).2 : ℝ) := by
  obtain ⟨⟨re, im⟩, r⟩ := b
  exact ballRound_mem_aux (dyScale_pos _) h

/-! ### Ball sum and product over `ℚ` -/

/-- `CertBall.plus` over `ℚ` without its error terms, which vanish there (`plusQ_eq`). -/
def plusQ (b₁ b₂ : CertBall ℚ) : CertBall ℚ :=
  ⟨⟨b₁.c.re + b₂.c.re, b₁.c.im + b₂.c.im⟩, b₁.r + b₂.r⟩

/-- `CertBall.times` over `ℚ` without its error terms, which vanish there (`timesQ_eq`). -/
def timesQ (b₁ b₂ : CertBall ℚ) : CertBall ℚ :=
  ⟨⟨b₁.c.re * b₂.c.re - b₁.c.im * b₂.c.im, b₁.c.re * b₂.c.im + b₁.c.im * b₂.c.re⟩,
    b₁.r * (|b₂.c.re| + |b₂.c.im| + b₂.r) + (|b₁.c.re| + |b₁.c.im|) * b₂.r⟩

theorem plusQ_eq (b₁ b₂ : CertBall ℚ) : plusQ b₁ b₂ = CertBall.plus b₁ b₂ := by
  simp [plusQ, CertBall.plus, CertArith.add, CertArith.upAdd, CertArith.addErr]

theorem timesQ_eq (b₁ b₂ : CertBall ℚ) : timesQ b₁ b₂ = CertBall.times b₁ b₂ := by
  simp [timesQ, CertBall.times, CertBall.mulReErr, CertBall.mulImErr, CC.normUp,
    CertArith.add, CertArith.upAdd, CertArith.addErr, CertArith.mul, CertArith.upMul,
    CertArith.mulErr, CertArith.neg, CertArith.abs, sub_eq_add_neg]

/-! ### The rounded range-reduced exponential -/

/-- Square a ball `s` times, rounding outward after each squaring. -/
def ballSqIter (P : ℕ) (b : CC ℚ × ℚ) : ℕ → CC ℚ × ℚ
  | 0 => b
  | s + 1 =>
    match ballSqIter P b s with
    | (c, r) =>
      let t := timesQ (⟨c, r⟩ : CertBall ℚ) ⟨c, r⟩
      ballRound P (t.c, t.r)

theorem ballSqIter_mem (P : ℕ) {v : ℂ} {b : CC ℚ × ℚ}
    (hv : ‖Complex.exp v - b.1.toC‖ ≤ (b.2 : ℝ)) (s : ℕ) :
    ‖Complex.exp (2 ^ s * v) - (ballSqIter P b s).1.toC‖ ≤ ((ballSqIter P b s).2 : ℝ) := by
  induction s with
  | zero => simpa [ballSqIter] using hv
  | succ s ih =>
    have e : Complex.exp (2 ^ (s + 1) * v) =
        Complex.exp (2 ^ s * v) * Complex.exp (2 ^ s * v) := by
      rw [← Complex.exp_add]; congr 1; ring
    rw [e]
    simp only [ballSqIter]
    rcases hb : ballSqIter P b s with ⟨c, r⟩
    rw [hb] at ih
    have hm : CertBall.Mem (Complex.exp (2 ^ s * v)) (⟨c, r⟩ : CertBall ℚ) := ih
    have ht := CertBall.mem_times hm hm
    rw [← timesQ_eq] at ht
    exact ballRound_mem P ht

/-- The range-reduced exponential ball of `certCExpReduced`, with the Taylor ball and every
squaring rounded outward to the grid `2^-P`; `none` unless the reduced ball passes
`certCExpSmall`. -/
def ballExp (P : ℕ) (z : CC ℚ) (zRad : ℚ) (s N : ℕ) : Option (CC ℚ × ℚ) :=
  let red := CertBall.times (⟨z, zRad⟩ : CertBall ℚ) (CertBall.ofRat (1 / 2 ^ s))
  if certCExpSmall red.c red.r then
    some (ballSqIter P (ballRound P (certCExp red.c red.r N)) s)
  else none

theorem ballExp_sound (P : ℕ) {z : CC ℚ} {zRad : ℚ} {s N : ℕ} {out : CC ℚ × ℚ}
    (h : ballExp P z zRad s N = some out) {w : ℂ} (hw : ‖w - z.toC‖ ≤ (zRad : ℝ)) :
    ‖Complex.exp w - out.1.toC‖ ≤ (out.2 : ℝ) := by
  unfold ballExp at h
  set red := CertBall.times (⟨z, zRad⟩ : CertBall ℚ) (CertBall.ofRat (α := ℚ) (1 / 2 ^ s))
    with hred
  by_cases hs : certCExpSmall red.c red.r = true
  · simp only [hs, ite_true, Option.some.injEq] at h
    have hmem : CertBall.Mem (w * (((1 / 2 ^ s : ℚ)) : ℂ)) red :=
      CertBall.mem_times (b₁ := ⟨z, zRad⟩) hw (CertBall.mem_ofRat _)
    have hexp := certCExp_sound_of_small red.c red.r N (certCExpSmall_sound hs) hmem
    have hsq := ballSqIter_mem P (ballRound_mem P hexp) s
    have e : (2 : ℂ) ^ s * (w * (((1 / 2 ^ s : ℚ)) : ℂ)) = w := by
      push_cast
      have : (2 : ℂ) ^ s ≠ 0 := pow_ne_zero _ two_ne_zero
      field_simp
    rw [e] at hsq
    rw [← h]
    exact hsq
  · simp only [hs] at h
    cases h

end KAM.Certificate

end
