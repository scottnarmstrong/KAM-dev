/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Certificate.Arith.ComplexExp
public import KAM.Certificate.Arith.Rat
public import KAM.Certificate.Expr.Slp
public import KAM.Certificate.Model.Basic
public import KAM.Certificate.Arith.PiHigh

/-!
# Certified ball evaluation of expression programs

`Slp.balls` evaluates a straight-line program in exact rational ball arithmetic on the
Hamiltonian domain `certDomain`: every slot gets a centre and a radius with
`|slot - centre| ≤ radius` there (`Slp.val_mem_ball`). Constants carry a ball for `(2π)^deg`
from the coarse enclosure of `π`; actions are the domain balls; characters `e^{2πi k·θ}` are
bounded by the strip weight; `exp` (hence compiled `sin`, `cos`) goes through the
range-reduced `certCExpReduced` with the halving count `cexpHalvings` computed from the operand
ball, failing closed on `none`; `inv` fails unless the operand ball excludes `0`.
-/

@[expose] public section

namespace KAM.Certificate

open KAM CertArith

/-- The halving count computed from a rational ball (used by `Slp.balls`, never a caller-side
hypothesis): `2^s > 2 (|re| + |im| + r)`, so the exact reduced ball has `normUp + radius ≤ 1/2`. -/
def cexpHalvings (z : CC ℚ) (r : ℚ) : ℕ :=
  Nat.log2 ⌈2 * (|z.re| + |z.im| + r)⌉₊ + 1

theorem certCExpSmall_reduced (z : CC ℚ) (r : ℚ) (s : ℕ) :
    certCExpSmall (CertBall.times ⟨z, r⟩ (CertBall.ofRat (α := ℚ) (1 / 2 ^ s))).c
      (CertBall.times ⟨z, r⟩ (CertBall.ofRat (α := ℚ) (1 / 2 ^ s))).r =
    decide ((|z.re| + |z.im| + r) * (1 / 2 ^ s) ≤ 1) := by
  simp [certCExpSmall, CertBall.times, CertBall.ofRat, CC.normUp, CertArith.ble, CertArith.upAdd,
    CertArith.upMul, CertArith.add, CertArith.mul, CertArith.neg, CertArith.abs, CertArith.ofInt,
    CertArith.ofRatUp, CertArith.ofRatDown, CertArith.addErr, CertArith.mulErr,
    CertBall.mulReErr, CertBall.mulImErr]
  rw [add_mul, add_mul]

/-- Completeness over the exact backend (SO-BALL): with the computed count the reduction never
fails, so `Slp.balls` returns `none` at an `exp` slot only on a malformed program. -/
theorem certCExpReduced_cexpHalvings_isSome (z : CC ℚ) {r : ℚ} (hr : 0 ≤ r) (N : ℕ) :
    (certCExpReduced z r (cexpHalvings z r) N).isSome = true := by
  have hx : 0 ≤ |z.re| + |z.im| + r := by positivity
  have h1 : (⌈2 * (|z.re| + |z.im| + r)⌉₊ : ℚ) < 2 ^ (cexpHalvings z r) := by
    have := Nat.lt_log2_self (n := ⌈2 * (|z.re| + |z.im| + r)⌉₊)
    unfold cexpHalvings
    exact_mod_cast this
  have h2 : 2 * (|z.re| + |z.im| + r) ≤ (⌈2 * (|z.re| + |z.im| + r)⌉₊ : ℚ) := Nat.le_ceil _
  have h3 : (|z.re| + |z.im| + r) * (1 / 2 ^ (cexpHalvings z r)) ≤ 1 := by
    have hp : (0 : ℚ) < 2 ^ (cexpHalvings z r) := by positivity
    rw [mul_one_div, div_le_one hp]
    linarith
  unfold certCExpReduced
  dsimp only
  rw [certCExpSmall_reduced]
  rw [decide_eq_true h3]
  simp

/-! ### Balls of the constants -/

/-- A rational lower bound of `(2π)^d`. -/
def ballPiLo (d : ℤ) : ℚ := if 0 ≤ d then (2 * piLoQ) ^ d else (2 * piUpQ) ^ d

/-- A rational upper bound of `(2π)^d`. -/
def ballPiHi (d : ℤ) : ℚ := if 0 ≤ d then (2 * piUpQ) ^ d else (2 * piLoQ) ^ d

theorem ball_two_pi_zpow_mem (d : ℤ) :
    (ballPiLo d : ℝ) ≤ (2 * Real.pi) ^ d ∧ (2 * Real.pi) ^ d ≤ (ballPiHi d : ℝ) := by
  have h1 : (2 * (piLoQ : ℝ)) ≤ 2 * Real.pi := by linarith [piLoQ_lt_pi]
  have h2 : 2 * Real.pi ≤ 2 * (piUpQ : ℝ) := by linarith [pi_lt_piUpQ]
  have hlo : (0 : ℝ) < piLoQ := by norm_num [piLoQ]
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  unfold ballPiLo ballPiHi
  split_ifs with hd
  · push_cast
    exact ⟨zpow_le_zpow_left₀ hd (by positivity) h1, zpow_le_zpow_left₀ hd (by positivity) h2⟩
  · push_cast
    obtain ⟨m, rfl⟩ : ∃ m : ℕ, d = -(m : ℤ) := ⟨(-d).toNat, by omega⟩
    simp only [zpow_neg, zpow_natCast]
    exact ⟨inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) h2 m),
      inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) h1 m)⟩

/-- The ball of `(re + i im)(2π)^deg`. -/
def constBall (re im : ℚ) (deg : ℤ) : CertBall ℚ :=
  CertBall.times ⟨⟨re, im⟩, 0⟩ ⟨⟨(ballPiLo deg + ballPiHi deg) / 2, 0⟩,
    (ballPiHi deg - ballPiLo deg) / 2⟩

theorem mem_constBall (re im : ℚ) (deg : ℤ) :
    CertBall.Mem (slpConstVal re im deg) (constBall re im deg) := by
  refine CertBall.mem_times (w₁ := (re : ℂ) + (im : ℂ) * Complex.I) (b₁ := ⟨⟨re, im⟩, 0⟩)
    (w₂ := (2 * (Real.pi : ℂ)) ^ deg) ?_ ?_
  · have : (re : ℂ) + (im : ℂ) * Complex.I = CC.toC (⟨re, im⟩ : CC ℚ) := by
      apply Complex.ext <;> simp [CC.toC, CertArith.val, instCertArithRat]
    show ‖_ - _‖ ≤ _
    rw [this]
    simp [CertArith.val, instCertArithRat]
  · obtain ⟨hlo, hhi⟩ := ball_two_pi_zpow_mem deg
    have e : (2 * (Real.pi : ℂ)) ^ deg = (((2 * Real.pi) ^ deg : ℝ) : ℂ) := by push_cast; rfl
    have e2 : CC.toC (⟨(ballPiLo deg + ballPiHi deg) / 2, 0⟩ : CC ℚ) =
        ((((ballPiLo deg + ballPiHi deg) / 2 : ℚ) : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [CC.toC, CertArith.val, instCertArithRat]
    show ‖_ - CC.toC _‖ ≤ _
    rw [e, e2, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_le]
    change -(((ballPiHi deg - ballPiLo deg) / 2 : ℚ) : ℝ) ≤ _ ∧ _ ≤
      (((ballPiHi deg - ballPiLo deg) / 2 : ℚ) : ℝ)
    push_cast
    constructor <;> linarith

/-! ### Ball of the inverse -/

theorem inv_ball_bound {x c : ℂ} {m r : ℝ} (hrm : r < m) (hmc : m ≤ ‖c‖) (hx : ‖x - c‖ ≤ r) :
    x ≠ 0 ∧ ‖x⁻¹ - c⁻¹‖ ≤ r / ((m - r) * m) := by
  have hr0 : 0 ≤ r := (norm_nonneg _).trans hx
  have hm0 : 0 < m := lt_of_le_of_lt hr0 hrm
  have hxc : m - r ≤ ‖x‖ := by
    have : ‖c‖ ≤ ‖x‖ + ‖x - c‖ := by
      have := norm_sub_norm_le c x
      rw [norm_sub_rev] at this
      linarith
    linarith
  have hpos : 0 < m - r := by linarith
  have hx0 : x ≠ 0 := by
    intro h
    rw [norm_eq_zero.mpr h] at hxc
    linarith
  refine ⟨hx0, ?_⟩
  have hc0 : c ≠ 0 := by
    intro h
    rw [h, norm_zero] at hmc
    linarith
  have e : x⁻¹ - c⁻¹ = (c - x) / (x * c) := by field_simp
  rw [e, norm_div, norm_mul, norm_sub_rev]
  have hd : (m - r) * m ≤ ‖x‖ * ‖c‖ := mul_le_mul hxc hmc hm0.le (norm_nonneg _)
  calc ‖x - c‖ / (‖x‖ * ‖c‖) ≤ r / (‖x‖ * ‖c‖) :=
        div_le_div_of_nonneg_right hx (by positivity)
    _ ≤ r / ((m - r) * m) := div_le_div_of_nonneg_left hr0 (by positivity) hd

/-! ### Ball arithmetic of a program -/

/-- The ball of an unwritten slot. -/
def ballZero : CC ℚ × ℚ := (⟨0, 0⟩, 0)

/-- The `CertBall` of a centre and radius. -/
def ballOf (b : CC ℚ × ℚ) : CertBall ℚ := ⟨b.1, b.2⟩

/-- The ball of one operation, given the balls `acc` of the earlier slots. -/
def ballStep (n : ℕ) (WH : CertWeight) (centre radius : List ℚ) (taylorN : ℕ)
    (acc : List (CC ℚ × ℚ)) : SlpOp → Option (CC ℚ × ℚ)
  | .const re im deg => some ((constBall re im deg).c, (constBall re im deg).r)
  | .action j =>
    if j < n then some (⟨centre.getD j 0, 0⟩, radius.getD j 0) else some ballZero
  | .char k => some (⟨0, 0⟩, WH.w ^ (k.map Int.natAbs).sum)
  | .add a b =>
    some ((CertBall.plus (ballOf (acc.getD a ballZero)) (ballOf (acc.getD b ballZero))).c,
      (CertBall.plus (ballOf (acc.getD a ballZero)) (ballOf (acc.getD b ballZero))).r)
  | .mul a b =>
    some ((CertBall.times (ballOf (acc.getD a ballZero)) (ballOf (acc.getD b ballZero))).c,
      (CertBall.times (ballOf (acc.getD a ballZero)) (ballOf (acc.getD b ballZero))).r)
  | .exp a =>
    certCExpReduced (acc.getD a ballZero).1 (acc.getD a ballZero).2
      (cexpHalvings (acc.getD a ballZero).1 (acc.getD a ballZero).2) taylorN
  | .inv a =>
    if (acc.getD a ballZero).2 < max |(acc.getD a ballZero).1.re| |(acc.getD a ballZero).1.im|
    then
      some (⟨(acc.getD a ballZero).1.re /
          ((acc.getD a ballZero).1.re ^ 2 + (acc.getD a ballZero).1.im ^ 2),
        -(acc.getD a ballZero).1.im /
          ((acc.getD a ballZero).1.re ^ 2 + (acc.getD a ballZero).1.im ^ 2)⟩,
        (acc.getD a ballZero).2 /
          ((max |(acc.getD a ballZero).1.re| |(acc.getD a ballZero).1.im| -
            (acc.getD a ballZero).2) *
            max |(acc.getD a ballZero).1.re| |(acc.getD a ballZero).1.im|))
    else none

/-- The balls of the slots of the operations `ops` after the slots `acc`. -/
def ballsAux (n : ℕ) (WH : CertWeight) (centre radius : List ℚ) (taylorN : ℕ) :
    List (CC ℚ × ℚ) → List SlpOp → Option (List (CC ℚ × ℚ))
  | acc, [] => some acc
  | acc, op :: ops =>
    (ballStep n WH centre radius taylorN acc op).bind fun b =>
      ballsAux n WH centre radius taylorN (acc ++ [b]) ops

/-- Ball arithmetic of every slot on `D` (no embedding), in `ℚ`: `(centre, radius)` with
`|slot - centre| ≤ radius` on `D`. Constants exact up to the enclosure of `π`; actions
`(c_j, r_j)`; characters `(0, w_H^{|k|₁})`; sums and products; `exp` (also the compiled `sin`,
`cos`) via `certCExpReduced c r (cexpHalvings c r) taylorN` on the operand ball `(c, r)`; `inv`
fails (`none`) unless the operand ball excludes `0`, i.e. `radius < max(|re|, |im|)` of its
centre. -/
def Slp.balls (n : ℕ) (p : Slp) (WH : CertWeight) (centre radius : List ℚ) (taylorN : ℕ) :
    Option (List (CC ℚ × ℚ)) :=
  ballsAux n WH centre radius taylorN [] p.ops

end KAM.Certificate

end
