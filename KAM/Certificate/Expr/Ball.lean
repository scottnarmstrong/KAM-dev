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

/-! ### Soundness of the slot balls -/

/-- The slot values `V` lie in the balls `acc`. -/
def BallRel (V : List ℂ) (acc : List (CC ℚ × ℚ)) : Prop :=
  V.length = acc.length ∧
    ∀ i, ‖V.getD i 0 - (acc.getD i ballZero).1.toC‖ ≤ ((acc.getD i ballZero).2 : ℝ)

theorem toC_zero_rat : CC.toC (⟨0, 0⟩ : CC ℚ) = 0 := by
  apply Complex.ext <;> simp [CC.toC, CertArith.val, instCertArithRat]

theorem toC_ratCast (q : ℚ) : CC.toC (⟨q, 0⟩ : CC ℚ) = ((q : ℝ) : ℂ) := by
  apply Complex.ext <;> simp [CC.toC, CertArith.val, instCertArithRat]

theorem ballZero_mem : ‖(0 : ℂ) - ballZero.1.toC‖ ≤ (ballZero.2 : ℝ) := by
  show ‖(0 : ℂ) - CC.toC (⟨0, 0⟩ : CC ℚ)‖ ≤ ((0 : ℚ) : ℝ)
  rw [toC_zero_rat]
  simp

theorem BallRel.nil : BallRel [] [] := ⟨rfl, fun i => by simpa using ballZero_mem⟩

theorem BallRel.snoc {V : List ℂ} {acc : List (CC ℚ × ℚ)} (h : BallRel V acc) {v : ℂ}
    {b : CC ℚ × ℚ} (hb : ‖v - b.1.toC‖ ≤ (b.2 : ℝ)) : BallRel (V ++ [v]) (acc ++ [b]) := by
  refine ⟨by simp [h.1], fun i => ?_⟩
  simp only [List.getD_eq_getElem?_getD]
  rcases lt_trichotomy i V.length with hi | hi | hi
  · have hi' : i < acc.length := h.1 ▸ hi
    rw [List.getElem?_append_left hi, List.getElem?_append_left hi']
    have := h.2 i
    simpa [List.getD_eq_getElem?_getD] using this
  · have hi' : i = acc.length := hi.trans h.1
    subst hi
    rw [List.getElem?_append_right (le_refl _), List.getElem?_append_right (le_of_eq h.1.symm),
      ← h.1]
    simpa using hb
  · have hi' : acc.length < i := h.1 ▸ hi
    rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]
    simpa using ballZero_mem

theorem ballStep_sound {n : ℕ} {WH : CertWeight} {s N : ℕ} (hW : checkWeight WH s N = true)
    {centre radius : List ℚ} {taylorN : ℕ} {z : (Fin n → ℂ) × (Fin n → ℂ)}
    (hz : z ∈ certDomain n WH.rho centre radius) {V : List ℂ} {acc : List (CC ℚ × ℚ)}
    (hR : BallRel V acc) {op : SlpOp} {b : CC ℚ × ℚ}
    (h : ballStep n WH centre radius taylorN acc op = some b) :
    ‖op.step n z V - b.1.toC‖ ≤ (b.2 : ℝ) := by
  cases op with
  | const re im deg =>
    simp only [ballStep, Option.some.injEq] at h
    subst h
    exact mem_constBall re im deg
  | action j =>
    simp only [ballStep] at h
    by_cases hj : j < n
    · simp only [hj, ite_true, Option.some.injEq] at h
      subst h
      have := (hz.2 ⟨j, hj⟩).le
      simp only [SlpOp.step, hj, dite_true]
      rw [toC_ratCast]
      exact_mod_cast this
    · simp only [hj, ite_false, Option.some.injEq] at h
      subst h
      simp only [SlpOp.step, hj, dite_false]
      exact ballZero_mem
  | char k =>
    simp only [ballStep, Option.some.injEq] at h
    subst h
    simp only [SlpOp.step]
    rw [toC_zero_rat, sub_zero]
    have hθ := norm_character_le_weight hW (certKeyFun n k) hz.1
    have hc : Complex.exp (Complex.I * modePhase n k z.1) = character (certKeyFun n k) z.1 := by
      unfold character modePhase
      congr 1
      ring
    rw [hc]
    refine hθ.trans ?_
    have h1 := CertWeight.one_le_w hW
    have h2 := sum_natAbs_certKeyFun_le n k
    show _ ≤ ((WH.w ^ (k.map Int.natAbs).sum : ℚ) : ℝ)
    push_cast
    exact pow_le_pow_right₀ h1 h2
  | add a b =>
    simp only [ballStep, Option.some.injEq] at h
    subst h
    exact CertBall.mem_plus (b₁ := ballOf (acc.getD a ballZero))
      (b₂ := ballOf (acc.getD b ballZero)) (hR.2 a) (hR.2 b)
  | mul a b =>
    simp only [ballStep, Option.some.injEq] at h
    subst h
    exact CertBall.mem_times (b₁ := ballOf (acc.getD a ballZero))
      (b₂ := ballOf (acc.getD b ballZero)) (hR.2 a) (hR.2 b)
  | exp a =>
    simp only [ballStep] at h
    exact certCExpReduced_sound h (hR.2 a)
  | inv a =>
    simp only [ballStep] at h
    split_ifs at h with hlt
    simp only [Option.some.injEq] at h
    subst h
    simp only [SlpOp.step]
    set x := acc.getD a ballZero with hx
    have hmem := hR.2 a
    rw [← hx] at hmem
    have hlt' : (x.2 : ℝ) < max |(x.1.re : ℝ)| |(x.1.im : ℝ)| := by exact_mod_cast hlt
    have hmc : max |(x.1.re : ℝ)| |(x.1.im : ℝ)| ≤ ‖x.1.toC‖ := by
      refine max_le ?_ ?_
      · exact Complex.abs_re_le_norm x.1.toC
      · exact Complex.abs_im_le_norm x.1.toC
    obtain ⟨-, hb⟩ := inv_ball_bound hlt' hmc hmem
    have hc : x.1.toC⁻¹ = CC.toC (⟨x.1.re / (x.1.re ^ 2 + x.1.im ^ 2),
        -x.1.im / (x.1.re ^ 2 + x.1.im ^ 2)⟩ : CC ℚ) := by
      apply Complex.ext <;>
        simp [CC.toC, CertArith.val, instCertArithRat, Complex.inv_re, Complex.inv_im,
          Complex.normSq_apply, sq, neg_div]
    rw [← hc]
    convert hb using 1
    push_cast
    rfl

end KAM.Certificate

end
