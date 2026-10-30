/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Certificate.Arith.ComplexExp
public import KAM.Certificate.Arith.Rat
public import KAM.Certificate.Expr.Diff
public import KAM.Certificate.Model.Basic
public import KAM.Certificate.Arith.PiHigh
public import KAM.Certificate.Expr.BallRound
public import KAM.Certificate.Expr.BallSqrt

/-!
# Certified ball evaluation of expression programs

`Slp.balls` evaluates a straight-line program in rational ball arithmetic on the
Hamiltonian domain `certDomain`: every slot gets a centre and a radius with
`|slot - centre| ≤ radius` there (`Slp.val_mem_ball`). Constants carry a ball for `(2π)^deg`
from the coarse enclosure of `π`; actions are the domain balls; characters `e^{2πi k·θ}` are
bounded by the strip weight; `exp` (hence compiled `sin`, `cos`) goes through the
range-reduced `ballExp` (the rounded form of `certCExpReduced`) with the halving count
`cexpHalvings` computed from the operand ball, failing closed on `none`; `inv` fails unless the
operand ball excludes `0`; `sqrt` goes through `ballSqrt`, which fails unless the operand ball lies
in the right half-plane (`r < re c` and `R < s²` for a positive anchor `s`).

The balls of products, reciprocals, exponentials and square roots are rounded outward to
`slpBallPrec` significant bits (`ballRound`), so the rational sizes stay bounded over long programs,
and every slot ball is forced as it is computed (`ballForce`). The evaluated pass `ballsRev` keeps
the slots in reverse order (one cons per operation, one final reverse) and reads every operand ball
once; `ballsAux_eq_spec` identifies it with the in-order reference form `ballsSpec`, on which the
soundness proofs run.
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

/-- Completeness over the exact backend: with the computed count the reduction never
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
      apply Complex.ext <;> simp [CC.toC, CertArith.val]
    show ‖_ - _‖ ≤ _
    rw [this]
    simp [CertArith.val]
  · obtain ⟨hlo, hhi⟩ := ball_two_pi_zpow_mem deg
    have e : (2 * (Real.pi : ℂ)) ^ deg = (((2 * Real.pi) ^ deg : ℝ) : ℂ) := by push_cast; rfl
    have e2 : CC.toC (⟨(ballPiLo deg + ballPiHi deg) / 2, 0⟩ : CC ℚ) =
        ((((ballPiLo deg + ballPiHi deg) / 2 : ℚ) : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [CC.toC, CertArith.val]
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

/-- The ball of one operation, reading the balls of the earlier slots through `get`; each
operand ball is read once. The balls of `mul` and `inv` are rounded outward to `P` significant
bits (`ballRound`), `exp` goes through the rounded `ballExp`; constants, actions, characters and
sums are exact (a sum of rounded balls grows by at most one bit). -/
def ballStepG (P n : ℕ) (WH : CertWeight) (centre radius : List ℚ) (taylorN : ℕ)
    (get : ℕ → CC ℚ × ℚ) : SlpOp → Option (CC ℚ × ℚ)
  | .const re im deg =>
    let t := constBall re im deg
    some (t.c, t.r)
  | .action j =>
    if j < n then some (⟨centre.getD j 0, 0⟩, radius.getD j 0) else some ballZero
  | .char k => some (⟨0, 0⟩, WH.w ^ (k.map Int.natAbs).sum)
  | .add a₁ a₂ =>
    match get a₁, get a₂ with
    | (c₁, r₁), (c₂, r₂) =>
      let t := plusQ (⟨c₁, r₁⟩ : CertBall ℚ) ⟨c₂, r₂⟩
      some (t.c, t.r)
  | .mul a₁ a₂ =>
    match get a₁, get a₂ with
    | (c₁, r₁), (c₂, r₂) =>
      let t := timesQ (⟨c₁, r₁⟩ : CertBall ℚ) ⟨c₂, r₂⟩
      some (ballRound P (t.c, t.r))
  | .exp a =>
    match get a with
    | (c, r) => ballExp P c r (cexpHalvings c r) taylorN
  | .inv a =>
    match get a with
    | (c, r) =>
      let m := max |c.re| |c.im|
      if r < m then
        let d := c.re ^ 2 + c.im ^ 2
        some (ballRound P (⟨c.re / d, -c.im / d⟩, r / ((m - r) * m)))
      else none
  | .sqrt a =>
    match get a with
    | (c, r) => ballSqrt P c r

/-- Force a computed ball. The test on the denominators always holds; it makes the kernel
evaluate the three rationals of the ball at this step, so no deferred chain of rational
operations builds up across the program. -/
def ballForce : Option (CC ℚ × ℚ) → Option (CC ℚ × ℚ)
  | some b => if 0 < b.2.den + b.1.re.den + b.1.im.den then some b else none
  | none => none

/-- The ball of one operation, given the balls `acc` of the earlier slots, at the precision
`slpBallPrec`. -/
def ballStep (n : ℕ) (WH : CertWeight) (centre radius : List ℚ) (taylorN : ℕ)
    (acc : List (CC ℚ × ℚ)) (op : SlpOp) : Option (CC ℚ × ℚ) :=
  ballForce
    (ballStepG slpBallPrec n WH centre radius taylorN (fun a => acc.getD a ballZero) op)

/-- Slot `a` of the `k` balls stored in reverse order in `racc` (slots `k - 1, …, 0`). -/
def revGet (racc : List (CC ℚ × ℚ)) (k a : ℕ) : CC ℚ × ℚ :=
  if a < k then racc.getD (k - 1 - a) ballZero else ballZero

/-- The evaluated pass: the `k` earlier balls are kept in reverse order (`racc`), every new
ball is consed in front (no list copying), every operand ball is read once, and every ball is
forced (`ballForce`). Tail recursive in the operations. -/
def ballsRev (P n : ℕ) (WH : CertWeight) (centre radius : List ℚ) (taylorN : ℕ) :
    ℕ → List (CC ℚ × ℚ) → List SlpOp → Option (List (CC ℚ × ℚ))
  | _, racc, [] => some racc
  | k, racc, op :: ops =>
    match ballForce (ballStepG P n WH centre radius taylorN (revGet racc k) op) with
    | some b => ballsRev P n WH centre radius taylorN (k + 1) (b :: racc) ops
    | none => none

/-- The balls of the slots of the operations `ops` after the slots `acc`: `ballsRev` on the
reversed slots, reversed back once. -/
def ballsAux (n : ℕ) (WH : CertWeight) (centre radius : List ℚ) (taylorN : ℕ)
    (acc : List (CC ℚ × ℚ)) (ops : List SlpOp) : Option (List (CC ℚ × ℚ)) :=
  (ballsRev slpBallPrec n WH centre radius taylorN acc.length acc.reverse ops).map List.reverse

/-- Ball arithmetic of every slot on `D` (no embedding), in `ℚ`: `(centre, radius)` with
`|slot - centre| ≤ radius` on `D`. Constants exact up to the enclosure of `π`; actions
`(c_j, r_j)`; characters `(0, w_H^{|k|₁})`; sums and products; `exp` (also the compiled `sin`,
`cos`) via the range-reduced `ballExp` with the count `cexpHalvings c r` and Taylor order
`taylorN` on the operand ball `(c, r)`; `inv` fails (`none`) unless the operand ball excludes
`0`, i.e. `radius < max(|re|, |im|)` of its centre. Products, reciprocals and exponentials are
rounded outward to `slpBallPrec` significant bits (`ballRound`), which keeps the rational sizes
bounded. -/
def Slp.balls (n : ℕ) (p : Slp) (WH : CertWeight) (centre radius : List ℚ) (taylorN : ℕ) :
    Option (List (CC ℚ × ℚ)) :=
  ballsAux n WH centre radius taylorN [] p.ops

/-- The reference form of `ballsAux` (slots in order, `acc ++ [b]`), used in the proofs. -/
def ballsSpec (n : ℕ) (WH : CertWeight) (centre radius : List ℚ) (taylorN : ℕ) :
    List (CC ℚ × ℚ) → List SlpOp → Option (List (CC ℚ × ℚ))
  | acc, [] => some acc
  | acc, op :: ops =>
    (ballStep n WH centre radius taylorN acc op).bind fun b =>
      ballsSpec n WH centre radius taylorN (acc ++ [b]) ops

theorem revGet_reverse (acc : List (CC ℚ × ℚ)) :
    revGet acc.reverse acc.length = fun a => acc.getD a ballZero := by
  funext a
  unfold revGet
  split_ifs with ha
  · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_reverse (by omega)]
    congr 2
    omega
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    rfl

theorem ballsRev_eq {n : ℕ} {WH : CertWeight} {centre radius : List ℚ} {taylorN : ℕ}
    (ops : List SlpOp) : ∀ acc : List (CC ℚ × ℚ),
    ballsRev slpBallPrec n WH centre radius taylorN acc.length acc.reverse ops =
      (ballsSpec n WH centre radius taylorN acc ops).map List.reverse := by
  induction ops with
  | nil => intro acc; simp [ballsRev, ballsSpec]
  | cons op ops ih =>
    intro acc
    have e : ballForce (ballStepG slpBallPrec n WH centre radius taylorN
        (revGet acc.reverse acc.length) op) = ballStep n WH centre radius taylorN acc op := by
      rw [revGet_reverse]
      rfl
    rw [ballsRev, e, ballsSpec]
    cases ballStep n WH centre radius taylorN acc op with
    | none => rfl
    | some b =>
      have := ih (acc ++ [b])
      simp only [List.length_append, List.length_singleton, List.reverse_append,
        List.reverse_singleton, List.singleton_append] at this
      simpa using this

theorem ballsAux_eq_spec {n : ℕ} {WH : CertWeight} {centre radius : List ℚ} {taylorN : ℕ}
    (acc : List (CC ℚ × ℚ)) (ops : List SlpOp) :
    ballsAux n WH centre radius taylorN acc ops = ballsSpec n WH centre radius taylorN acc ops := by
  simp [ballsAux, ballsRev_eq, Option.map_map]

/-! ### Soundness of the slot balls -/

/-- The slot values `V` lie in the balls `acc`. -/
def BallRel (V : List ℂ) (acc : List (CC ℚ × ℚ)) : Prop :=
  V.length = acc.length ∧
    ∀ i, ‖V.getD i 0 - (acc.getD i ballZero).1.toC‖ ≤ ((acc.getD i ballZero).2 : ℝ)

theorem toC_zero_rat : CC.toC (⟨0, 0⟩ : CC ℚ) = 0 := by
  apply Complex.ext <;> simp [CC.toC, CertArith.val]

theorem toC_ratCast (q : ℚ) : CC.toC (⟨q, 0⟩ : CC ℚ) = ((q : ℝ) : ℂ) := by
  apply Complex.ext <;> simp [CC.toC, CertArith.val]

theorem ballZero_mem : ‖(0 : ℂ) - ballZero.1.toC‖ ≤ (ballZero.2 : ℝ) := by
  show ‖(0 : ℂ) - CC.toC (⟨0, 0⟩ : CC ℚ)‖ ≤ ((0 : ℚ) : ℝ)
  rw [toC_zero_rat]
  simp

theorem BallRel.ballRel_nil : BallRel [] [] := ⟨rfl, fun i => by simpa using ballZero_mem⟩

theorem BallRel.ballRel_snoc {V : List ℂ} {acc : List (CC ℚ × ℚ)} (h : BallRel V acc) {v : ℂ}
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

theorem ballForce_eq_some {o : Option (CC ℚ × ℚ)} {b : CC ℚ × ℚ}
    (h : ballForce o = some b) : o = some b := by
  cases o with
  | none => simp [ballForce] at h
  | some b₀ =>
    simp only [ballForce] at h
    split_ifs at h
    exact h

/-- Forcing a computed ball returns it. -/
theorem ballForce_some (b : CC ℚ × ℚ) : ballForce (some b) = some b := by
  have := b.2.den_pos
  simp only [ballForce]
  split_ifs with h
  · rfl
  · omega

/-- The ball of a character: `(0, w_H^{|k|₁})`. -/
theorem ballStep_char {n : ℕ} {WH : CertWeight} {centre radius : List ℚ} {taylorN : ℕ}
    (acc : List (CC ℚ × ℚ)) (k : CertKey) :
    ballStep n WH centre radius taylorN acc (.char k) =
      some (⟨0, 0⟩, WH.w ^ (k.map Int.natAbs).sum) := by
  simp only [ballStep, ballStepG]
  exact ballForce_some _

theorem ballStepG_sound {P n : ℕ} {WH : CertWeight} {s N : ℕ} (hW : checkWeight WH s N = true)
    {centre radius : List ℚ} {taylorN : ℕ} {z : (Fin n → ℂ) × (Fin n → ℂ)}
    (hz : z ∈ certDomain n WH.rho centre radius) {V : List ℂ} {get : ℕ → CC ℚ × ℚ}
    (hget : ∀ a, ‖V.getD a 0 - (get a).1.toC‖ ≤ ((get a).2 : ℝ)) {op : SlpOp}
    {b : CC ℚ × ℚ} (h : ballStepG P n WH centre radius taylorN get op = some b) :
    ‖op.step n z V - b.1.toC‖ ≤ (b.2 : ℝ) := by
  cases op with
  | const re im deg =>
    simp only [ballStepG, Option.some.injEq] at h
    subst h
    exact mem_constBall re im deg
  | action j =>
    simp only [ballStepG] at h
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
    simp only [ballStepG, Option.some.injEq] at h
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
  | add a₁ a₂ =>
    have h₁ := hget a₁
    have h₂ := hget a₂
    simp only [ballStepG] at h
    rcases hg₁ : get a₁ with ⟨c₁, r₁⟩
    rcases hg₂ : get a₂ with ⟨c₂, r₂⟩
    simp only [hg₁, hg₂, Option.some.injEq] at h h₁ h₂
    subst h
    have ht := CertBall.mem_plus (b₁ := ⟨c₁, r₁⟩) (b₂ := ⟨c₂, r₂⟩) h₁ h₂
    rw [← plusQ_eq] at ht
    exact ht
  | mul a₁ a₂ =>
    have h₁ := hget a₁
    have h₂ := hget a₂
    simp only [ballStepG] at h
    rcases hg₁ : get a₁ with ⟨c₁, r₁⟩
    rcases hg₂ : get a₂ with ⟨c₂, r₂⟩
    simp only [hg₁, hg₂, Option.some.injEq] at h h₁ h₂
    subst h
    have ht := CertBall.mem_times (b₁ := ⟨c₁, r₁⟩) (b₂ := ⟨c₂, r₂⟩) h₁ h₂
    rw [← timesQ_eq] at ht
    exact ballRound_mem _ ht
  | exp a =>
    have ha := hget a
    simp only [ballStepG] at h
    rcases hg : get a with ⟨c, r⟩
    simp only [hg] at h ha
    exact ballExp_sound P h ha
  | inv a =>
    have hmem := hget a
    simp only [ballStepG] at h
    rcases hg : get a with ⟨c, r⟩
    simp only [hg] at h hmem
    split_ifs at h with hlt
    simp only [Option.some.injEq] at h
    subst h
    simp only [SlpOp.step]
    refine ballRound_mem _ ?_
    have hlt' : (r : ℝ) < max |(c.re : ℝ)| |(c.im : ℝ)| := by exact_mod_cast hlt
    have hmc : max |(c.re : ℝ)| |(c.im : ℝ)| ≤ ‖c.toC‖ := by
      refine max_le ?_ ?_
      · exact Complex.abs_re_le_norm c.toC
      · exact Complex.abs_im_le_norm c.toC
    obtain ⟨-, hb⟩ := inv_ball_bound hlt' hmc hmem
    have hc : c.toC⁻¹ = CC.toC (⟨c.re / (c.re ^ 2 + c.im ^ 2),
        -c.im / (c.re ^ 2 + c.im ^ 2)⟩ : CC ℚ) := by
      apply Complex.ext <;>
        simp [CC.toC, CertArith.val, Complex.inv_re, Complex.inv_im,
          Complex.normSq_apply, sq, neg_div]
    rw [← hc]
    convert hb using 1
    push_cast
    rfl
  | sqrt a =>
    have ha := hget a
    simp only [ballStepG] at h
    rcases hg : get a with ⟨c, r⟩
    simp only [hg] at h ha
    exact ballSqrt_sound P h ha

theorem ballStep_sound {n : ℕ} {WH : CertWeight} {s N : ℕ} (hW : checkWeight WH s N = true)
    {centre radius : List ℚ} {taylorN : ℕ} {z : (Fin n → ℂ) × (Fin n → ℂ)}
    (hz : z ∈ certDomain n WH.rho centre radius) {V : List ℂ} {acc : List (CC ℚ × ℚ)}
    (hR : BallRel V acc) {op : SlpOp} {b : CC ℚ × ℚ}
    (h : ballStep n WH centre radius taylorN acc op = some b) :
    ‖op.step n z V - b.1.toC‖ ≤ (b.2 : ℝ) := by
  exact ballStepG_sound hW hz (get := fun a => acc.getD a ballZero) hR.2 (ballForce_eq_some h)

theorem ballsSpec_sound {n : ℕ} {WH : CertWeight} {s N : ℕ} (hW : checkWeight WH s N = true)
    {centre radius : List ℚ} {taylorN : ℕ} {z : (Fin n → ℂ) × (Fin n → ℂ)}
    (hz : z ∈ certDomain n WH.rho centre radius) (ops : List SlpOp) :
    ∀ (V : List ℂ) (acc bs : List (CC ℚ × ℚ)), BallRel V acc →
      ballsSpec n WH centre radius taylorN acc ops = some bs →
      BallRel (ops.foldl (fun acc op => acc ++ [op.step n z acc]) V) bs := by
  induction ops with
  | nil =>
    intro V acc bs hR h
    simp only [ballsSpec, Option.some.injEq] at h
    subst h
    exact hR
  | cons op ops ih =>
    intro V acc bs hR h
    simp only [ballsSpec, Option.bind_eq_some_iff] at h
    obtain ⟨b, hb, h⟩ := h
    exact ih _ _ _ (hR.ballRel_snoc (ballStep_sound hW hz hR hb)) h

theorem ballsAux_sound {n : ℕ} {WH : CertWeight} {s N : ℕ} (hW : checkWeight WH s N = true)
    {centre radius : List ℚ} {taylorN : ℕ} {z : (Fin n → ℂ) × (Fin n → ℂ)}
    (hz : z ∈ certDomain n WH.rho centre radius) (ops : List SlpOp) :
    ∀ (V : List ℂ) (acc bs : List (CC ℚ × ℚ)), BallRel V acc →
      ballsAux n WH centre radius taylorN acc ops = some bs →
      BallRel (ops.foldl (fun acc op => acc ++ [op.step n z acc]) V) bs := by
  intro V acc bs hR h
  rw [ballsAux_eq_spec] at h
  exact ballsSpec_sound hW hz ops V acc bs hR h

theorem Slp.val_mem_ball {n : ℕ} (p : Slp) {WH : CertWeight} {s N : ℕ}
    (hW : checkWeight WH s N = true) {centre radius : List ℚ} {taylorN : ℕ}
    {bs : List (CC ℚ × ℚ)} (h : p.balls n WH centre radius taylorN = some bs)
    {z : (Fin n → ℂ) × (Fin n → ℂ)} (hz : z ∈ certDomain n WH.rho centre radius) (i : ℕ)
    (hi : i < bs.length) :
    ‖p.val n z i - (bs.getD i (⟨0, 0⟩, 0)).1.toC‖ ≤ (bs.getD i (⟨0, 0⟩, 0)).2 :=
  have _ := hi
  (ballsAux_sound hW hz p.ops [] [] bs BallRel.ballRel_nil h).2 i

/-! ### Certified denominators -/

/-- A successful `inv` step certifies its operand ball away from `0`. -/
theorem ballStep_inv_lt {n : ℕ} {WH : CertWeight} {centre radius : List ℚ} {taylorN : ℕ}
    {acc : List (CC ℚ × ℚ)} {a : ℕ} {b : CC ℚ × ℚ}
    (h : ballStep n WH centre radius taylorN acc (.inv a) = some b) :
    (acc.getD a ballZero).2 < max |(acc.getD a ballZero).1.re| |(acc.getD a ballZero).1.im| := by
  have h₀ := ballForce_eq_some h
  simp only [ballStepG] at h₀
  rcases hx : acc.getD a ballZero with ⟨c, r⟩
  simp only [hx] at h₀
  split_ifs at h₀ with hlt
  exact hlt

theorem ballsSpec_prefix_inv {n : ℕ} {WH : CertWeight} {centre radius : List ℚ} {taylorN : ℕ}
    (ops : List SlpOp) :
    ∀ (acc bs : List (CC ℚ × ℚ)), ballsSpec n WH centre radius taylorN acc ops = some bs →
      acc <+: bs ∧ ∀ j a : ℕ, ops[j]? = some (SlpOp.inv a) →
        (bs.getD a ballZero).2 < max |(bs.getD a ballZero).1.re| |(bs.getD a ballZero).1.im| := by
  induction ops with
  | nil =>
    intro acc bs h
    simp only [ballsSpec, Option.some.injEq] at h
    subst h
    exact ⟨List.prefix_refl _, fun j a hj => by simp at hj⟩
  | cons op ops ih =>
    intro acc bs h
    simp only [ballsSpec, Option.bind_eq_some_iff] at h
    obtain ⟨b, hb, h⟩ := h
    obtain ⟨hp, hinv⟩ := ih _ _ h
    refine ⟨(List.prefix_append acc [b]).trans hp, fun j a hj => ?_⟩
    cases j with
    | succ j => exact hinv j a hj
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
      subst hj
      have hlt := ballStep_inv_lt hb
      by_cases ha : a < acc.length
      · obtain ⟨t, ht⟩ := (List.prefix_append acc [b]).trans hp
        rw [← ht, List.getD_eq_getElem?_getD, List.getElem?_append_left ha,
          ← List.getD_eq_getElem?_getD]
        exact hlt
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)] at hlt
        simp [ballZero] at hlt

theorem ballsAux_prefix_inv {n : ℕ} {WH : CertWeight} {centre radius : List ℚ} {taylorN : ℕ}
    (ops : List SlpOp) :
    ∀ (acc bs : List (CC ℚ × ℚ)), ballsAux n WH centre radius taylorN acc ops = some bs →
      acc <+: bs ∧ ∀ j a : ℕ, ops[j]? = some (SlpOp.inv a) →
        (bs.getD a ballZero).2 < max |(bs.getD a ballZero).1.re| |(bs.getD a ballZero).1.im| := by
  intro acc bs h
  rw [ballsAux_eq_spec] at h
  exact ballsSpec_prefix_inv ops acc bs h

/-- A successful `sqrt` step certifies its operand ball in the right half-plane. -/
theorem ballStep_sqrt_lt {n : ℕ} {WH : CertWeight} {centre radius : List ℚ} {taylorN : ℕ}
    {acc : List (CC ℚ × ℚ)} {a : ℕ} {b : CC ℚ × ℚ}
    (h : ballStep n WH centre radius taylorN acc (.sqrt a) = some b) :
    (acc.getD a ballZero).2 < (acc.getD a ballZero).1.re := by
  have h₀ := ballForce_eq_some h
  simp only [ballStepG] at h₀
  rcases hx : acc.getD a ballZero with ⟨c, r⟩
  simp only [hx] at h₀
  exact ballSqrt_lt_re h₀

theorem ballsSpec_prefix_sqrt {n : ℕ} {WH : CertWeight} {centre radius : List ℚ} {taylorN : ℕ}
    (ops : List SlpOp) :
    ∀ (acc bs : List (CC ℚ × ℚ)), ballsSpec n WH centre radius taylorN acc ops = some bs →
      acc <+: bs ∧ ∀ j a : ℕ, ops[j]? = some (SlpOp.sqrt a) →
        (bs.getD a ballZero).2 < (bs.getD a ballZero).1.re := by
  induction ops with
  | nil =>
    intro acc bs h
    simp only [ballsSpec, Option.some.injEq] at h
    subst h
    exact ⟨List.prefix_refl _, fun j a hj => by simp at hj⟩
  | cons op ops ih =>
    intro acc bs h
    simp only [ballsSpec, Option.bind_eq_some_iff] at h
    obtain ⟨b, hb, h⟩ := h
    obtain ⟨hp, hsq⟩ := ih _ _ h
    refine ⟨(List.prefix_append acc [b]).trans hp, fun j a hj => ?_⟩
    cases j with
    | succ j => exact hsq j a hj
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
      subst hj
      have hlt := ballStep_sqrt_lt hb
      by_cases ha : a < acc.length
      · obtain ⟨t, ht⟩ := (List.prefix_append acc [b]).trans hp
        rw [← ht, List.getD_eq_getElem?_getD, List.getElem?_append_left ha,
          ← List.getD_eq_getElem?_getD]
        exact hlt
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)] at hlt
        simp [ballZero] at hlt

theorem ballsAux_prefix_sqrt {n : ℕ} {WH : CertWeight} {centre radius : List ℚ} {taylorN : ℕ}
    (ops : List SlpOp) :
    ∀ (acc bs : List (CC ℚ × ℚ)), ballsAux n WH centre radius taylorN acc ops = some bs →
      acc <+: bs ∧ ∀ j a : ℕ, ops[j]? = some (SlpOp.sqrt a) →
        (bs.getD a ballZero).2 < (bs.getD a ballZero).1.re := by
  intro acc bs h
  rw [ballsAux_eq_spec] at h
  exact ballsSpec_prefix_sqrt ops acc bs h

/-- Every `inv` operation of `ops` has an operand that is nonzero at every point of `S`. -/
def SlpInvGood (n : ℕ) (S : Set ((Fin n → ℂ) × (Fin n → ℂ))) (ops : List SlpOp) : Prop :=
  ∀ j a : ℕ, ops[j]? = some (SlpOp.inv a) → ∀ z ∈ S, (Slp.vals n z ops).getD a 0 ≠ 0

/-- Successful ball arithmetic certifies every `inv` operand on `D`. -/
theorem Slp.invGood_of_balls {n : ℕ} (p : Slp) {WH : CertWeight} {s N : ℕ}
    (hW : checkWeight WH s N = true) {centre radius : List ℚ} {taylorN : ℕ}
    {bs : List (CC ℚ × ℚ)} (h : p.balls n WH centre radius taylorN = some bs) :
    SlpInvGood n (certDomain n WH.rho centre radius) p.ops := by
  intro j a hj z hz
  obtain ⟨-, hinv⟩ := ballsAux_prefix_inv p.ops [] bs h
  have hlt := hinv j a hj
  have ha : a < bs.length := by
    by_contra hna
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)] at hlt
    simp [ballZero] at hlt
  have hmem := Slp.val_mem_ball p hW h hz a ha
  set x := bs.getD a ballZero with hx
  have hmem' : ‖Slp.val n p z a - x.1.toC‖ ≤ (x.2 : ℝ) := hmem
  have hlt' : (x.2 : ℝ) < max |(x.1.re : ℝ)| |(x.1.im : ℝ)| := by exact_mod_cast hlt
  have hmc : max |(x.1.re : ℝ)| |(x.1.im : ℝ)| ≤ ‖x.1.toC‖ :=
    max_le (Complex.abs_re_le_norm x.1.toC) (Complex.abs_im_le_norm x.1.toC)
  exact (inv_ball_bound hlt' hmc hmem').1

/-- Every `sqrt` operation of `ops` has an operand with positive real part at every point of `S`. -/
def SlpSqrtGood (n : ℕ) (S : Set ((Fin n → ℂ) × (Fin n → ℂ))) (ops : List SlpOp) : Prop :=
  ∀ j a : ℕ, ops[j]? = some (SlpOp.sqrt a) → ∀ z ∈ S, 0 < ((Slp.vals n z ops).getD a 0).re

/-- Successful ball arithmetic certifies every `sqrt` operand on `D`. -/
theorem Slp.sqrtGood_of_balls {n : ℕ} (p : Slp) {WH : CertWeight} {s N : ℕ}
    (hW : checkWeight WH s N = true) {centre radius : List ℚ} {taylorN : ℕ}
    {bs : List (CC ℚ × ℚ)} (h : p.balls n WH centre radius taylorN = some bs) :
    SlpSqrtGood n (certDomain n WH.rho centre radius) p.ops := by
  intro j a hj z hz
  obtain ⟨-, hsq⟩ := ballsAux_prefix_sqrt p.ops [] bs h
  have hlt := hsq j a hj
  have ha : a < bs.length := by
    by_contra hna
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)] at hlt
    simp [ballZero] at hlt
  have hmem := Slp.val_mem_ball p hW h hz a ha
  exact re_pos_of_ball hlt hmem

variable {n : ℕ}

local notation "Ph" => (Fin n → ℂ) × (Fin n → ℂ)

theorem jetSmoothOn_empty (f : Ph → ℂ) : JetSmoothOn (∅ : Set Ph) f := contDiffOn_empty

theorem slpMulO_prefix_self (s : List SlpOp) (a b : Option ℕ) : s <+: (slpMulO s a b).1 := by
  cases a <;> cases b <;> simp [slpMulO, slpEmit]

theorem slpInvPre_emit_prefix (s : List SlpOp) (A : SlpNode) :
    s ++ [SlpOp.inv A.v] <+: (slpInvPre s A).1 :=
  (slpMulO_prefix_self _ _ _).trans ((slpMulO_prefix_self _ _ _).trans
    (slpMulO_prefix_self _ _ _))

theorem slpInvNode_emit_prefix {S : Set Ph} (hS : IsOpen S) {f : Ph → ℂ}
    (hf : JetSmoothOn S f) (h0 : ∀ z ∈ S, f z ≠ 0) {s : List SlpOp} {A : SlpNode}
    (hA : A.Sound n S f s) : s ++ [SlpOp.inv A.v] <+: (slpInvNode n s A).1 := by
  obtain ⟨hp, hvlt, hval, hw2, hw3, hw4⟩ := slpInvPre_spec hA
  obtain ⟨p, -⟩ := slpInvTail_sound hS hf h0 (hA.mono hp) hvlt hval hw2 hw3 hw4
  exact (slpInvPre_emit_prefix s A).trans p

/-- Inverse and square-root safety of a program containing the compiled expression certify the
domain conditions of the expression. -/
theorem HamExpr.nonvanishingOn_of_program_good {D : Set Ph} (hD : IsOpen D) (e : HamExpr n) :
    ∀ (s ops : List SlpOp), (slpCompile e s).1 <+: ops → SlpInvGood n D ops →
      SlpSqrtGood n D ops → e.NonvanishingOn D := by
  induction e with
  | const q => intros; trivial
  | pi => intros; trivial
  | action j => intros; trivial
  | cosMode k => intros; trivial
  | sinMode k => intros; trivial
  | add a b iha ihb =>
    intro s ops hp hg hq
    obtain ⟨p1, h1⟩ := slpCompile_sound a isOpen_empty a.nonvanishingOn_empty s
    obtain ⟨p2, h2⟩ := slpCompile_sound b isOpen_empty b.nonvanishingOn_empty (slpCompile a s).1
    obtain ⟨p3, -⟩ := slpAddNode_sound isOpen_empty (jetSmoothOn_empty _) (jetSmoothOn_empty _)
      (h1.mono p2) h2
    exact ⟨iha s ops ((p2.trans p3).trans hp) hg hq, ihb _ ops (p3.trans hp) hg hq⟩
  | mul a b iha ihb =>
    intro s ops hp hg hq
    obtain ⟨p1, h1⟩ := slpCompile_sound a isOpen_empty a.nonvanishingOn_empty s
    obtain ⟨p2, h2⟩ := slpCompile_sound b isOpen_empty b.nonvanishingOn_empty (slpCompile a s).1
    obtain ⟨p3, -⟩ := slpMulNode_sound isOpen_empty (jetSmoothOn_empty _) (jetSmoothOn_empty _)
      (h1.mono p2) h2
    exact ⟨iha s ops ((p2.trans p3).trans hp) hg hq, ihb _ ops (p3.trans hp) hg hq⟩
  | div a b iha ihb =>
    intro s ops hp hg hq
    obtain ⟨p1, h1⟩ := slpCompile_sound a isOpen_empty a.nonvanishingOn_empty s
    obtain ⟨p2, h2⟩ := slpCompile_sound b isOpen_empty b.nonvanishingOn_empty (slpCompile a s).1
    have h2' := slpInvNode_sound isOpen_empty (jetSmoothOn_empty _) (fun z hz => absurd hz
      (Set.notMem_empty z)) h2
    have hemit := slpInvNode_emit_prefix isOpen_empty (jetSmoothOn_empty _)
      (fun z hz => absurd hz (Set.notMem_empty z)) h2
    obtain ⟨p3, -⟩ := slpMulNode_sound isOpen_empty (jetSmoothOn_empty _) (jetSmoothOn_empty _)
      ((h1.mono p2).mono h2'.1) h2'.2
    have hp' : (slpInvNode n (slpCompile b (slpCompile a s).1).1
        (slpCompile b (slpCompile a s).1).2).1 <+: ops :=
      p3.trans hp
    have hA := iha s ops (p2.trans (h2'.1.trans p3) |>.trans hp) hg hq
    have hB := ihb _ ops ((h2'.1).trans hp') hg hq
    refine ⟨hA, hB, fun z hz => ?_⟩
    obtain ⟨hpb, hb⟩ := slpCompile_sound b hD hB (slpCompile a s).1
    have hget : ops[(slpCompile b (slpCompile a s).1).1.length]? =
        some (SlpOp.inv (slpCompile b (slpCompile a s).1).2.v) := by
      obtain ⟨t, ht⟩ := hemit.trans hp'
      rw [← ht, List.getElem?_append_left (by simp)]
      simp
    have hne := hg _ _ hget z hz
    obtain ⟨t, ht⟩ := hemit.trans hp'
    have e : ops = (slpCompile b (slpCompile a s).1).1 ++ ([SlpOp.inv
        (slpCompile b (slpCompile a s).1).2.v] ++ t) := by rw [← ht]; simp
    rw [e, Slp.val_append n z _ _ hb.v_lt, hb.val z] at hne
    exact hne
  | pow a m iha =>
    intro s ops hp hg hq
    obtain ⟨p1, h1⟩ := slpCompile_sound a isOpen_empty a.nonvanishingOn_empty s
    obtain ⟨p2, -⟩ := slpPowNode_sound isOpen_empty (jetSmoothOn_empty _) h1 m
    exact iha s ops (p2.trans hp) hg hq
  | exp a iha =>
    intro s ops hp hg hq
    obtain ⟨p1, h1⟩ := slpCompile_sound a isOpen_empty a.nonvanishingOn_empty s
    obtain ⟨p2, -⟩ := slpExpNode_sound isOpen_empty (jetSmoothOn_empty _) h1
    exact iha s ops (p2.trans hp) hg hq
  | sin a iha =>
    intro s ops hp hg hq
    obtain ⟨p1, h1⟩ := slpCompile_sound a isOpen_empty a.nonvanishingOn_empty s
    obtain ⟨p2, -⟩ := slpTrigNode_sound isOpen_empty (jetSmoothOn_empty _) h1 0 (-1 / 2) 0 (1 / 2)
    exact iha s ops (p2.trans hp) hg hq
  | cos a iha =>
    intro s ops hp hg hq
    obtain ⟨p1, h1⟩ := slpCompile_sound a isOpen_empty a.nonvanishingOn_empty s
    obtain ⟨p2, -⟩ := slpTrigNode_sound isOpen_empty (jetSmoothOn_empty _) h1 (1 / 2) 0 (1 / 2) 0
    exact iha s ops (p2.trans hp) hg hq
  | sqrt a iha =>
    intro s ops hp hg hq
    obtain ⟨-, h1⟩ := slpCompile_sound a isOpen_empty a.nonvanishingOn_empty s
    have hemit := slpSqrtNode_emit_prefix isOpen_empty (jetSmoothOn_empty _)
      (fun z hz => absurd hz (Set.notMem_empty z)) h1
    have hp' : (slpSqrtNode n (slpCompile a s).1 (slpCompile a s).2).1 <+: ops := hp
    have hA := iha s ops ((List.prefix_append _ _).trans (hemit.trans hp')) hg hq
    refine ⟨hA, fun z hz => ?_⟩
    obtain ⟨-, ha⟩ := slpCompile_sound a hD hA s
    have hget : ops[(slpCompile a s).1.length]? = some (SlpOp.sqrt (slpCompile a s).2.v) := by
      obtain ⟨t, ht⟩ := hemit.trans hp'
      rw [← ht, List.getElem?_append_left (by simp)]
      simp
    have hpos := hq _ _ hget z hz
    obtain ⟨t, ht⟩ := hemit.trans hp'
    have e : ops = (slpCompile a s).1 ++ ([SlpOp.sqrt (slpCompile a s).2.v] ++ t) := by
      rw [← ht]; simp
    rw [e, Slp.val_append n z _ _ ha.v_lt, ha.val z] at hpos
    exact hpos

/-- Successful ball arithmetic on the jet program certifies every denominator and every
square-root operand on `D`. -/
theorem HamExpr.nonvanishingOn_of_balls {n : ℕ} (e : HamExpr n) {WH : CertWeight} {s N : ℕ}
    (hW : checkWeight WH s N = true) {centre radius : List ℚ} {taylorN : ℕ}
    {bs : List (CC ℚ × ℚ)} (h : e.jet.prog.balls n WH centre radius taylorN = some bs) :
    e.NonvanishingOn (certDomain n WH.rho centre radius) :=
  HamExpr.nonvanishingOn_of_program_good (isOpen_certDomain n WH.rho centre radius) e
    [.const 0 0 0] e.jet.prog.ops (List.prefix_refl _) (Slp.invGood_of_balls e.jet.prog hW h)
    (Slp.sqrtGood_of_balls e.jet.prog hW h)

end KAM.Certificate

end
