/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Certificate.Arith.Interface
public import KAM.Certificate.Arith.PiHigh
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Root enclosures and the scalar complex exponential ball

* `checkRootEnclosure m d lo hi`: a rational check that `[lo, hi]` encloses `d ^ (1 / m)`.
* `CertBall α`: a complex ball `‖w - c.toC‖ ≤ val r` with backend centre and radius, with sound
  addition and multiplication (`CertBall.plus`, `CertBall.times`) and rational constants.
* `certCExp z zRad N`: a ball enclosing `exp w` for every `w` within `zRad` of `z`, by a Taylor
  sum of order `N + 1` evaluated in ball arithmetic plus the `Complex.exp_bound` remainder.

**Design signal (finding).** The signed statement `certCExp_sound` (no size hypothesis on
`z`, `zRad`) cannot hold for any definition built from the interface operations: for `N = 0`
the output is a bounded-depth computation, which cannot dominate `exp (val zRad)` as
`val zRad → ∞` (take `α = ℚ`). Here the soundness theorem is `certCExp_sound_of_small`, with the
size hypothesis `‖z.toC‖ + val zRad ≤ 1` (the Taylor remainder of `Complex.exp_bound` needs
`‖w‖ ≤ 1`), together with the backend test `certCExpSmall` that discharges it.
-/

@[expose] public section

namespace KAM.Certificate

open CertArith

/-! ### Root enclosures -/

/-- `0 ≤ lo`, `lo^m ≤ d ≤ hi^m`, `0 ≤ hi`: encloses the real `m`-th root of `d`. -/
def checkRootEnclosure (m d : ℕ) (lo hi : ℚ) : Bool :=
  decide (0 ≤ lo) && decide (lo ^ m ≤ (d : ℚ)) && decide ((d : ℚ) ≤ hi ^ m) && decide (0 ≤ hi)

theorem rpow_mem_of_checkRootEnclosure {m d : ℕ} {lo hi : ℚ} (hm : 0 < m)
    (h : checkRootEnclosure m d lo hi = true) :
    (lo : ℝ) ≤ (d : ℝ) ^ ((1 : ℝ) / m) ∧ (d : ℝ) ^ ((1 : ℝ) / m) ≤ hi := by
  simp only [checkRootEnclosure, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ := h
  have hm' : m ≠ 0 := hm.ne'
  have e1 : (lo : ℝ) = ((lo : ℝ) ^ m) ^ ((m : ℝ)⁻¹) :=
    (Real.pow_rpow_inv_natCast (by exact_mod_cast h0) hm').symm
  have e2 : (hi : ℝ) = ((hi : ℝ) ^ m) ^ ((m : ℝ)⁻¹) :=
    (Real.pow_rpow_inv_natCast (by exact_mod_cast h3) hm').symm
  have f1 : (lo : ℝ) ^ m ≤ d := by exact_mod_cast h1
  have f2 : (d : ℝ) ≤ (hi : ℝ) ^ m := by exact_mod_cast h2
  have hinv : (0 : ℝ) ≤ (m : ℝ)⁻¹ := by positivity
  rw [one_div]
  constructor
  · rw [e1]
    exact Real.rpow_le_rpow (by positivity) f1 hinv
  · rw [e2]
    exact Real.rpow_le_rpow (by positivity) f2 hinv

theorem sqrt_mem_of_checkRootEnclosure {d : ℕ} {lo hi : ℚ}
    (h : checkRootEnclosure 2 d lo hi = true) :
    (lo : ℝ) ≤ Real.sqrt d ∧ Real.sqrt d ≤ hi := by
  have := rpow_mem_of_checkRootEnclosure (by norm_num) h
  rw [Real.sqrt_eq_rpow]
  simpa using this

/-! ### Ball arithmetic on `ℂ` -/

/-- A complex ball with backend centre and radius. -/
structure CertBall (α : Type) where
  c : CC α
  r : α

/-- The ball contains `w`. -/
def CertBall.Mem {α : Type} [CertArith α] (w : ℂ) (b : CertBall α) : Prop :=
  ‖w - b.c.toC‖ ≤ val b.r

/-- An upper bound of `‖c.toC‖`. -/
def CC.normUp {α : Type} [CertArith α] (c : CC α) : α := upAdd (abs c.re) (abs c.im)

theorem CC.norm_le_normUp {α : Type} [CertArith α] [LawfulCertArith α] (c : CC α) :
    ‖c.toC‖ ≤ val c.normUp := by
  have h1 := LawfulCertArith.upAdd_ge (abs c.re) (abs c.im)
  rw [LawfulCertArith.val_abs, LawfulCertArith.val_abs] at h1
  exact (Complex.norm_le_abs_re_add_abs_im _).trans h1

theorem CC.normUp_nonneg {α : Type} [CertArith α] [LawfulCertArith α] (c : CC α) :
    0 ≤ val c.normUp := (norm_nonneg _).trans (CC.norm_le_normUp c)

theorem norm_le_of_re_im {z : ℂ} {A B : ℝ} (hA : |z.re| ≤ A) (hB : |z.im| ≤ B) : ‖z‖ ≤ A + B :=
  (Complex.norm_le_abs_re_add_abs_im z).trans (add_le_add hA hB)

namespace CertBall

variable {α : Type} [CertArith α]

/-- The rational constant `q`: centre `ofRatUp q`, radius an upper bound of
`ofRatUp q - ofRatDown q`. -/
def ofRat (q : ℚ) : CertBall α :=
  ⟨⟨ofRatUp q, ofInt 0⟩, upAdd (add (ofRatUp q) (neg (ofRatDown q)))
    (addErr (ofRatUp q) (neg (ofRatDown q)))⟩

/-- The constant `1`. -/
def one : CertBall α := ⟨⟨ofInt 1, ofInt 0⟩, ofInt 0⟩

/-- Sum of balls. -/
def plus (b₁ b₂ : CertBall α) : CertBall α :=
  ⟨⟨CertArith.add b₁.c.re b₂.c.re, CertArith.add b₁.c.im b₂.c.im⟩,
    upAdd (upAdd b₁.r b₂.r) (upAdd (addErr b₁.c.re b₂.c.re) (addErr b₁.c.im b₂.c.im))⟩

/-- Rounding error of the real part of a product (upper bound). -/
def mulReErr (a b c d : α) : α :=
  upAdd (upAdd (addErr (mul a c) (neg (mul b d))) (mulErr a c)) (mulErr b d)

/-- Rounding error of the imaginary part of a product (upper bound). -/
def mulImErr (a b c d : α) : α :=
  upAdd (upAdd (addErr (mul a d) (mul b c)) (mulErr a d)) (mulErr b c)

/-- Product of balls. -/
def times (b₁ b₂ : CertBall α) : CertBall α :=
  let a := b₁.c.re
  let b := b₁.c.im
  let c := b₂.c.re
  let d := b₂.c.im
  ⟨⟨CertArith.add (CertArith.mul a c) (neg (CertArith.mul b d)),
      CertArith.add (CertArith.mul a d) (CertArith.mul b c)⟩,
    upAdd (upAdd (upMul b₁.r (upAdd b₂.c.normUp b₂.r)) (upMul b₁.c.normUp b₂.r))
      (upAdd (mulReErr a b c d) (mulImErr a b c d))⟩

variable [LawfulCertArith α]

theorem mem_ofRat (q : ℚ) : Mem (q : ℂ) (ofRat (α := α) q) := by
  have h1 := LawfulCertArith.ofRatUp_ge (α := α) q
  have h2 := LawfulCertArith.ofRatDown_le (α := α) q
  have h3 := LawfulCertArith.add_err (ofRatUp q) (neg (ofRatDown (α := α) q))
  have h4 := LawfulCertArith.upAdd_ge (add (ofRatUp q) (neg (ofRatDown q)))
    (addErr (ofRatUp q) (neg (ofRatDown (α := α) q)))
  rw [LawfulCertArith.val_neg] at h3
  rw [abs_le] at h3
  have hz : (q : ℂ) - (ofRat (α := α) q).c.toC = ((q : ℝ) - val (ofRatUp (α := α) q) : ℝ) := by
    apply Complex.ext <;> simp [ofRat, CC.toC, LawfulCertArith.val_ofInt]
  unfold Mem
  rw [hz, Complex.norm_real, Real.norm_eq_abs, abs_le]
  constructor <;> simp only [ofRat] <;> linarith [h3.1, h3.2]

theorem mem_one : Mem (1 : ℂ) (one (α := α)) := by
  have hz : (1 : ℂ) - (one (α := α)).c.toC = 0 := by
    apply Complex.ext <;> simp [one, CC.toC, LawfulCertArith.val_ofInt]
  unfold Mem
  rw [hz]
  simp [one, LawfulCertArith.val_ofInt]

theorem mem_plus {w₁ w₂ : ℂ} {b₁ b₂ : CertBall α} (h₁ : Mem w₁ b₁) (h₂ : Mem w₂ b₂) :
    Mem (w₁ + w₂) (plus b₁ b₂) := by
  have e1 := LawfulCertArith.add_err b₁.c.re b₂.c.re
  have e2 := LawfulCertArith.add_err b₁.c.im b₂.c.im
  have u1 := LawfulCertArith.upAdd_ge b₁.r b₂.r
  have u2 := LawfulCertArith.upAdd_ge (addErr b₁.c.re b₂.c.re) (addErr b₁.c.im b₂.c.im)
  have u3 := LawfulCertArith.upAdd_ge (upAdd b₁.r b₂.r)
    (upAdd (addErr b₁.c.re b₂.c.re) (addErr b₁.c.im b₂.c.im))
  have hc : ‖(b₁.c.toC + b₂.c.toC) - (plus b₁ b₂).c.toC‖ ≤
      val (addErr b₁.c.re b₂.c.re) + val (addErr b₁.c.im b₂.c.im) := by
    apply norm_le_of_re_im
    · simp only [Complex.sub_re, Complex.add_re, plus, CC.toC]
      rw [abs_sub_comm]; exact e1
    · simp only [Complex.sub_im, Complex.add_im, plus, CC.toC]
      rw [abs_sub_comm]; exact e2
  have : w₁ + w₂ - (plus b₁ b₂).c.toC =
      (w₁ - b₁.c.toC) + (w₂ - b₂.c.toC) + ((b₁.c.toC + b₂.c.toC) - (plus b₁ b₂).c.toC) := by ring
  unfold Mem at *
  rw [this]
  have hr : val (plus b₁ b₂).r = val (upAdd (upAdd b₁.r b₂.r)
      (upAdd (addErr b₁.c.re b₂.c.re) (addErr b₁.c.im b₂.c.im))) := rfl
  rw [hr]
  have n2 := norm_add_le (w₁ - b₁.c.toC) (w₂ - b₂.c.toC)
  have n3 := norm_add_le ((w₁ - b₁.c.toC) + (w₂ - b₂.c.toC))
    ((b₁.c.toC + b₂.c.toC) - (plus b₁ b₂).c.toC)
  linarith

theorem mulReErr_bound (a b c d : α) :
    |val (CertArith.add (CertArith.mul a c) (neg (CertArith.mul b d))) -
      (val a * val c - val b * val d)| ≤ val (mulReErr a b c d) := by
  have e1 := LawfulCertArith.add_err (CertArith.mul a c) (neg (CertArith.mul b d))
  have e2 := LawfulCertArith.mul_err a c
  have e3 := LawfulCertArith.mul_err b d
  have n := LawfulCertArith.val_neg (CertArith.mul b d)
  have u1 := LawfulCertArith.upAdd_ge (addErr (CertArith.mul a c) (neg (CertArith.mul b d)))
    (mulErr a c)
  have u2 := LawfulCertArith.upAdd_ge (upAdd (addErr (CertArith.mul a c)
    (neg (CertArith.mul b d))) (mulErr a c)) (mulErr b d)
  rw [n] at e1
  rw [abs_le] at e1 e2 e3 ⊢
  unfold mulReErr
  constructor <;> linarith [e1.1, e1.2, e2.1, e2.2, e3.1, e3.2]

theorem mulImErr_bound (a b c d : α) :
    |val (CertArith.add (CertArith.mul a d) (CertArith.mul b c)) -
      (val a * val d + val b * val c)| ≤ val (mulImErr a b c d) := by
  have e1 := LawfulCertArith.add_err (CertArith.mul a d) (CertArith.mul b c)
  have e2 := LawfulCertArith.mul_err a d
  have e3 := LawfulCertArith.mul_err b c
  have u1 := LawfulCertArith.upAdd_ge (addErr (CertArith.mul a d) (CertArith.mul b c))
    (mulErr a d)
  have u2 := LawfulCertArith.upAdd_ge (upAdd (addErr (CertArith.mul a d)
    (CertArith.mul b c)) (mulErr a d)) (mulErr b c)
  rw [abs_le] at e1 e2 e3 ⊢
  unfold mulImErr
  constructor <;> linarith [e1.1, e1.2, e2.1, e2.2, e3.1, e3.2]

theorem mem_times {w₁ w₂ : ℂ} {b₁ b₂ : CertBall α} (h₁ : Mem w₁ b₁) (h₂ : Mem w₂ b₂) :
    Mem (w₁ * w₂) (times b₁ b₂) := by
  have hr1 : 0 ≤ val b₁.r := (norm_nonneg _).trans h₁
  have hr2 : 0 ≤ val b₂.r := (norm_nonneg _).trans h₂
  have n2 := CC.norm_le_normUp b₂.c
  have n1 := CC.norm_le_normUp b₁.c
  have p2 := CC.normUp_nonneg b₂.c
  have p1 := CC.normUp_nonneg b₁.c
  have x := LawfulCertArith.upAdd_ge b₂.c.normUp b₂.r
  have m1 := LawfulCertArith.upMul_ge b₁.r (upAdd b₂.c.normUp b₂.r) hr1 (by linarith)
  have m2 := LawfulCertArith.upMul_ge b₁.c.normUp b₂.r p1 hr2
  have u1 := LawfulCertArith.upAdd_ge (upMul b₁.r (upAdd b₂.c.normUp b₂.r))
    (upMul b₁.c.normUp b₂.r)
  have u2 := LawfulCertArith.upAdd_ge (mulReErr b₁.c.re b₁.c.im b₂.c.re b₂.c.im)
    (mulImErr b₁.c.re b₁.c.im b₂.c.re b₂.c.im)
  have u3 := LawfulCertArith.upAdd_ge
    (upAdd (upMul b₁.r (upAdd b₂.c.normUp b₂.r)) (upMul b₁.c.normUp b₂.r))
    (upAdd (mulReErr b₁.c.re b₁.c.im b₂.c.re b₂.c.im) (mulImErr b₁.c.re b₁.c.im b₂.c.re b₂.c.im))
  have hc : ‖b₁.c.toC * b₂.c.toC - (times b₁ b₂).c.toC‖ ≤
      val (mulReErr b₁.c.re b₁.c.im b₂.c.re b₂.c.im) +
        val (mulImErr b₁.c.re b₁.c.im b₂.c.re b₂.c.im) := by
    apply norm_le_of_re_im
    · simp only [Complex.sub_re, Complex.mul_re, times, CC.toC]
      rw [abs_sub_comm]; exact mulReErr_bound _ _ _ _
    · simp only [Complex.sub_im, Complex.mul_im, times, CC.toC]
      rw [abs_sub_comm]; exact mulImErr_bound _ _ _ _
  have hw2 : ‖w₂‖ ≤ ‖b₂.c.toC‖ + val b₂.r := by
    calc ‖w₂‖ = ‖(w₂ - b₂.c.toC) + b₂.c.toC‖ := by rw [sub_add_cancel]
      _ ≤ _ := (norm_add_le _ _).trans (by unfold Mem at h₂; linarith)
  have t1 : ‖(w₁ - b₁.c.toC) * w₂‖ ≤ val b₁.r * (‖b₂.c.toC‖ + val b₂.r) := by
    rw [norm_mul]
    exact mul_le_mul h₁ hw2 (norm_nonneg _) hr1
  have t2 : ‖b₁.c.toC * (w₂ - b₂.c.toC)‖ ≤ ‖b₁.c.toC‖ * val b₂.r := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left h₂ (norm_nonneg _)
  have t1' : val b₁.r * (‖b₂.c.toC‖ + val b₂.r) ≤ val b₁.r * val (upAdd b₂.c.normUp b₂.r) :=
    mul_le_mul_of_nonneg_left (by linarith) hr1
  have t2' : ‖b₁.c.toC‖ * val b₂.r ≤ val b₁.c.normUp * val b₂.r :=
    mul_le_mul_of_nonneg_right n1 hr2
  have : w₁ * w₂ - (times b₁ b₂).c.toC = (w₁ - b₁.c.toC) * w₂ + b₁.c.toC * (w₂ - b₂.c.toC) +
      (b₁.c.toC * b₂.c.toC - (times b₁ b₂).c.toC) := by ring
  unfold Mem
  rw [this]
  have hr : val (times b₁ b₂).r = val (upAdd
    (upAdd (upMul b₁.r (upAdd b₂.c.normUp b₂.r)) (upMul b₁.c.normUp b₂.r))
    (upAdd (mulReErr b₁.c.re b₁.c.im b₂.c.re b₂.c.im)
      (mulImErr b₁.c.re b₁.c.im b₂.c.re b₂.c.im))) := rfl
  rw [hr]
  have k2 := norm_add_le ((w₁ - b₁.c.toC) * w₂) (b₁.c.toC * (w₂ - b₂.c.toC))
  have k3 := norm_add_le ((w₁ - b₁.c.toC) * w₂ + b₁.c.toC * (w₂ - b₂.c.toC))
    (b₁.c.toC * b₂.c.toC - (times b₁ b₂).c.toC)
  linarith

/-- Taylor data for `exp`: after `m` steps, the balls of `w ^ m / m !` and `∑_{i ≤ m} w ^ i / i !`.
-/
def expAux (zb : CertBall α) : ℕ → CertBall α × CertBall α
  | 0 => (one, one)
  | m + 1 =>
    let t := times (times (expAux zb m).1 zb) (ofRat (1 / ((m : ℚ) + 1)))
    (t, plus (expAux zb m).2 t)

theorem expAux_mem {w : ℂ} {zb : CertBall α} (hw : Mem w zb) (m : ℕ) :
    Mem (w ^ m / (m.factorial : ℂ)) (expAux zb m).1 ∧
      Mem (∑ i ∈ Finset.range (m + 1), w ^ i / (i.factorial : ℂ)) (expAux zb m).2 := by
  induction m with
  | zero => simpa [expAux] using And.intro (mem_one (α := α)) (mem_one (α := α))
  | succ m ih =>
    have ht : Mem (w ^ (m + 1) / ((m + 1).factorial : ℂ)) (expAux zb (m + 1)).1 := by
      have := mem_times (mem_times ih.1 hw) (mem_ofRat (α := α) (1 / ((m : ℚ) + 1)))
      have e : w ^ (m + 1) / ((m + 1).factorial : ℂ) =
          w ^ m / (m.factorial : ℂ) * w * ((1 / ((m : ℚ) + 1) : ℚ) : ℂ) := by
        push_cast
        rw [Nat.factorial_succ]
        push_cast
        have : ((m : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
        rw [pow_succ]
        field_simp
      rw [e]
      exact this
    refine ⟨ht, ?_⟩
    have := mem_plus ih.2 ht
    rw [Finset.sum_range_succ _ (m + 1)]
    exact this

end CertBall

/-! ### The scalar complex exponential ball -/

/-- A certified scalar complex exponential ball (Taylor order `N`, `Complex.exp_bound`):
returns a centre and a radius. The Taylor sum has `N + 1` terms, evaluated in ball arithmetic
over the input ball `(z, zRad)`; the remainder is `eRem (N + 1)`. -/
def certCExp {α : Type} [CertArith α] (z : CC α) (zRad : α) (N : ℕ) : CC α × α :=
  let b := (CertBall.expAux ⟨z, zRad⟩ N).2
  (b.c, upAdd b.r (ofRatUp (eRem (N + 1))))

/-- The backend test that the input ball lies in the unit disc (`‖z‖ + zRad ≤ 1`). -/
def certCExpSmall {α : Type} [CertArith α] (z : CC α) (zRad : α) : Bool :=
  ble (upAdd z.normUp zRad) (ofInt 1)

theorem certCExpSmall_sound {α : Type} [CertArith α] [LawfulCertArith α] {z : CC α} {zRad : α}
    (h : certCExpSmall z zRad = true) : ‖z.toC‖ + val zRad ≤ 1 := by
  have h1 := LawfulCertArith.ble_sound _ _ h
  have h2 := LawfulCertArith.upAdd_ge z.normUp zRad
  rw [LawfulCertArith.val_ofInt] at h1
  have := CC.norm_le_normUp z
  push_cast at h1
  linarith

/-- Soundness of `certCExp` for balls inside the unit disc. The signed statement without the size
hypothesis `hsmall` is false (see the module docstring); `certCExpSmall_sound` discharges it
from a backend test. -/
theorem certCExp_sound_of_small {α : Type} [CertArith α] [LawfulCertArith α] (z : CC α)
    (zRad : α) (N : ℕ) (hsmall : ‖z.toC‖ + val zRad ≤ 1) {w : ℂ}
    (hw : ‖w - z.toC‖ ≤ val zRad) :
    ‖Complex.exp w - (certCExp z zRad N).1.toC‖ ≤ val (certCExp z zRad N).2 := by
  have hm := (CertBall.expAux_mem (α := α) (zb := ⟨z, zRad⟩) hw N).2
  have hw1 : ‖w‖ ≤ 1 := by
    have : ‖w‖ ≤ ‖w - z.toC‖ + ‖z.toC‖ := by
      simpa using norm_add_le (w - z.toC) z.toC
    linarith
  have hb := Complex.exp_bound hw1 (n := N + 1) (Nat.succ_pos N)
  have hpow : ‖w‖ ^ (N + 1) ≤ 1 := pow_le_one₀ (norm_nonneg _) hw1
  have hrem : ‖w‖ ^ (N + 1) * (((N + 1).succ : ℝ) * (((N + 1).factorial : ℝ) * ((N + 1 : ℕ) : ℝ))⁻¹)
      ≤ (eRem (N + 1) : ℝ) := by
    have : (eRem (N + 1) : ℝ) = (((N + 1).succ : ℝ) * (((N + 1).factorial : ℝ) *
        ((N + 1 : ℕ) : ℝ))⁻¹) := by
      unfold eRem
      push_cast
      rw [div_eq_mul_inv]
    rw [this]
    have h0 : 0 ≤ (((N + 1).succ : ℝ) * (((N + 1).factorial : ℝ) * ((N + 1 : ℕ) : ℝ))⁻¹) := by
      positivity
    exact mul_le_of_le_one_left h0 hpow
  have hup := LawfulCertArith.ofRatUp_ge (α := α) (eRem (N + 1))
  have hu := LawfulCertArith.upAdd_ge (CertBall.expAux ⟨z, zRad⟩ N).2.r
    (ofRatUp (eRem (N + 1)))
  unfold CertBall.Mem at hm
  have hc : certCExp z zRad N = ((CertBall.expAux ⟨z, zRad⟩ N).2.c,
      upAdd (CertBall.expAux ⟨z, zRad⟩ N).2.r (ofRatUp (eRem (N + 1)))) := rfl
  rw [hc]
  simp only
  have : Complex.exp w - (CertBall.expAux ⟨z, zRad⟩ N).2.c.toC =
      (Complex.exp w - ∑ i ∈ Finset.range (N + 1), w ^ i / (i.factorial : ℂ)) +
      (∑ i ∈ Finset.range (N + 1), w ^ i / (i.factorial : ℂ) -
        (CertBall.expAux ⟨z, zRad⟩ N).2.c.toC) := by ring
  rw [this]
  have := norm_add_le (Complex.exp w - ∑ i ∈ Finset.range (N + 1), w ^ i / (i.factorial : ℂ))
    (∑ i ∈ Finset.range (N + 1), w ^ i / (i.factorial : ℂ) -
        (CertBall.expAux ⟨z, zRad⟩ N).2.c.toC)
  linarith

end KAM.Certificate
