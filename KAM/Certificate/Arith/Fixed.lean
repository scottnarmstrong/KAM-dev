/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Certificate.Arith.PiEnclosure
public import KAM.Certificate.Arith.Roots

/-!
# The fixed-point backend

`CertFixed P` is an integer `m` denoting `m / 2^P`. Addition and negation are exact
(`addErr = 0`); multiplication floors the product by `2^P` and reports an error of one ulp.
`ofRatDown`/`upMul` round down/up by integer floor division. Every operation uses only `Int`/`Nat`
literal arithmetic (`Int.mul`, `Int.ediv`, `Nat.pow`) and reduces in the kernel
(`decide +kernel`); there is no well-founded recursion.
-/

@[expose] public section

namespace KAM.Certificate

open CertArith

/-- Backend 2: fixed point, `m ↦ m / 2^P` with floor rounding and tracked ulp errors. -/
structure CertFixed (P : ℕ) where
  m : ℤ

namespace CertFixed

/-- The ulpDen `2^P` as an integer (a `Nat.pow` literal, kernel-accelerated). -/
def ulpDen (P : ℕ) : ℤ := ((2 ^ P : ℕ) : ℤ)

/-- Ceiling division of an integer by a positive integer. -/
def cdiv (x d : ℤ) : ℤ := -((-x) / d)

theorem ulpDen_pos (P : ℕ) : (0 : ℝ) < ((ulpDen P : ℤ) : ℝ) := by
  simp [ulpDen]

theorem ulpDen_cast (P : ℕ) : ((ulpDen P : ℤ) : ℝ) = (2 : ℝ) ^ P := by
  simp [ulpDen]

/-- Floor division: `(x / d) * d ≤ x < (x / d) * d + d` over `ℝ`. -/
theorem fdiv_bounds (x d : ℤ) (hd : 0 < d) :
    (((x / d : ℤ) : ℝ)) * d ≤ x ∧ (x : ℝ) < ((x / d : ℤ) : ℝ) * d + d := by
  have h := Int.mul_ediv_add_emod x d
  have h0 := Int.emod_nonneg x hd.ne'
  have h1 := Int.emod_lt_of_pos x hd
  have e : (x : ℝ) = (d : ℝ) * ((x / d : ℤ) : ℝ) + ((x % d : ℤ) : ℝ) := by exact_mod_cast h.symm
  have a0 : (0 : ℝ) ≤ ((x % d : ℤ) : ℝ) := by exact_mod_cast h0
  have a1 : ((x % d : ℤ) : ℝ) < d := by exact_mod_cast h1
  constructor <;> nlinarith

/-- Ceiling division: `x ≤ cdiv x d * d < x + d` over `ℝ`. -/
theorem cdiv_bounds (x d : ℤ) (hd : 0 < d) :
    (x : ℝ) ≤ ((cdiv x d : ℤ) : ℝ) * d ∧ ((cdiv x d : ℤ) : ℝ) * d < x + d := by
  obtain ⟨h1, h2⟩ := fdiv_bounds (-x) d hd
  unfold cdiv
  push_cast at h1 h2 ⊢
  constructor <;> nlinarith

end CertFixed

open CertFixed

noncomputable instance instCertArithFixed (P : ℕ) : CertArith (CertFixed P) where
  val a := (a.m : ℝ) / (2 : ℝ) ^ P
  ofInt z := ⟨z * ulpDen P⟩
  ofRatUp q := ⟨cdiv (q.num * ulpDen P) q.den⟩
  ofRatDown q := ⟨(q.num * ulpDen P) / q.den⟩
  add a b := ⟨a.m + b.m⟩
  neg a := ⟨-a.m⟩
  mul a b := ⟨(a.m * b.m) / ulpDen P⟩
  abs a := ⟨(a.m.natAbs : ℤ)⟩
  addErr _ _ := ⟨0⟩
  mulErr _ _ := ⟨1⟩
  upAdd a b := ⟨a.m + b.m⟩
  upMul a b := ⟨cdiv (a.m * b.m) (ulpDen P)⟩
  ble a b := decide (a.m ≤ b.m)
  blt a b := decide (a.m < b.m)
  beq a b := decide (a.m = b.m)

theorem CertFixed.val_def {P : ℕ} (a : CertFixed P) :
    CertArith.val a = (a.m : ℝ) / (2 : ℝ) ^ P := rfl

instance instLawfulCertArithFixed (P : ℕ) : LawfulCertArith (CertFixed P) where
  val_ofInt z := by
    have := (ulpDen_pos P).ne'
    rw [ulpDen_cast] at this
    simp only [CertArith.val, CertArith.ofInt]
    push_cast [ulpDen]
    field_simp
  ofRatUp_ge q := by
    have hd : (0 : ℤ) < q.den := by exact_mod_cast q.den_pos
    obtain ⟨h, -⟩ := cdiv_bounds (q.num * ulpDen P) q.den hd
    have hD := ulpDen_pos P
    have hq : (q : ℝ) = q.num / q.den := Rat.cast_def q
    have hden : (0 : ℝ) < q.den := by exact_mod_cast q.den_pos
    simp only [CertArith.val, CertArith.ofRatUp]
    rw [hq, ← ulpDen_cast, div_le_div_iff₀ hden hD]
    push_cast at h
    linarith
  ofRatDown_le q := by
    have hd : (0 : ℤ) < q.den := by exact_mod_cast q.den_pos
    obtain ⟨h, -⟩ := fdiv_bounds (q.num * ulpDen P) q.den hd
    have hD := ulpDen_pos P
    have hq : (q : ℝ) = q.num / q.den := Rat.cast_def q
    have hden : (0 : ℝ) < q.den := by exact_mod_cast q.den_pos
    simp only [CertArith.val, CertArith.ofRatDown]
    rw [hq, ← ulpDen_cast, div_le_div_iff₀ hD hden]
    push_cast at h
    linarith
  add_err a b := by
    simp only [CertArith.val, CertArith.add, CertArith.addErr]
    push_cast
    rw [show ((a.m : ℝ) + b.m) / 2 ^ P - (a.m / 2 ^ P + b.m / 2 ^ P) = 0 by ring]
    simp
  val_neg a := by
    simp only [CertArith.val, CertArith.neg]
    push_cast
    ring
  mul_err a b := by
    obtain ⟨h1, h2⟩ := fdiv_bounds (a.m * b.m) (ulpDen P) (by simp [ulpDen])
    have hD := ulpDen_pos P
    rw [ulpDen_cast] at hD h1 h2
    simp only [CertArith.val, CertArith.mul, CertArith.mulErr]
    push_cast at h1 h2 ⊢
    set k : ℝ := (((a.m * b.m) / ulpDen P : ℤ) : ℝ)
    have hDP : (0 : ℝ) < 2 ^ P := hD
    have e : k / 2 ^ P - a.m / 2 ^ P * (b.m / 2 ^ P) = (k * 2 ^ P - a.m * b.m) / (2 ^ P) ^ 2 := by
      field_simp
    rw [e, abs_le]
    have hsq : (0 : ℝ) < ((2 : ℝ) ^ P) ^ 2 := by positivity
    have e1 : (1 : ℝ) / 2 ^ P = (2 ^ P) / (2 ^ P) ^ 2 := by field_simp
    rw [e1]
    constructor
    · rw [neg_le, neg_div', div_le_div_iff_of_pos_right hsq]; linarith
    · rw [div_le_div_iff_of_pos_right hsq]; linarith
  val_abs a := by
    simp only [CertArith.val, CertArith.abs]
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ P)]
    push_cast
    simp
  upAdd_ge a b := by
    simp only [CertArith.val, CertArith.upAdd]
    push_cast
    rw [add_div]
  upMul_ge a b _ _ := by
    obtain ⟨h1, -⟩ := cdiv_bounds (a.m * b.m) (ulpDen P) (by simp [ulpDen])
    have hD := ulpDen_pos P
    rw [ulpDen_cast] at hD h1
    simp only [CertArith.val, CertArith.upMul]
    push_cast at h1 ⊢
    have hsq : (0 : ℝ) < ((2 : ℝ) ^ P) ^ 2 := by positivity
    have e : (a.m : ℝ) / 2 ^ P * (b.m / 2 ^ P) = (a.m * b.m) / (2 ^ P) ^ 2 := by
      field_simp
    rw [e, div_le_div_iff₀ hsq hD]
    nlinarith
  ble_sound a b h := by
    have : a.m ≤ b.m := of_decide_eq_true h
    simp only [CertArith.val]
    gcongr
  blt_sound a b h := by
    have : a.m < b.m := of_decide_eq_true h
    simp only [CertArith.val]
    gcongr
  beq_sound a b h := by
    have : a.m = b.m := of_decide_eq_true h
    simp [CertArith.val, this]

section Examples

abbrev F64 := CertFixed 64
abbrev F448 := CertFixed 448

example : ble (upAdd (ofRatUp (α := F64) (1 / 3)) (ofRatUp (1 / 6))) (ofRatUp (1 / 2)) = false := by
  decide +kernel

example : ble (ofRatDown (α := F64) (1 / 3)) (ofRatUp (1 / 3)) = true := by decide +kernel

example : blt (ofRatDown (α := F64) (1 / 3)) (ofRatUp (1 / 3)) = true := by decide +kernel

example : blt (upMul (ofRatUp (2 / 3 : ℚ)) (ofRatUp (3 / 4))) (ofInt (α := F64) 1) = true := by
  decide +kernel

example : beq (add (ofInt (α := F64) 2) (neg (ofRatDown (4 / 2)))) (ofInt 0) = true := by
  decide +kernel

example : beq (add (ofInt (α := F64) 2) (neg (ofRatDown (5 / 2)))) (ofInt 0) = false := by
  decide +kernel

example : ble (mul (ofRatDown (α := F448) (1 / 3)) (ofRatDown (1 / 3)))
    (ofRatUp (1 / 9)) = true := by decide +kernel

example : blt (ofRatUp (α := F448) (1 / 9)) (mul (ofRatDown (1 / 3)) (ofRatDown (1 / 3))) =
    false := by decide +kernel

example : certCExpSmall (⟨ofRatUp (1 / 4), ofRatUp (1 / 4)⟩ : CC F448) (ofRatUp (1 / 4)) =
    true := by decide +kernel

example : checkPiEnclosure (α := F448) ⟨ofRatDown ((piLowRat 50 15 + piUpRat 50 15) / 2),
    upAdd (ofRatUp ((piUpRat 50 15 - piLowRat 50 15) / 2)) ⟨4⟩, 50, 15⟩ = true := by
  decide +kernel

example : checkPiEnclosure (α := F448) ⟨ofRatDown ((piLowRat 50 15 + piUpRat 50 15) / 2),
    ⟨0⟩, 50, 15⟩ = false := by
  decide +kernel

end Examples

end KAM.Certificate
