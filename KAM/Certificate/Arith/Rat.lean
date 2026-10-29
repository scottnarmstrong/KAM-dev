/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Certificate.Arith.PiEnclosure
public import KAM.Certificate.Arith.Roots

/-!
# The exact rational backend

`ℚ` is a certified arithmetic backend with `val = Rat.cast`, exact operations and zero errors; the
rounding-direction operations are exact too. All operations reduce in the kernel (`decide +kernel`).
-/

@[expose] public section

namespace KAM.Certificate

open CertArith

/-- Backend 1: exact rationals (`addErr = mulErr = 0`). -/
instance instCertArithRat : CertArith ℚ where
  val q := (q : ℝ)
  ofInt z := (z : ℚ)
  ofRatUp q := q
  ofRatDown q := q
  add a b := a + b
  neg a := -a
  mul a b := a * b
  abs a := |a|
  addErr _ _ := 0
  mulErr _ _ := 0
  upAdd a b := a + b
  upMul a b := a * b
  ble a b := decide (a ≤ b)
  blt a b := decide (a < b)
  beq a b := decide (a = b)

instance instLawfulCertArithRat : LawfulCertArith ℚ where
  val_ofInt z := by simp [CertArith.val, CertArith.ofInt]
  ofRatUp_ge q := le_of_eq rfl
  ofRatDown_le q := le_of_eq rfl
  add_err a b := by simp [CertArith.val, CertArith.add, CertArith.addErr]
  val_neg a := by simp [CertArith.val, CertArith.neg]
  mul_err a b := by simp [CertArith.val, CertArith.mul, CertArith.mulErr]
  val_abs a := by simp [CertArith.val, CertArith.abs]
  upAdd_ge a b := by simp [CertArith.val, CertArith.upAdd]
  upMul_ge a b _ _ := by simp [CertArith.val, CertArith.upMul]
  ble_sound a b h := by
    simpa [CertArith.ble, CertArith.val] using (by exact_mod_cast of_decide_eq_true h : a ≤ b)
  blt_sound a b h := by
    simpa [CertArith.blt, CertArith.val] using (by exact_mod_cast of_decide_eq_true h : a < b)
  beq_sound a b h := by
    simp [CertArith.val, of_decide_eq_true (show decide (a = b) = true from h)]

example : ble (upAdd (ofRatUp (α := ℚ) (1 / 3)) (ofRatUp (1 / 6))) (ofRatUp (1 / 2)) = true := by
  decide +kernel

example : ble (upAdd (ofRatUp (α := ℚ) (1 / 3)) (ofRatUp (1 / 3))) (ofRatUp (1 / 2)) = false := by
  decide +kernel

example : blt (upMul (ofRatUp (2 / 3 : ℚ)) (ofRatUp (3 / 4))) (ofInt (α := ℚ) 1) = true := by
  decide +kernel

example : beq (add (ofInt (α := ℚ) 2) (neg (ofRatDown (4 / 2)))) (ofInt 0) = true := by
  decide +kernel

example : certCExpSmall (⟨1 / 4, 1 / 4⟩ : CC ℚ) (1 / 4) = true := by
  decide +kernel

example : checkPiEnclosure (α := ℚ) ⟨(piLowRat 20 5 + piUpRat 20 5) / 2,
    (piUpRat 20 5 - piLowRat 20 5) / 2, 20, 5⟩ = true := by
  decide +kernel

example : checkPiEnclosure (α := ℚ) ⟨(piLowRat 20 5 + piUpRat 20 5) / 2,
    (piUpRat 20 5 - piLowRat 20 5) / 4, 20, 5⟩ = false := by
  decide +kernel

end KAM.Certificate
