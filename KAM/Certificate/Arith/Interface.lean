/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.Analysis.Complex.Norm

/-!
# The certified arithmetic interface

`CertArith α` is the data of a certified arithmetic backend (the exact real denoted by each
element and the rounded operations with their error terms); `LawfulCertArith α` is the
`Prop`-valued class of its soundness laws. Definitions over `CertArith` are computational and
law-free; every correctness theorem uses `[LawfulCertArith α]`.

`CC α` is a backend complex number `re + i im`; `CC.toC` is its denotation.
-/

@[expose] public section

namespace KAM.Certificate

/-- A certified arithmetic backend (data only). `val a` is the exact real denoted by `a`.
`add`/`mul` may round (fixed point) or be exact (`ℚ`); `addErr`/`mulErr` bound the rounding error.
`upAdd`/`upMul` round upward and are used on nonnegative radii only. Comparisons are one-sided
tests. Definitions over `CertArith` are computational and law-free; every correctness theorem that
uses a value of `ofInt`, `neg`, `add`, `mul` or a comparison assumes `[LawfulCertArith α]`
(finding F2). -/
class CertArith (α : Type) where
  val : α → ℝ
  ofInt : ℤ → α
  /-- outward conversions of an exact rational parameter -/
  ofRatUp : ℚ → α
  ofRatDown : ℚ → α
  add : α → α → α
  neg : α → α
  mul : α → α → α
  abs : α → α
  addErr : α → α → α
  mulErr : α → α → α
  upAdd : α → α → α
  upMul : α → α → α
  ble : α → α → Bool
  blt : α → α → Bool
  beq : α → α → Bool

/-- Soundness of a backend (one `Prop`-valued class, proved once per backend). -/
class LawfulCertArith (α : Type) [CertArith α] : Prop where
  val_ofInt : ∀ z : ℤ, CertArith.val (CertArith.ofInt (α := α) z) = z
  ofRatUp_ge : ∀ q : ℚ, (q : ℝ) ≤ CertArith.val (CertArith.ofRatUp (α := α) q)
  ofRatDown_le : ∀ q : ℚ, CertArith.val (CertArith.ofRatDown (α := α) q) ≤ q
  add_err : ∀ a b : α, |CertArith.val (CertArith.add a b) - (CertArith.val a + CertArith.val b)| ≤
    CertArith.val (CertArith.addErr a b)
  val_neg : ∀ a : α, CertArith.val (CertArith.neg a) = -CertArith.val a
  mul_err : ∀ a b : α, |CertArith.val (CertArith.mul a b) - CertArith.val a * CertArith.val b| ≤
    CertArith.val (CertArith.mulErr a b)
  val_abs : ∀ a : α, CertArith.val (CertArith.abs a) = |CertArith.val a|
  upAdd_ge : ∀ a b : α, CertArith.val a + CertArith.val b ≤ CertArith.val (CertArith.upAdd a b)
  upMul_ge : ∀ a b : α, 0 ≤ CertArith.val a → 0 ≤ CertArith.val b →
    CertArith.val a * CertArith.val b ≤ CertArith.val (CertArith.upMul a b)
  ble_sound : ∀ a b : α, CertArith.ble a b = true → CertArith.val a ≤ CertArith.val b
  blt_sound : ∀ a b : α, CertArith.blt a b = true → CertArith.val a < CertArith.val b
  beq_sound : ∀ a b : α, CertArith.beq a b = true → CertArith.val a = CertArith.val b

open CertArith

/-- A complex backend number `re + i im` (exact data or a computed centre). -/
structure CC (α : Type) where
  re : α
  im : α

/-- The complex number denoted by a `CC` (law-free). -/
def CC.toC {α : Type} [CertArith α] (c : CC α) : ℂ := ⟨val c.re, val c.im⟩

/-- Exact conjugation of a backend complex number. -/
def CC.conj {α : Type} [CertArith α] (c : CC α) : CC α := ⟨c.re, neg c.im⟩

theorem CC.toC_conj {α : Type} [CertArith α] [LawfulCertArith α] (c : CC α) :
    c.conj.toC = (starRingEnd ℂ) c.toC := by
  apply Complex.ext <;> simp [CC.conj, CC.toC, LawfulCertArith.val_neg]

/-- The zero of a backend complex number (needs `val_ofInt`). -/
theorem CC.toC_zero {α : Type} [CertArith α] [LawfulCertArith α] :
    (⟨ofInt 0, ofInt 0⟩ : CC α).toC = 0 := by
  apply Complex.ext <;> simp [CC.toC, LawfulCertArith.val_ofInt]

end KAM.Certificate
