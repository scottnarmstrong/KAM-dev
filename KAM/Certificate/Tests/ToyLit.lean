/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Certificate.Defs
public import KAM.Certificate.Arith.Rat

/-!
# Literal helpers of the toy certificates

Long rationals of the toy data (`certificates/so-toys/`, emitted by
`scripts/spin_orbit/toy_lean_cert.py`) are written in decimal chunks of `90` digits so that every
line stays within `100` columns. The helpers are plain computable functions: `decide +kernel`
evaluates them with the kernel's arbitrary-precision arithmetic.
-/

@[expose] public section

namespace KAM.Certificate

/-- The natural number with decimal chunks `cs` (every chunk after the first has `90` digits). -/
def toyNat (cs : List ℕ) : ℕ := cs.foldl (fun a c => a * 10 ^ 90 + c) 0

/-- `toyNat cs` as an integer. -/
def toyPos (cs : List ℕ) : ℤ := (toyNat cs : ℤ)

/-- `-toyNat cs` as an integer. -/
def toyNeg (cs : List ℕ) : ℤ := -(toyNat cs : ℤ)

/-- The rational `a / b` (normalized by `mkRat`). -/
def toyQ (a : ℤ) (b : ℕ) : ℚ := mkRat a b

/-- A Fourier polynomial over the common denominator `D`: the terms `(k, re / D + i im / D)`. -/
def toyScaledPoly (D : ℕ) (ts : List (CertKey × ℤ × ℤ)) : CertPoly ℚ :=
  ⟨ts.map fun t => (t.1, ⟨toyQ t.2.1 D, toyQ t.2.2 D⟩)⟩

theorem toyNat_test : toyNat [1, 2] = 10 ^ 90 + 2 := by decide +kernel

end KAM.Certificate
