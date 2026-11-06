/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

/-!
# Ledger data types (T2-CONF, N7)

The plain data structures of the tube-checker ledger, in core Lean only (no Mathlib), so that the
generated literal modules import nothing heavy: packing parameters `Prm`, compact literals `LitD`,
sparse literals `SpD`, model claims `Cl`, and the step parameters `UPrm`, `OPrm`, `SqPrm`, `IvPrm`.
Their semantics live in `Engine/Input.lean`, `Engine/Sparse.lean`, `Engine/Horner.lean` and
`Engine/Powers.lean`.
-/

@[expose] public section

namespace KAM.EffectiveStability.Tube

/-- Global packing parameters: slot width, row stride, compact digit width. -/
structure Prm where
  w : Nat
  S : Nat
  b : Nat

/-- A whitened compact literal model. -/
structure LitD where
  C : Nat
  par : Bool
  q : Rat
  salt : Nat
  nch : Nat
  lit : Nat
  L₁ : Nat
  L₂ : Nat

/-- A sparse model. -/
structure SpD where
  C : Nat
  par : Bool
  q : Rat
  es : List ((Nat × Nat) × Int)

/-- The claims of a ledger model: its `C¹` errors and an `ℓ¹` bound of its mantissas. -/
structure Cl where
  e₀ : Rat
  e₁ : Rat
  n : Nat

/-- Per-`U` parameters: `Q`, the product errors, the slot bound, the load level, the `ℓ¹` claim. -/
structure UPrm where
  Q : Rat
  E₀ : Rat
  E₁ : Rat
  BX : Nat
  l : Nat
  n : Nat

/-- Per-output parameters: `Q`, the product errors, the slot bound, `α_X`, `α_O`, the load level of
the difference and its errors. -/
structure OPrm where
  Q : Rat
  E₀ : Rat
  E₁ : Rat
  BX : Nat
  aX : Nat
  aO : Nat
  lD : Nat
  F₀ : Rat
  F₁ : Rat

/-- The parameters of a square-root witness. -/
structure SqPrm where
  Q : Rat
  E₀ : Rat
  E₁ : Rat
  BX : Nat
  aX : Nat
  aO : Nat
  lD : Nat
  F₀ : Rat
  F₁ : Rat
  ρ : Rat
  ρ' : Rat
  σ₀ : Rat
  w₀ : Rat

/-- The parameters of an inverse-square-root witness. -/
structure IvPrm where
  Q : Rat
  E₀ : Rat
  E₁ : Rat
  BX : Nat
  aX : Nat
  aO : Nat
  lD : Nat
  F₀ : Rat
  F₁ : Rat
  qq : Rat
  qq' : Rat

/-- A rational from a sign and two naturals (the literal form of big rationals). -/
def mkQ (neg : Bool) (n d : Nat) : Rat := (if neg then -(n : Rat) else (n : Rat)) / (d : Rat)

/-- A dense list of `k` rationals from index `i` on, merging sparse `(index, value)` entries in
increasing index order (one pass; the ledger's entries are sorted and distinct). -/
def denseM : Nat → Nat → List (Nat × Rat) → List Rat
  | 0, _, _ => []
  | k + 1, i, [] => 0 :: denseM k (i + 1) []
  | k + 1, i, e :: es =>
    if e.1 == i then e.2 :: denseM k (i + 1) es else 0 :: denseM k (i + 1) (e :: es)

/-- A dense list of `len` rationals from sorted sparse `(index, value)` entries. -/
def denseQ (len : Nat) (es : List (Nat × Rat)) : List Rat := denseM len 0 es

/-- The default literal (never certified; returned by table lookups that miss). -/
def LitD.dflt : LitD := ⟨0, false, 0, 0, 1, 0, 0, 0⟩

/-- The default claim. -/
def Cl.dflt : Cl := ⟨0, 0, 0⟩

/-- The default output parameters. -/
def OPrm.dflt : OPrm := ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩

/-- The default square-root parameters. -/
def SqPrm.dflt : SqPrm := ⟨1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0⟩

/-- The default inverse-square-root parameters. -/
def IvPrm.dflt : IvPrm := ⟨1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩

end KAM.EffectiveStability.Tube

end
