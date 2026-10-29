/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Certificate.Expr.Basic
public import KAM.Certificate.PhaseBasis

/-!
# Straight-line programs over `ℂ`

`Slp` is the internal straight-line program language of the SO certificate (SO design §D): a list
of operations whose operands are earlier slot numbers. A constant carries its `2π`-degree, `char k`
is `e^{2πi k·θ}`, and the nonlinearities are `exp` and `inv`. The value of a slot is computed by
a left fold, so an operand that is not an earlier slot reads `0` and appending operations never
changes the value of an existing slot (`Slp.val_append`). `HamJet` and `phaseNat` are the table
types of the jet compiler of `KAM.Certificate.Expr.Diff`.
-/

@[expose] public noncomputable section

namespace KAM.Certificate

/-- Straight-line program over `ℂ` (internal). Operands are earlier slot numbers; a constant
carries its `2π`-degree; `char k` is `e^{2πi k·θ}`. Nonlinearities: `exp` and `inv` (`x⁻¹`). -/
inductive SlpOp : Type
  | const (re im : ℚ) (deg : ℤ)
  | action (j : ℕ)
  | char (k : CertKey)
  | add (a b : ℕ)
  | mul (a b : ℕ)
  | exp (a : ℕ)
  | inv (a : ℕ)

structure Slp where
  ops : List SlpOp

/-- The complex number `(re + i im) (2π)^deg` denoted by a constant operation. -/
def slpConstVal (re im : ℚ) (deg : ℤ) : ℂ :=
  ((re : ℂ) + (im : ℂ) * Complex.I) * (2 * (Real.pi : ℂ)) ^ deg

/-- The value of one operation at `z`, given the values `acc` of the earlier slots. -/
def SlpOp.step (n : ℕ) (z : (Fin n → ℂ) × (Fin n → ℂ)) (acc : List ℂ) : SlpOp → ℂ
  | .const re im deg => slpConstVal re im deg
  | .action j => if h : j < n then z.2 ⟨j, h⟩ else 0
  | .char k => Complex.exp (Complex.I * modePhase n k z.1)
  | .add a b => acc.getD a 0 + acc.getD b 0
  | .mul a b => acc.getD a 0 * acc.getD b 0
  | .exp a => Complex.exp (acc.getD a 0)
  | .inv a => (acc.getD a 0)⁻¹

/-- The values of all slots of a program, in order. -/
def Slp.vals (n : ℕ) (z : (Fin n → ℂ) × (Fin n → ℂ)) (ops : List SlpOp) : List ℂ :=
  ops.foldl (fun acc op => acc ++ [op.step n z acc]) []

/-- Value of slot `i` at the phase point `z` (out-of-range operands read `0`; `inv` is `x⁻¹`). -/
def Slp.val (n : ℕ) (p : Slp) (z : (Fin n → ℂ) × (Fin n → ℂ)) (i : ℕ) : ℂ :=
  (Slp.vals n z p.ops).getD i 0

/-- The program and slot tables of the jet of order three of an expression: slot of `H`,
of `∂_a H`, `∂_a ∂_b H`, `∂_a ∂_b ∂_c H` (`a, b, c` phase indices in `sumVec` order).
Forward-mode differentiation with sharing, zero/constant folding and dependency pruning;
`(x⁻¹)' = -x⁻¹ · x⁻¹ · x'`. -/
structure HamJet where
  prog : Slp
  v0 : ℕ
  d1 : List ℕ
  d2 : List (List ℕ)
  d3 : List (List (List ℕ))

/-- Phase index as a natural number: `inl j ↦ j`, `inr j ↦ n + j`. -/
def phaseNat {n : ℕ} : Fin n ⊕ Fin n → ℕ
  | .inl j => j.val
  | .inr j => n + j.val

theorem Slp.vals_append_prefix (n : ℕ) (z : (Fin n → ℂ) × (Fin n → ℂ)) (more : List SlpOp) :
    ∀ acc : List ℂ,
      acc <+: more.foldl (fun acc op => acc ++ [op.step n z acc]) acc := by
  induction more with
  | nil => intro acc; exact List.prefix_refl _
  | cons op more ih =>
    intro acc
    exact (List.prefix_append acc _).trans (ih _)

theorem Slp.vals_append (n : ℕ) (z : (Fin n → ℂ) × (Fin n → ℂ)) (ops more : List SlpOp) :
    Slp.vals n z ops <+: Slp.vals n z (ops ++ more) := by
  unfold Slp.vals
  rw [List.foldl_append]
  exact Slp.vals_append_prefix n z more _

theorem Slp.vals_length (n : ℕ) (z : (Fin n → ℂ) × (Fin n → ℂ)) (ops : List SlpOp) :
    (Slp.vals n z ops).length = ops.length := by
  unfold Slp.vals
  induction ops using List.reverseRecOn with
  | nil => rfl
  | append_singleton ops op ih => simp [List.foldl_append, ih]

/-- Appending operations never changes the value of an existing slot. -/
theorem Slp.val_append (n : ℕ) (z : (Fin n → ℂ) × (Fin n → ℂ)) (ops more : List SlpOp)
    {i : ℕ} (hi : i < ops.length) :
    (Slp.vals n z (ops ++ more)).getD i 0 = (Slp.vals n z ops).getD i 0 := by
  obtain ⟨t, ht⟩ := Slp.vals_append n z ops more
  have hi' : i < (Slp.vals n z ops).length := by rwa [Slp.vals_length]
  rw [← ht, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_left hi']

/-- The value of the slot just appended. -/
theorem Slp.vals_snoc (n : ℕ) (z : (Fin n → ℂ) × (Fin n → ℂ)) (ops : List SlpOp) (op : SlpOp) :
    Slp.vals n z (ops ++ [op]) = Slp.vals n z ops ++ [op.step n z (Slp.vals n z ops)] := by
  unfold Slp.vals
  rw [List.foldl_append]
  rfl

theorem Slp.val_snoc_self (n : ℕ) (z : (Fin n → ℂ) × (Fin n → ℂ)) (ops : List SlpOp)
    (op : SlpOp) :
    (Slp.vals n z (ops ++ [op])).getD ops.length 0 = op.step n z (Slp.vals n z ops) := by
  rw [Slp.vals_snoc, List.getD_eq_getElem?_getD, List.getElem?_append_right
    (by rw [Slp.vals_length])]
  simp [Slp.vals_length]

end KAM.Certificate

end
