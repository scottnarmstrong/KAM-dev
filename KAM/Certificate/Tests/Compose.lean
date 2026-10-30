/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Certificate.Expr.Compose
public import KAM.Certificate.Arith.Rat

/-!
# Composition tests (`Embedding`, `Expr/Compose`)

Every check below is decided by `decide +kernel` (kernel reduction only), in `ℚ`.

* **`n = 1`**: `K(θ) = (θ + U/2π, A)` with `U = 0.1 cos 2πθ`, `A = 1 + 0.1 cos 2πθ`, and the
  program `A`, `1/2`, `A/2`, `χ_1∘K`, `χ_{-1}∘K`, their sum, `(A/2)(χ_1 + χ_{-1})∘K`,
  `exp(1/2)`, `1/A`, `i/2π` and `i/2π + 1/2` (mixed degrees). The character witness
  `exp(iU) ≈ Σ_{|k| ≤ 5} i^{|k|} J_{|k|}(0.1) χ_k` serves `χ_1` directly and `χ_{-1}` through
  `conjReflect`; every radius is `≤ 10⁻⁶`. The product with the constant `1/2` takes the scalar
  route (exact: radius `0`); the reflected character has the same radius as the direct one.
* **Fail closed**: a missing character, exp or reciprocal witness, and a character pin
  `exp(i U(0))` with `|U(0)| = 3.1` at `pinHalvings = 0`, make `Slp.compose` return `none`; a
  slot off the program is the zero model.
* **`n = 2`, key normalization** (the lunar pattern): `U₂ = 0` (syntactically zero), so the
  keys `(1, 0)`, `(1, 3)` and `(-1, 2)` share the one witness under `(1, 0)` (the last through
  `conjReflect`).
* **Contract**: `Slp.compose_sound` instantiated on the toy.
-/

public section

namespace KAM.Certificate

open CertArith

def composeTestW : CertWeight := ⟨1 / 100, 11 / 10⟩

theorem composeTest_weight : checkWeight composeTestW 0 6 = true := by decide +kernel

def composeTestPi : PiEnclosure ℚ := ⟨314159 / 100000, 1 / 10000, 5, 2⟩

theorem composeTest_pi : checkPiEnclosure composeTestPi = true := by decide +kernel

/-- `x` rounded down to `10⁻¹²`. -/
def composeTestRound (x : ℚ) : ℚ := ((x.num * 10 ^ 12 / x.den : ℤ) : ℚ) / 10 ^ 12

/-- `J_k(a)`, twelve terms of the series. -/
def composeTestJ (a : ℚ) (k : ℕ) : ℚ :=
  ((List.range 12).map fun m =>
    (-1) ^ m * (a / 2) ^ (2 * m + k) / ((m.factorial * (m + k).factorial : ℕ) : ℚ)).sum

/-- `i^m x`. -/
def composeTestIPow (m : ℕ) (x : ℚ) : CC ℚ :=
  match m % 4 with
  | 0 => ⟨x, 0⟩
  | 1 => ⟨0, x⟩
  | 2 => ⟨-x, 0⟩
  | _ => ⟨0, -x⟩

/-- The keys `-K, …, K`. -/
def composeTestRange (K : ℕ) : List ℤ := (List.range (2 * K + 1)).map fun i => (i : ℤ) - K

/-- `exp(i a cos 2πθ₁) ≈ Σ_{|k| ≤ 5} i^{|k|} J_{|k|}(a) χ_{(k, 0, …)}` (`pad` zeros appended). -/
def composeTestCharE (a : ℚ) (pad : List ℤ) (h : ℕ) : ExpWitness ℚ :=
  ⟨⟨(composeTestRange 5).map fun k =>
    (k :: pad, composeTestIPow k.natAbs (composeTestRound (composeTestJ a k.natAbs)))⟩, h, 20⟩

/-- `0.1 cos 2πθ₁` with the constant `c` (keys padded by `pad`). -/
def composeTestCos (c : ℚ) (pad : List ℤ) : CertRealPoly ℚ := ⟨c, [(1 :: pad, ⟨1 / 20, 0⟩)]⟩

/-- `K(θ) = (θ + U/2π, A)`, `U = c + 0.1 cos 2πθ`, `A = 1 + 0.1 cos 2πθ`. -/
def composeTestK (c : ℚ) : CertEmbedding ℚ :=
  ⟨[-1], [composeTestCos c []], [0], [composeTestCos 1 []]⟩

def composeTestProg : Slp :=
  ⟨[.action 0, .const (1 / 2) 0 0, .mul 1 0, .char [1], .char [-1], .add 3 4, .mul 2 5,
    .exp 1, .inv 0, .const 0 1 (-1), .add 9 1]⟩

/-- `1/(1 + 0.1 cos 2πθ) ≈ s Σ_{|k| ≤ 6} (-r)^{|k|} χ_k`, `s = 1/√0.99`, `r = 10(1 - √0.99)`. -/
def composeTestInv : CertPoly ℚ :=
  ⟨(composeTestRange 6).map fun k =>
    ([k], ⟨composeTestRound (10050378152592 / 10 ^ 13 * (-501256289 / 10 ^ 10) ^ k.natAbs), 0⟩)⟩

def composeTestWit (h : ℕ) : Witnesses ℚ :=
  ⟨[⟨⟨[([0], ⟨16487212707 / 10 ^ 10, 0⟩)]⟩, 0, 20⟩], [composeTestInv],
    [([1], composeTestCharE (1 / 10) [] h)], []⟩

def composeTestCfg : ModelConfig ℚ :=
  ⟨100, 10, 4, fun _ _ => none,
    [([0, 6], .direct), ([2, 0], .direct), ([1, 0, 0], .direct), ([1, 1, 0], .direct)]⟩

/-- The composition of every slot. -/
def composeTestRun (c : ℚ) (wit : Witnesses ℚ) (wanted : List ℕ) : Option (List (CertModel ℚ)) :=
  Slp.compose 1 composeTestProg (composeTestK c) wit composeTestW composeTestCfg composeTestPi
    wanted

theorem composeTest_all :
    (composeTestRun 0 (composeTestWit 0) (List.range 11)).any (fun ms =>
      ms.length == 11 && ms.all fun m => decide (0 ≤ m.rad ∧ m.rad ≤ 1 / 10 ^ 6)) = true := by
  decide +kernel

/-- The product with the constant `1/2` is a scalar multiplication: exact. -/
theorem composeTest_scalar :
    (composeTestRun 0 (composeTestWit 0) [2]).any (fun ms =>
      ms.all fun m => m.poly.terms.length == 3 && decide (m.rad = 0)) = true := by
  decide +kernel

/-- `χ_{-1}∘K` through the reflected witness of `χ_1`: the same radius. -/
theorem composeTest_conj :
    (composeTestRun 0 (composeTestWit 0) [3, 4]).any (fun ms =>
      decide (0 < (ms.getD 0 zeroModel).rad ∧
        (ms.getD 0 zeroModel).rad = (ms.getD 1 zeroModel).rad)) = true := by
  decide +kernel

theorem composeTest_noChar :
    composeTestRun 0 ⟨(composeTestWit 0).expWit, (composeTestWit 0).invWit, [], []⟩
      [0] = none := by
  decide +kernel

theorem composeTest_noExp :
    composeTestRun 0 ⟨[], (composeTestWit 0).invWit, (composeTestWit 0).charWit,
      []⟩ [0] = none := by
  decide +kernel

theorem composeTest_noInv :
    composeTestRun 0 ⟨(composeTestWit 0).expWit, [], (composeTestWit 0).charWit,
      []⟩ [0] = none := by
  decide +kernel

/-- The pin `exp(i U(0))`, `U(0) = 3.1`, fails at `pinHalvings = 0`: fail closed. -/
theorem composeTest_pinFail : composeTestRun 3 (composeTestWit 0) [0] = none := by
  decide +kernel

/-- A slot off the program is the zero model. -/
theorem composeTest_offProgram :
    (composeTestRun 0 (composeTestWit 0) [40]).any (fun ms =>
      ms.all fun m => m.poly.terms.isEmpty && m.deg == 0 && decide (m.rad = 0)) = true := by
  decide +kernel

/-! ### `n = 2`: key normalization -/

/-- `U = (0.1 cos 2πθ₁, 0)`, `A = (1 + 0.1 cos 2πθ₁, 1)`. -/
def composeTestK2 : CertEmbedding ℚ :=
  ⟨[-1, -1], [composeTestCos 0 [0], ⟨0, []⟩], [0, 0], [composeTestCos 1 [0], ⟨1, []⟩]⟩

def composeTestProg2 : Slp := ⟨[.char [1, 0], .char [1, 3], .char [-1, 2], .add 0 1, .add 3 2]⟩

theorem composeTest_normKey :
    composeTestK2.normKey 2 [1, 3] = [1, 0] ∧ composeTestK2.normKey 2 [-1, 2] = [-1, 0] := by
  decide +kernel

theorem composeTest_n2 :
    (Slp.compose 2 composeTestProg2 composeTestK2 ⟨[], [], [([1, 0], composeTestCharE (1 / 10)
        [0] 0)], []⟩ composeTestW composeTestCfg composeTestPi [0, 1, 2, 4]).any (fun ms =>
      ms.length == 4 && ms.all fun m => decide (0 < m.rad ∧ m.rad ≤ 1 / 10 ^ 6)) = true := by
  decide +kernel

/-! ### Contract -/

/-- **Contract instance**: every model returned by the toy composition encloses its slot
composed with the toy embedding. -/
theorem composeTest_sound {ms : List (CertModel ℚ)}
    (h : composeTestRun 0 (composeTestWit 0) (List.range 11) = some ms) :
    ms.length = 11 ∧ ∀ idx (hidx : idx < ms.length), ms[idx].Encloses 1 composeTestW.rho
      (fun θ => composeTestProg.val 1 ((composeTestK 0).eval 1 θ) ((List.range 11).getD idx 0)) :=
  Slp.compose_sound composeTestProg _ _ composeTest_weight composeTestCfg composeTest_pi _ h

end KAM.Certificate
