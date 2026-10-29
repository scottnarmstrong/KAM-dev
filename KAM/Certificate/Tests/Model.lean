/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Certificate.Model.Ops
public import KAM.Certificate.Arith.Rat

/-!
# Model-algebra tests (`Model/Ops`)

Every check below is decided by `decide +kernel` (kernel reduction only).

* **Product routes** (fixed point `CertFixed 4`, the `n = 2` data of `Tests/Packed`, restated
  here because the bodies of that module's definitions are not exported). The packed
  route returns exactly the polynomial of `CertPoly.mulPacked`; a missing key and a failing
  advice (one slot off by `+2`) both give the crude enclosure (empty polynomial); a constant
  factor is a scalar multiplication whether or not advice is registered, even bogus advice under
  its key (SO-ADVCOUNT lever 1); the zero model times anything is the zero model with radius `0`.
* **Direct route** (`ℚ`): equal product keys are merged in lexicographic order.
* **`add`, `trim`, `ofDeriv`, `toDeg`** (`ℚ`): merged coefficients; the dropped weighted size in
  the radius; the multiplier `i k_j` and the dropped zero-multiplier term; the degree change with
  `(2π)^1` enclosed by the Machin bounds of a validated `π` enclosure.
* **Contracts.** The enclosure of a product of two enclosed functions on the packed route.
-/

public section

namespace KAM.Certificate

open CertArith

/-! ### Product routes on the fixed-point backend -/

/-- Keys `(0..1, -1..1)`, row stride `5`, one row per block (as `packedTestLay2`). -/
def modelTestLay : PackLayout := ⟨[0, -1], [2, 3], [5, 1], 24, 1⟩

/-- The full product window `(0..2, -2..2)`. -/
def modelTestTarget : PackLayout := ⟨[0, -2], [3, 5], [5, 1], 24, 1⟩

def modelTestA2 : List (CertKey × ℤ) :=
  [([0, -1], 3), ([0, 0], -5), ([0, 1], 7), ([1, -1], 2), ([1, 0], 11), ([1, 1], -4)]

def modelTestB2 : List (CertKey × ℤ) :=
  [([0, -1], 6), ([0, 0], 1), ([0, 1], -9), ([1, -1], -3), ([1, 0], 8), ([1, 1], 5)]

/-- Correct design-B advice at `scale = 4`. -/
def modelTestAdv : PackedAdvice :=
  ⟨modelTestLay, modelTestLay, modelTestTarget, 4,
    [[1, -2, 1, 3, -4, 0, 0, 0, 0], [0, 7, -5, -4, 4, 0, 0, 0, 0], [0, -1, 7, 1, -1, 0, 0, 0, 0]],
    0⟩

/-- One advice slot off by `+2`. -/
def modelTestAdvOff : PackedAdvice :=
  ⟨modelTestLay, modelTestLay, modelTestTarget, 4,
    [[1, -2, 1, 5, -4, 0, 0, 0, 0], [0, 7, -5, -4, 4, 0, 0, 0, 0], [0, -1, 7, 1, -1, 0, 0, 0, 0]],
    0⟩

/-- Bogus advice (scale zero): it fails every check. -/
def modelTestBogus : PackedAdvice := ⟨modelTestLay, modelTestLay, modelTestTarget, 0, [], 0⟩

/-- A strip weight `w = 11/10 ≥ e^{2π/100}`. -/
def modelTestW : CertWeight := ⟨1 / 100, 11 / 10⟩

theorem modelTest_weight : checkWeight modelTestW 0 6 = true := by decide +kernel

/-- A fixed-point polynomial with the given real mantissas (scale `2^4`). -/
def modelTestRe (cs : List (CertKey × ℤ)) : CertPoly (CertFixed 4) :=
  ⟨cs.map fun t => (t.1, ⟨⟨t.2⟩, ⟨0⟩⟩)⟩

/-- A configuration with the production decoder and the given advice book (cutoff 100). -/
def modelTestCfg (book : AdviceBook) : ModelConfig (CertFixed 4) :=
  ⟨100, 0, 0, CertFixed.toMant 4, book⟩

/-- The packed advice of the `n = 2` test product, registered under the key `[5]`. -/
def modelTestBook : AdviceBook :=
  [([1], .direct), ([5], .packed 4 modelTestAdv modelTestBogus modelTestBogus
    modelTestBogus)]

def modelTestA : CertModel (CertFixed 4) := ⟨0, modelTestRe modelTestA2, ⟨1⟩⟩

def modelTestB : CertModel (CertFixed 4) := ⟨1, modelTestRe modelTestB2, ⟨2⟩⟩

/-- A real constant `3/16` with radius `1/16`. -/
def modelTestConst : CertModel (CertFixed 4) := ⟨0, ⟨[([0, 0], ⟨⟨3⟩, ⟨0⟩⟩)]⟩, ⟨1⟩⟩

def modelTestZero : CertModel (CertFixed 4) := ⟨0, ⟨[]⟩, ⟨0⟩⟩

/-- Keys and mantissas of a fixed-point polynomial. -/
def modelTestView (P : CertPoly (CertFixed 4)) : List (CertKey × ℤ × ℤ) :=
  P.terms.map fun t => (t.1, t.2.re.m, t.2.im.m)

/-- Packed route: the product polynomial is the packed product's. -/
theorem modelTest_mul_packed :
    modelTestView (CertModel.mul modelTestW (modelTestCfg modelTestBook) [5] modelTestA
      modelTestB).poly =
      ((CertPoly.mulPacked (CertFixed.toMant 4) modelTestW 4 modelTestAdv modelTestBogus
        modelTestBogus modelTestBogus modelTestA.poly modelTestB.poly).map
          fun out => modelTestView out.1).getD [] ∧
    (CertModel.mul modelTestW (modelTestCfg modelTestBook) [5] modelTestA
      modelTestB).poly.terms.isEmpty = false := by
  decide +kernel

/-- A missing key gives the crude enclosure. -/
theorem modelTest_mul_missing :
    (CertModel.mul modelTestW (modelTestCfg modelTestBook) [6] modelTestA
      modelTestB).poly.terms.isEmpty = true := by
  decide +kernel

/-- Failing advice (one slot off by `+2`) gives the crude enclosure. -/
theorem modelTest_mul_failing :
    (CertModel.mul modelTestW (modelTestCfg [([5], .packed 4 modelTestAdvOff modelTestBogus
      modelTestBogus modelTestBogus)]) [5] modelTestA modelTestB).poly.terms.isEmpty = true := by
  decide +kernel

/-- A constant factor is a scalar multiplication: no advice is needed or read, even bogus advice
registered under the key; the product keys are the other factor's. -/
theorem modelTest_mul_scalar :
    (CertModel.mul modelTestW (modelTestCfg []) [9] modelTestConst modelTestB).poly.terms.map
        Prod.fst = modelTestB2.map Prod.fst ∧
    (CertModel.mul modelTestW (modelTestCfg [([9], .packed 4 modelTestBogus modelTestBogus
        modelTestBogus modelTestBogus)]) [9] modelTestB modelTestConst).poly.terms.map
        Prod.fst = modelTestB2.map Prod.fst ∧
    (CertModel.mul modelTestW (modelTestCfg []) [9] modelTestConst modelTestB).deg = 1 := by
  decide +kernel

/-- The scalar coefficients: `(3/16) · (6/16) = 18/256`, floored to `1/16`. -/
theorem modelTest_mul_scalar_coeff :
    modelTestView (CertModel.mul modelTestW (modelTestCfg []) [9] modelTestConst
      modelTestB).poly = [([0, -1], 1, 0), ([0, 0], 0, 0), ([0, 1], -2, 0), ([1, -1], -1, 0),
        ([1, 0], 1, 0), ([1, 1], 0, 0)] := by
  decide +kernel

/-- The zero model times anything is the zero model with radius zero (no advice). -/
theorem modelTest_mul_zero :
    (CertModel.mul modelTestW (modelTestCfg []) [9] modelTestZero modelTestB).poly.terms = [] ∧
    (CertModel.mul modelTestW (modelTestCfg []) [9] modelTestZero modelTestB).rad.m = 0 := by
  decide +kernel

/-- **Contract instance**: the packed-route model encloses the product of enclosed functions. -/
theorem modelTest_mul_encloses {f g : (Fin 2 → ℂ) → ℂ}
    (hf : modelTestA.Encloses 2 modelTestW.rho f) (hg : modelTestB.Encloses 2 modelTestW.rho g) :
    (CertModel.mul modelTestW (modelTestCfg modelTestBook) [5] modelTestA modelTestB).Encloses 2
      modelTestW.rho (f * g) :=
  CertModel.Encloses.mul modelTest_weight _ _ hf hg

/-! ### Rational backend -/

/-- A rational polynomial from `(key, real part)` pairs. -/
def modelTestQ (cs : List (CertKey × ℚ)) : CertPoly ℚ := ⟨cs.map fun t => (t.1, ⟨t.2, 0⟩)⟩

/-- Keys, real and imaginary parts of a rational polynomial. -/
def modelTestViewQ (P : CertPoly ℚ) : List (CertKey × ℚ × ℚ) :=
  P.terms.map fun t => (t.1, t.2.re, t.2.im)

def modelTestCfgQ : ModelConfig ℚ := ⟨100, 0, 0, fun _ _ => none, [([2], .direct)]⟩

/-- Direct route: `(1 + 2χ₁)(χ₋₁ + 1) = χ₋₁ + 3 + 2χ₁`, merged and sorted. -/
theorem modelTest_mul_direct :
    modelTestViewQ (CertModel.mul modelTestW modelTestCfgQ [2]
      ⟨0, modelTestQ [([0], 1), ([1], 2)], 0⟩ ⟨0, modelTestQ [([-1], 1), ([0], 1)], 0⟩).poly =
      [([-1], 1, 0), ([0], 3, 0), ([1], 2, 0)] := by
  decide +kernel

/-- `add` merges equal keys and keeps the lexicographic order. -/
theorem modelTest_add :
    modelTestViewQ (CertModel.add modelTestW ⟨0, modelTestQ [([0, 0], 1), ([1, 0], 2)], 1 / 10⟩
      ⟨0, modelTestQ [([0, 1], 5), ([1, 0], 3), ([2, 0], 1)], 1 / 5⟩).poly =
      [([0, 0], 1, 0), ([0, 1], 5, 0), ([1, 0], 5, 0), ([2, 0], 1, 0)] ∧
    (CertModel.add modelTestW ⟨0, modelTestQ [([0, 0], 1)], 1 / 10⟩
      ⟨0, modelTestQ [([0, 0], 1)], 1 / 5⟩).rad = 3 / 10 := by
  decide +kernel

/-- `trim` drops `χ₅/1000` (weighted size `1.1^5/1000 ≤ 1/100`) into the radius. -/
theorem modelTest_trim :
    modelTestViewQ (CertModel.trim modelTestW (1 / 100)
      ⟨0, modelTestQ [([0], 1), ([5], 1 / 1000)], 0⟩).poly = [([0], 1, 0)] ∧
    (CertModel.trim modelTestW (1 / 100)
      ⟨0, modelTestQ [([0], 1), ([5], 1 / 1000)], 0⟩).rad = (11 / 10) ^ 5 / 1000 := by
  decide +kernel

/-- `ofDeriv`: `∂₀ (3χ_{(2,1)} + χ_{(0,4)}) = 2π · (6i χ_{(2,1)})`, the `k₀ = 0` term dropped. -/
theorem modelTest_ofDeriv :
    modelTestViewQ (CertModel.ofDeriv modelTestW 0 0
      (modelTestQ [([2, 1], 3), ([0, 4], 1)])).poly = [([2, 1], 0, 6)] ∧
    (CertModel.ofDeriv modelTestW 0 0 (modelTestQ [([2, 1], 3), ([0, 4], 1)])).deg = 1 ∧
    (CertModel.ofDeriv modelTestW 0 0 (modelTestQ [([2, 1], 3), ([0, 4], 1)])).rad = 0 := by
  decide +kernel

/-- A validated rational `π` enclosure (Machin parameters `(5, 2)`). -/
def modelTestPi : PiEnclosure ℚ := ⟨314159 / 100000, 1 / 10000, 5, 2⟩

theorem modelTest_pi : checkPiEnclosure modelTestPi = true := by decide +kernel

/-- `toDeg` from degree `1` to `0`: the coefficient `1` becomes an upper bound of `2π`, within
`10⁻⁶`, and the same degree is the identity. -/
theorem modelTest_toDeg :
    (CertModel.toDeg modelTestW modelTestPi 0 ⟨1, modelTestQ [([1], 1)], 0⟩).deg = 0 ∧
    decide (0 ≤ ((CertModel.toDeg modelTestW modelTestPi 0
      ⟨1, modelTestQ [([1], 1)], 0⟩).poly.terms.headD ([], ⟨0, 0⟩)).2.re - 2 * 314159265 / 10 ^ 8 ∧
      ((CertModel.toDeg modelTestW modelTestPi 0
      ⟨1, modelTestQ [([1], 1)], 0⟩).poly.terms.headD ([], ⟨0, 0⟩)).2.re - 2 * 314159265 / 10 ^ 8
        ≤ 1 / 10 ^ 6) ∧
    decide ((CertModel.toDeg modelTestW modelTestPi 0
      ⟨1, modelTestQ [([1], 1)], 0⟩).rad ≤ 1 / 10 ^ 6) ∧
    (CertModel.toDeg modelTestW modelTestPi 1 ⟨1, modelTestQ [([1], 1)], 0⟩).rad = 0 := by
  decide +kernel

end KAM.Certificate
