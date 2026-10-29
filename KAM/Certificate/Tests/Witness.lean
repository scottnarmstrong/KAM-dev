/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Certificate.Model.Exp
public import KAM.Certificate.Model.Inv
public import KAM.Certificate.Arith.Rat
public import KAM.Certificate.Arith.Fixed

/-!
# Witness tests (`Model/{ExpBounds,Exp,Inv}`)

Every check below is decided by `decide +kernel` (kernel reduction only).

* **Scalar bounds** (`ℚ`): `expm1Up` brackets `e - 1` and fails closed when the halved argument
  exceeds `1`; `recipOneSubUp` bounds `1/(1 - δ)` through the squaring loop and fails at `δ = 1`.
* **Exp witnesses** (`ℚ`, `n = 1`): `g₀ = 0.2 cos 2πθ` (radius `10⁻⁶`) with the Bessel witness
  `E = Σ_{|k| ≤ 4} I_k(0.2) χ_k` (ten digits) certifies a radius `≤ 10⁻⁴`; the witness `E = 1`
  only a radius `> 0.1`; the pin `exp 3` fails with `pinHalvings = 0` and passes with `2`; a
  real bound `exp(B)` with `B = 3 > 1` and no halvings fails closed.
* **Reciprocal witnesses** (`ℚ`, `n = 1`): `b = 2 + 0.5 cos 2πθ` with the witness
  `Q = Σ_{|k| ≤ 5} c_k χ_k` of `1/b` certifies a radius `≤ 10⁻⁴`; an exact constant reciprocal
  gives radius `0`; `Q = 0` fails (`δ = 1`).
* **Fixed point** (`CertFixed 128`, `n = 2`): `g₀ = 0.2 cos 2πθ₁ + 0.1 cos 2πθ₂` and the
  `289`-term witness `E = Σ_{|k₁|,|k₂| ≤ 8} I_{k₁}(0.2) I_{k₂}(0.1) χ_k` (coefficients computed
  in the kernel): radius `≤ 2⁻³⁸` (measured: the full check costs about 3 s of kernel time).
* **Contracts**: the soundness theorems instantiated on the toys.
-/

public section

namespace KAM.Certificate

open CertArith

def witnessTestW : CertWeight := ⟨1 / 100, 11 / 10⟩

theorem witnessTest_weight : checkWeight witnessTestW 0 6 = true := by decide +kernel

/-- A rational polynomial from `(key, real part)` pairs. -/
def witnessTestQ (cs : List (CertKey × ℚ)) : CertPoly ℚ := ⟨cs.map fun t => (t.1, ⟨t.2, 0⟩)⟩

def witnessTestCfg : ModelConfig ℚ :=
  ⟨100, 10, 4, fun _ _ => none, [([1, 0], .direct), ([2], .direct)]⟩

/-! ### Scalar bounds -/

theorem witnessTest_expm1Up :
    (expm1Up 3 8 (1 : ℚ)).any (fun u => decide (1718281828 / 10 ^ 9 ≤ u ∧
      u ≤ 1718281829 / 10 ^ 9)) = true := by
  decide +kernel

theorem witnessTest_expm1Up_fail : expm1Up 0 8 (2 : ℚ) = none := by decide +kernel

theorem witnessTest_recip : (recipOneSubUp (9 / 10 : ℚ)).any (fun t => decide (10 ≤ t)) = true := by
  decide +kernel

theorem witnessTest_recip_fail : recipOneSubUp (1 : ℚ) = none := by decide +kernel

/-! ### Exp witnesses -/

/-- `g₀ = 0.2 cos 2πθ`, radius `10⁻⁶`. -/
def witnessTestG : CertModel ℚ := ⟨0, witnessTestQ [([-1], 1 / 10), ([1], 1 / 10)], 1 / 10 ^ 6⟩

/-- `exp(0.2 cos 2πθ) ≈ Σ_{|k| ≤ 4} I_k(0.2) χ_k` (ten digits). -/
def witnessTestE : ExpWitness ℚ :=
  ⟨witnessTestQ [([-4], 41750 / 10 ^ 10), ([-3], 1670838 / 10 ^ 10),
    ([-2], 50166875 / 10 ^ 10), ([-1], 1005008340 / 10 ^ 10), ([0], 10100250278 / 10 ^ 10),
    ([1], 1005008340 / 10 ^ 10), ([2], 50166875 / 10 ^ 10), ([3], 1670838 / 10 ^ 10),
    ([4], 41750 / 10 ^ 10)], 0, 12⟩

theorem witnessTest_exp :
    (expWitnessRadius 1 witnessTestW witnessTestCfg witnessTestG witnessTestE).any
      (fun r => decide (r ≤ 1 / 10 ^ 4)) = true := by
  decide +kernel

theorem witnessTest_exp_bad :
    (expWitnessRadius 1 witnessTestW witnessTestCfg witnessTestG
      ⟨witnessTestQ [([0], 1)], 0, 12⟩).any (fun r => decide (1 / 10 < r)) = true := by
  decide +kernel

/-- The constant `3`. -/
def witnessTestG3 : CertModel ℚ := ⟨0, witnessTestQ [([0], 3)], 0⟩

theorem witnessTest_pin_fail :
    expWitnessRadius 1 witnessTestW witnessTestCfg witnessTestG3
      ⟨witnessTestQ [([0], 200855369232 / 10 ^ 10)], 0, 12⟩ = none := by
  decide +kernel

theorem witnessTest_pin_reduced :
    (expWitnessRadius 1 witnessTestW witnessTestCfg witnessTestG3
      ⟨witnessTestQ [([0], 200855369232 / 10 ^ 10)], 2, 20⟩).any
      (fun r => decide (r ≤ 1 / 10 ^ 6)) = true := by
  decide +kernel

theorem witnessTest_real_fail :
    expWitnessRadius 1 witnessTestW ⟨100, 10, 0, fun _ _ => none, []⟩ witnessTestG3
      ⟨witnessTestQ [([0], 200855369232 / 10 ^ 10)], 2, 12⟩ = none := by
  decide +kernel

/-! ### Reciprocal witnesses -/

/-- `b = 2 + 0.5 cos 2πθ`. -/
def witnessTestB : CertModel ℚ := ⟨0, witnessTestQ [([-1], 1 / 4), ([0], 2), ([1], 1 / 4)], 0⟩

/-- `1/b ≈ Σ_{|k| ≤ 5} c_k χ_k` (ten digits). -/
def witnessTestInv : CertPoly ℚ :=
  witnessTestQ [([-5], -170721 / 10 ^ 10), ([-4], 1344086 / 10 ^ 10),
    ([-3], -10581966 / 10 ^ 10), ([-2], 83311643 / 10 ^ 10), ([-1], -655911180 / 10 ^ 10),
    ([0], 5163977795 / 10 ^ 10), ([1], -655911180 / 10 ^ 10), ([2], 83311643 / 10 ^ 10),
    ([3], -10581966 / 10 ^ 10), ([4], 1344086 / 10 ^ 10), ([5], -170721 / 10 ^ 10)]

theorem witnessTest_inv :
    (invWitnessRadius 1 witnessTestW witnessTestCfg witnessTestB witnessTestInv).any
      (fun r => decide (r ≤ 1 / 10 ^ 4)) = true := by
  decide +kernel

theorem witnessTest_inv_exact :
    invWitnessRadius 1 witnessTestW witnessTestCfg ⟨3, witnessTestQ [([0], 2)], 0⟩
      (witnessTestQ [([0], 1 / 2)]) = some 0 := by
  decide +kernel

theorem witnessTest_inv_fail :
    invWitnessRadius 1 witnessTestW witnessTestCfg witnessTestB ⟨[]⟩ = none := by
  decide +kernel

/-! ### Fixed point, `n = 2` -/

/-- `I_k(a)`, twelve terms of the series. -/
def witnessTestBessel (a : ℚ) (k : ℕ) : ℚ :=
  ((List.range 12).map fun m =>
    (a / 2) ^ (2 * m + k) / ((m.factorial * (m + k).factorial : ℕ) : ℚ)).sum

/-- A fixed-point polynomial from `(key, mantissa of the real part)` pairs. -/
def witnessTestFix (cs : List (CertKey × ℤ)) : CertPoly (CertFixed 128) :=
  ⟨cs.map fun t => (t.1, ⟨⟨t.2⟩, ⟨0⟩⟩)⟩

def witnessTestCfgFix : ModelConfig (CertFixed 128) :=
  ⟨100, 20, 30, CertFixed.toMant 128, [([1, 0], .direct), ([1, 1], .direct)]⟩

/-- `g₀ = 0.2 cos 2πθ₁ + 0.1 cos 2πθ₂` (mantissas rounded down), radius `2⁻⁶⁸`. -/
def witnessTestGFix : CertModel (CertFixed 128) :=
  ⟨0, witnessTestFix [([-1, 0], 2 ^ 128 / 10), ([1, 0], 2 ^ 128 / 10),
    ([0, -1], 2 ^ 128 / 20), ([0, 1], 2 ^ 128 / 20)], ⟨2 ^ 60⟩⟩

/-- The keys `-K, …, K`. -/
def witnessTestRange (K : ℕ) : List ℤ := (List.range (2 * K + 1)).map fun i => (i : ℤ) - K

/-- The witness `Σ_{|k₁|,|k₂| ≤ K} I_{k₁}(0.2) I_{k₂}(0.1) χ_k` (mantissas rounded down). -/
def witnessTestEFix (K : ℕ) : ExpWitness (CertFixed 128) :=
  ⟨witnessTestFix ((witnessTestRange K).flatMap fun k₁ => (witnessTestRange K).map fun k₂ =>
    ([k₁, k₂], let q := witnessTestBessel (1 / 5) k₁.natAbs * witnessTestBessel (1 / 10) k₂.natAbs
      q.num * 2 ^ 128 / q.den)), 0, 20⟩

theorem witnessTest_exp_fixed :
    (expWitnessRadius 2 witnessTestW witnessTestCfgFix witnessTestGFix (witnessTestEFix 8)).any
      (fun r => decide (r.m ≤ 2 ^ 90)) = true := by
  decide +kernel

/-! ### Contracts -/

/-- **Contract instance**: the Bessel witness encloses `exp g` for every `g` enclosed by
`witnessTestG`. -/
theorem witnessTest_exp_encloses {gf : (Fin 1 → ℂ) → ℂ}
    (hg : witnessTestG.Encloses 1 witnessTestW.rho gf) {r : ℚ}
    (hr : expWitnessRadius 1 witnessTestW witnessTestCfg witnessTestG witnessTestE = some r) :
    (⟨0, witnessTestE.poly, r⟩ : CertModel ℚ).Encloses 1 witnessTestW.rho
      (fun θ => Complex.exp (gf θ)) :=
  expWitness_sound witnessTest_weight witnessTestCfg hg rfl hr

/-- **Contract instance**: every `b` enclosed by `witnessTestB` has no zero on the strip, and
`witnessTestInv` encloses `1/b`. -/
theorem witnessTest_inv_encloses {bf : (Fin 1 → ℂ) → ℂ}
    (hb : witnessTestB.Encloses 1 witnessTestW.rho bf) {r : ℚ}
    (hr : invWitnessRadius 1 witnessTestW witnessTestCfg witnessTestB witnessTestInv = some r) :
    (∀ θ ∈ complexStrip 1 witnessTestW.rho, bf θ ≠ 0) ∧
      (⟨0, witnessTestInv, r⟩ : CertModel ℚ).Encloses 1 witnessTestW.rho
        (fun θ => (bf θ)⁻¹) :=
  invWitness_sound witnessTest_weight witnessTestCfg hb hr

end KAM.Certificate
