/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Certificate.Gram
public import KAM.Certificate.Arith.Rat

/-!
# Gram check tests (`Gram`)

Every check below is decided by `decide +kernel` (kernel reduction only), in `ℚ`.

* **`n = 1`**: `K(θ) = (θ + U/2π, A)` with `U = 0.1 cos 2πθ`, `A = 1 + 0.01 cos 2πθ`, so
  `G = (1 - 0.1 sin)² + (0.02π sin)²`. The witness `B = 1` certifies `δ ∈ (0.2, 0.3)`, `β = 1`;
  the refined witness `B = 1 + 0.2 sin` certifies a smaller `δ` (the `B·G` products are genuine
  model products); `σB - μ = 2` passes and `σB - μ = 1` fails.
* **Fail closed**: the witness `B = 0` (`δ = 1`), a witness of the wrong shape, and a negative
  bound `σB - μ` make `gramCheck` return `none`.
* **`n = 2`**: `U = (0.1 cos 2πθ₁, 0)`, `A = (1 + 0.01 cos 2πθ₁, 1)`: the off-diagonal Gram
  entries are exactly zero (empty polynomial, radius `0`), the lower triangle is the upper one,
  and `B = I` passes.
* **Contracts**: `gramModels_sound` and `gramCheck_sound` instantiated on the toys.
-/

public section

namespace KAM.Certificate

open CertArith

open scoped Matrix.Norms.Operator

def gramTestW : CertWeight := ⟨1 / 100, 11 / 10⟩

theorem gramTest_weight : checkWeight gramTestW 0 6 = true := by decide +kernel

def gramTestPi : PiEnclosure ℚ := ⟨314159 / 100000, 1 / 10000, 5, 2⟩

theorem gramTest_pi : checkPiEnclosure gramTestPi = true := by decide +kernel

/-- `c + a cos 2πθ₁` as real data (keys padded by `pad`). -/
def gramTestCos (c a : ℚ) (pad : List ℤ) : CertRealPoly ℚ := ⟨c, [(1 :: pad, ⟨a / 2, 0⟩)]⟩

/-- Every Gram product key `[3, 0|1, i, j, k]` with `i, j, k < 4`, advised `direct`. -/
def gramTestCfg : ModelConfig ℚ :=
  ⟨100, 10, 4, fun _ _ => none,
    ((List.range 2).flatMap fun s => (List.range 4).flatMap fun i => (List.range 4).flatMap
      fun j => (List.range 4).map fun k => [3, s, i, j, k]).map fun key => (key, .direct)⟩

/-! ### `n = 1` -/

/-- `K(θ) = (θ + U/2π, A)`, `U = 0.1 cos 2πθ`, `A = 1 + 0.01 cos 2πθ`. -/
def gramTestK : CertEmbedding ℚ := ⟨[-1], [gramTestCos 0 (1 / 10) []], [0],
  [gramTestCos 1 (1 / 100) []]⟩

/-- `1 + 0.2 sin 2πθ = 1 - 0.1 i χ_1 + 0.1 i χ_{-1}`. -/
def gramTestB : List (List (CertPoly ℚ)) :=
  [[⟨[([-1], ⟨0, 1 / 10⟩), ([0], ⟨1, 0⟩), ([1], ⟨0, -1 / 10⟩)]⟩]]

def gramTestOne (n : ℕ) : List (List (CertPoly ℚ)) :=
  (List.range n).map fun i => (List.range n).map fun j =>
    if i = j then ⟨[(List.replicate n 0, ⟨1, 0⟩)]⟩ else ⟨[]⟩

def gramTestRun (B : List (List (CertPoly ℚ))) (σ : ℚ) : Option (ℚ × ℚ) :=
  gramCheck 1 gramTestK B gramTestW gramTestCfg gramTestPi σ

theorem gramTest_one :
    (gramTestRun (gramTestOne 1) 2).any (fun δβ =>
      decide (1 / 5 < δβ.1 ∧ δβ.1 < 3 / 10 ∧ δβ.2 = 1)) = true := by
  decide +kernel

/-- The refined witness: genuine `B·G` products, a smaller defect. -/
theorem gramTest_refined :
    (gramTestRun gramTestB 2).any (fun δβ =>
      decide (δβ.1 < 1 / 10 ∧ 6 / 5 < δβ.2 ∧ δβ.2 < 5 / 4)) = true := by
  decide +kernel

/-- `β/(1 - δ) ≈ 1.3 > 1`: fail closed. -/
theorem gramTest_sigmaFail : gramTestRun (gramTestOne 1) 1 = none := by
  decide +kernel

theorem gramTest_negSigma : gramTestRun (gramTestOne 1) (-1) = none := by
  decide +kernel

/-- The witness `B = 0`: `δ = 1`, fail closed. -/
theorem gramTest_zero : gramTestRun [[⟨[]⟩]] 100 = none := by
  decide +kernel

theorem gramTest_shape : gramTestRun [] 100 = none ∧ gramTestRun [[⟨[]⟩, ⟨[]⟩]] 100 = none := by
  decide +kernel

/-! ### `n = 2` -/

/-- `U = (0.1 cos 2πθ₁, 0)`, `A = (1 + 0.01 cos 2πθ₁, 1)`. -/
def gramTestK2 : CertEmbedding ℚ :=
  ⟨[-1, -1], [gramTestCos 0 (1 / 10) [0], ⟨0, []⟩], [0, 0], [gramTestCos 1 (1 / 100) [0], ⟨1, []⟩]⟩

/-- The off-diagonal entries are exactly zero and shared; `G₂₂ = 1` exactly. -/
theorem gramTest_n2_models :
    let G := gramModels 2 gramTestK2 gramTestW gramTestCfg gramTestPi
    G.length == 2 && G.all (fun r => r.length == 2) &&
      (modelMatrixEntry G 0 1).poly.terms.isEmpty && decide ((modelMatrixEntry G 0 1).rad = 0) &&
      (modelMatrixEntry G 1 0).poly.terms.isEmpty && decide ((modelMatrixEntry G 1 0).rad = 0) &&
      decide ((modelMatrixEntry G 1 1).rad = 0) = true := by
  decide +kernel

theorem gramTest_n2 :
    (gramCheck 2 gramTestK2 (gramTestOne 2) gramTestW gramTestCfg gramTestPi 2).any (fun δβ =>
      decide (1 / 5 < δβ.1 ∧ δβ.1 < 3 / 10 ∧ δβ.2 = 1)) = true := by
  decide +kernel

/-! ### Contracts -/

theorem gramTest_models_sound :
    (gramModels 2 gramTestK2 gramTestW gramTestCfg gramTestPi).Encloses 2 (fun i : Fin 2 => i.val)
      gramTestW.rho (gramMatrix (gramTestK2.eval 2)) :=
  gramModels_sound _ gramTest_weight _ gramTest_pi

theorem gramTest_sound {δβ : ℚ × ℚ} (h : gramTestRun gramTestB 2 = some δβ) :
    val δβ.1 < 1 ∧ ∀ θ ∈ complexStrip 1 gramTestW.rho,
      IsUnit (gramMatrix (gramTestK.eval 1) θ).det ∧
      (∀ i, ∑ j, ‖(gramMatrix (gramTestK.eval 1) θ)⁻¹ i j‖ ≤ (2 : ℚ)) ∧
      ‖(gramMatrix (gramTestK.eval 1) θ)⁻¹ - polyMatrix 1 gramTestB θ‖ ≤
        val δβ.1 * val δβ.2 / (1 - val δβ.1) :=
  gramCheck_sound le_rfl _ _ gramTest_weight _ gramTest_pi _ h

end KAM.Certificate
