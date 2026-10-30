/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Certificate.Torsion.Models
public import KAM.Certificate.Torsion.Average
public import KAM.Certificate.Arith.Rat

/-!
# Torsion tests (`Torsion/Models`, `Torsion/Average`)

Every check below is decided by `decide +kernel` (kernel reduction only), in `ℚ`.

* **Averaging check, bordered form**: the bordered average `[[0, 1], [1, 0]]` at `n = 1` has a
  singular (zero) torsion block and is invertible only through the border (the pattern
  of the lunar tori); the self-inverse witness passes, with radius `10⁻³` in every entry.
* **Fail closed**: the witness `0` (`δ_T ≥ 1`), a too small bound `σT - μ`, an entry of degree
  `1`, and radii too large for the witness.
* **Shape (negative test 9)**: the self-inverse `A = [1 0 0; 0 0 1; 0 1 0]` is a valid
  inverse pair with zero defect and passes `torsionAvgCheck 2`, but fails `torsionAvgCheck 1`
  as a model matrix (`3` rows) and as a witness.
* **Pipeline, `n = 1`**: `H = I²/2`, `K(θ) = (θ + U/2π, A)` with `U = 0.1 cos 2πθ`,
  `A = 1 + 0.01 cos 2πθ`, the Gram witness `1 + 0.2 sin 2πθ`, the box `ω ∈ [0.999, 1.001]`,
  `s = 1`: `torsionModels` succeeds, the models have shape `2 × 2`, and the witness
  `S = [[0, 1.01], [1, -1]]` passes the averaging check at `σT - μ = 4` (it fails at `3`).
* **Contracts**: `torsionModels_sound` and `torsionAvgCheck_sound` on the pipeline: the
  bordered torsion average of the toy is invertible for EVERY `ω` in the box.
-/

public section

namespace KAM.Certificate

open CertArith

open scoped Matrix.Norms.Operator

def torsTestW : CertWeight := ⟨1 / 100, 11 / 10⟩

theorem torsTest_weight : checkWeight torsTestW 0 6 = true := by decide +kernel

def torsTestPi : PiEnclosure ℚ := ⟨314159 / 100000, 1 / 10000, 5, 2⟩

theorem torsTest_pi : checkPiEnclosure torsTestPi = true := by decide +kernel

/-! ### The averaging check -/

/-- The constant model `c` with radius `r` (`n = 1`, key `[0]`). -/
def torsTestConst (c r : ℚ) (deg : ℤ := 0) : CertModel ℚ := ⟨deg, ⟨[([0], ⟨c, 0⟩)]⟩, r⟩

def torsTestMat (A : List (List ℚ)) (r : ℚ) : ModelMatrix ℚ :=
  A.map fun row => row.map fun c => torsTestConst c r

def torsTestCC (A : List (List ℚ)) : List (List (CC ℚ)) := A.map fun row => row.map fun c => ⟨c, 0⟩

def torsTestSwap : List (List ℚ) := [[0, 1], [1, 0]]

/-- Singular torsion block, invertible through the border. -/
theorem torsTest_border :
    torsionAvgCheck 1 (torsTestMat torsTestSwap (1 / 1000)) (torsTestCC torsTestSwap) 2 = true := by
  decide +kernel

theorem torsTest_failClosed :
    torsionAvgCheck 1 (torsTestMat torsTestSwap (1 / 1000)) (torsTestCC [[0, 0], [0, 0]]) 100 =
        false ∧
      torsionAvgCheck 1 (torsTestMat torsTestSwap (1 / 1000)) (torsTestCC torsTestSwap) 1 =
        false ∧
      torsionAvgCheck 1 [[torsTestConst 0 0 1, torsTestConst 1 0], [torsTestConst 1 0,
        torsTestConst 0 0]] (torsTestCC torsTestSwap) 2 = false ∧
      torsionAvgCheck 1 (torsTestMat torsTestSwap (1 / 2)) (torsTestCC torsTestSwap) 100 =
        false := by
  decide +kernel

/-- The self-inverse `3 × 3` pair. -/
def torsTestA3 : List (List ℚ) := [[1, 0, 0], [0, 0, 1], [0, 1, 0]]

/-- **Shape.** A valid inverse pair at `n = 2`, rejected at `n = 1` (model matrix or witness). -/
theorem torsTest_F7 :
    torsionAvgCheck 2 (torsTestMat torsTestA3 0) (torsTestCC torsTestA3) 2 = true ∧
      torsionAvgCheck 1 (torsTestMat torsTestA3 0) (torsTestCC torsTestA3) 100 = false ∧
      torsionAvgCheck 1 (torsTestMat torsTestSwap 0) (torsTestCC torsTestA3) 100 = false ∧
      torsionAvgCheck 1 (torsTestMat torsTestA3 0) (torsTestCC torsTestSwap) 100 = false := by
  decide +kernel

/-! ### The pipeline at `n = 1` -/

/-- Every torsion, Gram and composition product key, advised `direct`. -/
def torsTestCfg : ModelConfig ℚ :=
  ⟨100, 10, 4, fun _ _ => none,
    (((List.range 11).flatMap fun t => (List.range 4).flatMap fun i => (List.range 4).flatMap
      fun j => (List.range 4).map fun k => [4, t, i, j, k]) ++
     ((List.range 2).flatMap fun t => (List.range 4).flatMap fun i => (List.range 4).flatMap
      fun j => (List.range 4).map fun k => [3, t, i, j, k]) ++
     ((List.range 32).map fun k => [0, k])).map fun key => (key, .direct)⟩

/-- `c + a cos 2πθ` as real data. -/
def torsTestCos (c a : ℚ) : CertRealPoly ℚ := ⟨c, [([1], ⟨a / 2, 0⟩)]⟩

/-- `K(θ) = (θ + U/2π, A)`, `U = 0.1 cos 2πθ`, `A = 1 + 0.01 cos 2πθ`. -/
def torsTestK : CertEmbedding ℚ := ⟨[-1], [torsTestCos 0 (1 / 10)], [0], [torsTestCos 1 (1 / 100)]⟩

/-- `H = I²/2`. -/
def torsTestH : HamExpr 1 := .mul (.const (1 / 2)) (.mul (.action 0) (.action 0))

/-- The Gram witness `1 + 0.2 sin 2πθ`. -/
def torsTestB : List (List (CertPoly ℚ)) :=
  [[⟨[([-1], ⟨0, 1 / 10⟩), ([0], ⟨1, 0⟩), ([1], ⟨0, -1 / 10⟩)]⟩]]

def torsTestWit : Witnesses ℚ := ⟨[], [], []⟩

def torsTestBox : FreqBox := [(1, 1 / 1000)]

/-- The averaging witness `≈ [[0, 1/0.99], [1, -0.985/0.99]]`. -/
def torsTestS : List (List (CC ℚ)) := torsTestCC [[0, 101 / 100], [1, -1]]

def torsTestModels (δβ : ℚ × ℚ) : Option (ModelMatrix ℚ) :=
  torsionModels 1 torsTestH torsTestK torsTestWit torsTestB δβ torsTestBox 1 torsTestW
    torsTestCfg torsTestPi

def torsTestRun (σ : ℚ) : Bool :=
  match gramCheck 1 torsTestK torsTestB torsTestW torsTestCfg torsTestPi 2 with
  | some δβ => (torsTestModels δβ).any fun T => listShapeOk 2 T && torsionAvgCheck 1 T torsTestS σ
  | none => false

theorem torsTest_pipeline : torsTestRun 4 = true := by decide +kernel

theorem torsTest_pipelineFail : torsTestRun 3 = false := by decide +kernel

/-! ### Contracts -/

theorem torsTest_sound {δβ : ℚ × ℚ}
    (hG : gramCheck 1 torsTestK torsTestB torsTestW torsTestCfg torsTestPi 2 = some δβ)
    {T : ModelMatrix ℚ} (hT : torsTestModels δβ = some T) {ω : Fin 1 → ℝ}
    (hω : FreqEncloses 1 torsTestBox ω) (σ : ℚ) (hA : torsionAvgCheck 1 T torsTestS σ = true) :
    IsUnit (KAM.Iso.extendedTorsionAverage torsTestH.eval (torsTestK.eval 1)
        (((1 : ℚ) : ℝ) • ω)).det ∧
      ∀ i, ∑ j, ‖(KAM.Iso.extendedTorsionAverage torsTestH.eval (torsTestK.eval 1)
        (((1 : ℚ) : ℝ) • ω))⁻¹ i j‖ ≤ σ := by
  obtain ⟨-, hEnc, hcont⟩ := torsionModels_sound le_rfl isOpen_univ
    (by simp [HamExpr.NonvanishingOn, torsTestH]) torsTest_weight (fun _ _ => Set.mem_univ _)
    torsTestWit torsTestB torsTestCfg torsTest_pi hG torsTestBox 1 hT hω
  exact torsionAvgCheck_sound (CertWeight.rho_pos torsTest_weight) hEnc hcont torsTestS σ hA

/-- End to end: the bordered torsion average of the toy is invertible, with inverse row sums
`≤ 4`, for every frequency in the box. -/
theorem torsTest_endToEnd {ω : Fin 1 → ℝ} (hω : FreqEncloses 1 torsTestBox ω) :
    IsUnit (KAM.Iso.extendedTorsionAverage torsTestH.eval (torsTestK.eval 1)
        (((1 : ℚ) : ℝ) • ω)).det ∧
      ∀ i, ∑ j, ‖(KAM.Iso.extendedTorsionAverage torsTestH.eval (torsTestK.eval 1)
        (((1 : ℚ) : ℝ) • ω))⁻¹ i j‖ ≤ ((4 : ℚ) : ℝ) := by
  have h := torsTest_pipeline
  unfold torsTestRun at h
  split at h
  · rename_i δβ hG
    simp only [Option.any_eq_true, Bool.and_eq_true] at h
    obtain ⟨T, hT, hA⟩ := h
    exact torsTest_sound hG hT hω 4 hA.2
  · exact absurd h Bool.false_ne_true

end KAM.Certificate
