/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Torus.Basic
public import KAM.Frozen.Defs.GramMatrix
public import KAM.Frozen.Defs.HamiltonianVectorFieldC
public import KAM.Frozen.Defs.InvarianceError
public import KAM.Matrix.Norms
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.Data.Matrix.Block

/-!
# The objects of Definition `bp:p2:objects`

Blueprint Part 2, Definition `bp:p2:objects`. The objects attached to a torus `K`, a Hamiltonian
`h` and a frequency `ω` are total functions of the angle `θ`:
holomorphy, `K(T_r) ⊆ 𝔅` and `det G ≠ 0` are hypotheses of the lemmas that use the objects, not
part of the definitions. All `2n`-row matrices are indexed by `Fin n ⊕ Fin n`; the vector `E` of
the frozen `KAM.invarianceError` enters products as `KAM.Torus.sumVec n E`.

| Blueprint | Lean |
|---|---|
| `L = DK` | `tangentMat K θ` |
| `A = DX_h ∘ K` | `linMat h K θ` |
| `Ω_K = Lᵀ Ω₀ L` | `lagrangeMat K θ` |
| `N = Ω₀ L B` | `normalMat K θ` |
| `P = (L N)` | `frameMat K θ` |
| `X_N = A N - ∂_ω N` | `normalFieldMat h K ω θ` |
| `E_sym = Pᵀ Ω₀ P - Ω₀` | `symDefect K θ` |
| `Q = -Ω₀ Pᵀ Ω₀` | `reducer K θ` |
| `η`, `ηᴸ`, `ηᴺ` | `eta`, `etaL`, `etaN` |
| `DE`, `Λ`, `E_red` | `errDerivMat`, `triangularMat T`, `redDefect` |

The Gram matrix `G`, its inverse `B`, the error `E`, the torsion `T` and its average `⟨T⟩` are the
frozen `gramMatrix`, `(gramMatrix K θ)⁻¹`, `invarianceError`, `torsion` and `torsionAverage`
(their agreement with the matrix formulas is `bp:p2:frozen-agreement`). The displayed block form of
`η` is `KAM.Torus.eta_eq_sumElim`.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator
open Matrix MeasureTheory Filter Topology

namespace KAM.Torus

variable {n : ℕ} (h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ)
  (K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)) (ω : Fin n → ℝ)

/-- `L = DK` (`2n × n`). The Gram matrix `G = LᵀL` and `B = G⁻¹` are the frozen
`gramMatrix K θ` and `(gramMatrix K θ)⁻¹`; `E` is the frozen `invarianceError h K ω θ`. -/
def tangentMat (θ : Fin n → ℂ) : Matrix (Fin n ⊕ Fin n) (Fin n) ℂ := colMat (fderiv ℂ K θ)

/-- `A = DX_h ∘ K` (`2n × 2n`). -/
def linMat (θ : Fin n → ℂ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ :=
  sqMat (fderiv ℂ (hamiltonianVectorFieldℂ h) (K θ))

/-- `Ω_K = Lᵀ Ω₀ L`. -/
def lagrangeMat (θ : Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  (tangentMat K θ)ᵀ * omegaZeroMatrix n * tangentMat K θ

/-- `N = Ω₀ L B`. -/
def normalMat (θ : Fin n → ℂ) : Matrix (Fin n ⊕ Fin n) (Fin n) ℂ :=
  omegaZeroMatrix n * tangentMat K θ * (gramMatrix K θ)⁻¹

/-- `P = (L N)`. -/
def frameMat (θ : Fin n → ℂ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ :=
  Matrix.fromCols (tangentMat K θ) (normalMat K θ)

/-- `X_N = A N - ∂_ω N`. The torsion `T = Nᵀ Ω₀ X_N` is the frozen `torsion h K ω θ`
(`torsion_eq_mat`), `⟨T⟩` the frozen `torsionAverage h K ω` (`torsionAverage_eq_avg`). -/
def normalFieldMat (θ : Fin n → ℂ) : Matrix (Fin n ⊕ Fin n) (Fin n) ℂ :=
  linMat h K θ * normalMat K θ - fderiv ℂ (normalMat K) θ (fun l => (ω l : ℂ))

/-- `E_sym = Pᵀ Ω₀ P - Ω₀`. -/
def symDefect (θ : Fin n → ℂ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ :=
  (frameMat K θ)ᵀ * omegaZeroMatrix n * frameMat K θ - omegaZeroMatrix n

/-- `Q = -Ω₀ Pᵀ Ω₀`. -/
def reducer (θ : Fin n → ℂ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ :=
  -(omegaZeroMatrix n * (frameMat K θ)ᵀ * omegaZeroMatrix n)

/-- `η = Ω₀ Pᵀ Ω₀ E`. -/
def eta (θ : Fin n → ℂ) : Fin n ⊕ Fin n → ℂ :=
  (omegaZeroMatrix n * (frameMat K θ)ᵀ * omegaZeroMatrix n) *ᵥ
    sumVec n (invarianceError h K ω θ)

/-- `ηᴸ = -Nᵀ Ω₀ E`. -/
def etaL (θ : Fin n → ℂ) : Fin n → ℂ :=
  -(((normalMat K θ)ᵀ * omegaZeroMatrix n) *ᵥ sumVec n (invarianceError h K ω θ))

/-- `ηᴺ = Lᵀ Ω₀ E`. -/
def etaN (θ : Fin n → ℂ) : Fin n → ℂ :=
  ((tangentMat K θ)ᵀ * omegaZeroMatrix n) *ᵥ sumVec n (invarianceError h K ω θ)

/-- `DE` as a `2n × n` matrix. -/
def errDerivMat (θ : Fin n → ℂ) : Matrix (Fin n ⊕ Fin n) (Fin n) ℂ :=
  colMat (fderiv ℂ (invarianceError h K ω) θ)

/-- `Λ = (0 T; 0 0)`. -/
def triangularMat (T : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ :=
  Matrix.fromBlocks 0 T 0 0

/-- `E_red` of Lemma `bp:p2:frame-identities`(e). -/
def redDefect (θ : Fin n → ℂ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ :=
  Matrix.fromBlocks ((normalMat K θ)ᵀ * omegaZeroMatrix n * errDerivMat h K ω θ) 0
    (-((tangentMat K θ)ᵀ * omegaZeroMatrix n * errDerivMat h K ω θ))
    ((errDerivMat h K ω θ)ᵀ * omegaZeroMatrix n * normalMat K θ)

/-- `Ω₀` acts on a vector `(a, b)` indexed by `Fin n ⊕ Fin n` as `(-b, a)`. -/
theorem omegaZeroMatrix_mulVec_sumElim (a b : Fin n → ℂ) :
    omegaZeroMatrix n *ᵥ Sum.elim a b = Sum.elim (-b) a := by
  rw [omegaZeroMatrix, Matrix.fromBlocks_mulVec]
  simp [Matrix.neg_mulVec]

/-- Blueprint `bp:p2:objects` (the displayed block form of `η`; proof `step:p2:fi-q`). -/
theorem eta_eq_sumElim (θ : Fin n → ℂ) : eta h K ω θ = Sum.elim (etaL h K ω θ) (etaN h K ω θ) :=
  by
  simp only [eta, etaL, etaN, frameMat, ← Matrix.mulVec_mulVec, Matrix.transpose_fromCols,
    Matrix.fromRows_mulVec, omegaZeroMatrix_mulVec_sumElim]


end KAM.Torus

end
