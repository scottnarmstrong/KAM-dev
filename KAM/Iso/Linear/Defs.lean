/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Apost.Standing
public import KAM.Apost.Triangular
public import KAM.Torus.Objects
public import KAM.Frozen.Iso.Defs.ExtendedTorsionAverage
public import KAM.Frozen.Iso.Defs.EnergyAverage

/-!
# Part 1 (isoenergetic linear step): standing data and definitions

Definitions only (the only proof is the `ext`/`rfl` bridge `extendedTorsion_eq_bordMat`).

* `Setting` (`bpI:p1:setting`): `KAM.Apost.Standing` plus `‖DH‖ ≤ M`.
* The last row `energyRow` (`Y = DH(K) N`), the bordered matrix `bordMat` (`(A c; yᵀ 0)` over
  `Fin n ⊕ Unit`) and the bridge `extendedTorsion_eq_bordMat` to the frozen `extendedTorsion`.
* `BordData` and the explicit solution of the bordered triangular system of `bpI:p1:border-solve`:
  `bordAvg`, `bordSol`, `bordXi0`, `bordXiOmega`, `bordXiN`, `bordGL`, `bordXiL`.
* The objects of `bpI:p1:reduced`: `isoLinError`, `isoResidual`, `bordOp`.
* `AdmissibleNoTwist` (K's (A1)-(A4), (A6)).

All of K's conventions apply: operator norm scope, holomorphy as `DifferentiableOn ℂ`, pointwise
bounds. Part 1 is a specialized implementation (`τ ≥ n - 1`, positive `σ`'s) of the source
statements for `τ ≥ 0`.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator
open Matrix

namespace KAM.Iso.Linear

open KAM KAM.Torus KAM.Apost

/-- `bpI:p1:setting` (+ `#k-bridge`): K's standing data with `h := H`, `𝔅 := D` (projection
`Setting.toStanding`), plus `‖DH‖ ≤ M`, the first item of (I4). The torus data are explicit
binders of each lemma. -/
structure Setting (n : ℕ) (τ M σK σB σT : ℝ) (D : Set ((Fin n → ℂ) × (Fin n → ℂ)))
    (H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) (ω : Fin n → ℝ) (γ : ℝ) : Prop
    extends KAM.Apost.Standing n τ M σK σB σT D H ω γ where
  dH_le : ∀ z ∈ D, ‖fderiv ℂ H z‖ ≤ M

variable {n : ℕ}

/-- `Y = DH(K) N` (HL19 (6.14)); entry `b` is the frozen last-row entry of `extendedTorsion`. -/
def energyRow (H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) (K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ))
    (θ : Fin n → ℂ) : Fin n → ℂ :=
  fun b => fderiv ℂ H (K θ) (normalFrame K θ b)

/-- The bordered matrix `(A c; yᵀ 0)` over `Fin n ⊕ Unit`. -/
def bordMat (A : Matrix (Fin n) (Fin n) ℂ) (c y : Fin n → ℂ) :
    Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) ℂ :=
  Matrix.fromBlocks A (Matrix.replicateCol Unit c) (Matrix.replicateRow Unit y) 0

theorem extendedTorsion_eq_bordMat (H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ)
    (K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)) (ω : Fin n → ℝ) (θ : Fin n → ℂ) :
    KAM.Iso.extendedTorsion H K ω θ =
      bordMat (torsion H K ω θ) (fun a => (ω a : ℂ)) (energyRow H K θ) := by
  ext (a | _) (b | _) <;> rfl

/-- The data `(ηᴸ, ηᴺ, T, Y, η^ω)` of the bordered triangular system. -/
structure BordData (n : ℕ) where
  ηL : (Fin n → ℂ) → Fin n → ℂ
  ηN : (Fin n → ℂ) → Fin n → ℂ
  T : (Fin n → ℂ) → Matrix (Fin n) (Fin n) ℂ
  Y : (Fin n → ℂ) → Fin n → ℂ
  ηω : ℂ

/-- `𝒯 = (⟨T⟩ ω; ⟨Y⟩ 0)`. -/
def bordAvg (ω : Fin n → ℝ) (d : BordData n) : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) ℂ :=
  bordMat (avg d.T) (fun a => (ω a : ℂ)) (avg d.Y)

/-- `(ξ₀, ξ^ω) = 𝒯⁻¹ (⟨ηᴸ⟩ + ⟨T uᴺ⟩, η^ω + ⟨Y uᴺ⟩)`, `uᴺ = 𝓡ηᴺ = KAM.Apost.triU ω ηᴺ`. -/
def bordSol (ω : Fin n → ℝ) (d : BordData n) : Fin n ⊕ Unit → ℂ :=
  (bordAvg ω d)⁻¹ *ᵥ Sum.elim (avg d.ηL + avg (fun θ => d.T θ *ᵥ triU ω d.ηN θ))
    (fun _ => d.ηω + avg (fun θ => d.Y θ ⬝ᵥ triU ω d.ηN θ))

def bordXi0 (ω : Fin n → ℝ) (d : BordData n) : Fin n → ℂ := fun a => bordSol ω d (Sum.inl a)
def bordXiOmega (ω : Fin n → ℝ) (d : BordData n) : ℂ := bordSol ω d (Sum.inr ())

/-- `ξᴺ = ξ₀ - uᴺ`. -/
def bordXiN (ω : Fin n → ℝ) (d : BordData n) : (Fin n → ℂ) → Fin n → ℂ :=
  fun θ => bordXi0 ω d - triU ω d.ηN θ

/-- `gᴸ = T ξᴺ + ω ξ^ω - ηᴸ`. -/
def bordGL (ω : Fin n → ℝ) (d : BordData n) : (Fin n → ℂ) → Fin n → ℂ :=
  fun θ => d.T θ *ᵥ bordXiN ω d θ + bordXiOmega ω d • (fun a => (ω a : ℂ)) - d.ηL θ

/-- `ξᴸ = ξᴸ₀ + 𝓡gᴸ`. -/
def bordXiL (ω : Fin n → ℝ) (d : BordData n) (ξL0 : Fin n → ℂ) : (Fin n → ℂ) → Fin n → ℂ :=
  fun θ => ξL0 + cohR ω (bordGL ω d) θ

/-- `E_lin = E_red ξ + Ω₀E_sym ∂_ωξ - (0; Ω_Kω) ξ^ω` (HL19 (6.34)). -/
def isoLinError (H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) (K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ))
    (ω : Fin n → ℝ) (ξ : (Fin n → ℂ) → Fin n ⊕ Fin n → ℂ) (ξω : ℂ) (θ : Fin n → ℂ) :
    Fin n ⊕ Fin n → ℂ :=
  redDefect H K ω θ *ᵥ ξ θ +
      (omegaZeroMatrix n * symDefect K θ) *ᵥ fderiv ℂ ξ θ (fun l => (ω l : ℂ)) -
    ξω • Sum.elim (0 : Fin n → ℂ) (lagrangeMat K θ *ᵥ fun l => (ω l : ℂ))

/-- `Res = AΔK - ∂_ωΔK + Lωξ^ω + E`, `ΔK = Pξ`, as a `Fin n ⊕ Fin n` vector. -/
def isoResidual (H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) (K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ))
    (ω : Fin n → ℝ) (ξ : (Fin n → ℂ) → Fin n ⊕ Fin n → ℂ) (ξω : ℂ) (θ : Fin n → ℂ) :
    Fin n ⊕ Fin n → ℂ :=
  linMat H K θ *ᵥ (frameMat K θ *ᵥ ξ θ) -
      fderiv ℂ (fun y => frameMat K y *ᵥ ξ y) θ (fun l => (ω l : ℂ)) +
    ξω • (tangentMat K θ *ᵥ fun l => (ω l : ℂ)) + sumVec n (invarianceError H K ω θ)

/-- The bordered operator `Λξ - ∂_ωξ + (ω; 0) ξ^ω`. -/
def bordOp (H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) (K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ))
    (ω : Fin n → ℝ) (ξ : (Fin n → ℂ) → Fin n ⊕ Fin n → ℂ) (ξω : ℂ) (θ : Fin n → ℂ) :
    Fin n ⊕ Fin n → ℂ :=
  triangularMat (torsion H K ω θ) *ᵥ ξ θ - fderiv ℂ ξ θ (fun l => (ω l : ℂ)) +
    ξω • Sum.elim (fun l => (ω l : ℂ)) (0 : Fin n → ℂ)

/-- K's (A1)–(A4), (A6) (`KAM.Apost.Admissible` without its `twist` field). -/
structure AdmissibleNoTwist (σK σB : ℝ) (D : Set ((Fin n → ℂ) × (Fin n → ℂ)))
    (H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) (ω : Fin n → ℝ) (r β ε : ℝ)
    (K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)) : Prop where
  r_pos : 0 < r
  β_pos : 0 < β
  ε_nonneg : 0 ≤ ε
  ε_le_one : ε ≤ 1
  holo : DifferentiableOn ℂ K (complexStrip n r)
  primary : IsPrimaryOnStrip K r
  real : IsRealOnReals K
  ball_sub : ∀ θ ∈ complexStrip n r, Metric.ball (K θ) β ⊆ D
  deriv_le : ∀ θ ∈ complexStrip n r, ‖fderiv ℂ K θ‖ ≤ σK
  gram : ∀ θ ∈ complexStrip n r, IsUnit (gramMatrix K θ).det ∧ ‖(gramMatrix K θ)⁻¹‖ ≤ σB
  error_le : ∀ θ ∈ complexStrip n r, ‖invarianceError H K ω θ‖ ≤ ε

end KAM.Iso.Linear

end
