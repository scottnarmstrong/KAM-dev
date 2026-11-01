/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Spatial.Rotation
public import KAM.Planetary.Spatial.Field

/-!
# Rotation invariance of the spatial model: solutions

Package LP-SP-MODEL, rotation invariance for the alignment in `LP:MAIN L18` (`d = 3`); track LP,
non-frozen; the statement surface is proposed in docs/tracks/LP/FREEZE-PROPOSAL.md.

For a rotation `R` (`Rᵀ R = 1`, `det R = 1`): the Hamilton field of `H_μ` is equivariant at
collision-free points, and `IsSpatialMovingSolutionOn ν μ J z ↔
IsSpatialMovingSolutionOn ν μ J (fun t => spatialRotatePhase R (z t))`.
-/

@[expose] public noncomputable section

namespace KAM.Planetary.Spatial

open KAM KAM.Planetary Matrix

variable {n : ℕ} {R : Matrix (Fin 3) (Fin 3) ℝ}

/-- Block rotation as a linear map. -/
def rotateBlocksLin (R : Matrix (Fin 3) (Fin 3) ℝ) :
    (Fin (n * 3) → ℝ) →ₗ[ℝ] (Fin (n * 3) → ℝ) where
  toFun := rotateBlocks R
  map_add' a b := eq_of_bodyVector3_eq fun i => by
    simp [bodyVector3_rotateBlocks, bodyVector3_add, Matrix.mulVec_add]
  map_smul' c a := eq_of_bodyVector3_eq fun i => by
    simp [bodyVector3_rotateBlocks, bodyVector3_smul, Matrix.mulVec_smul]

/-- Phase rotation as a continuous linear map. -/
def spatialRotatePhaseCLM (R : Matrix (Fin 3) (Fin 3) ℝ) : Phase (n * 3) →L[ℝ] Phase (n * 3) :=
  LinearMap.toContinuousLinearMap ((rotateBlocksLin R).prodMap (rotateBlocksLin R))

theorem spatialRotatePhaseCLM_apply (z : Phase (n * 3)) :
    spatialRotatePhaseCLM R z = spatialRotatePhase R z := rfl

theorem spatialGKernel_rotate (hR : Rᵀ * R = 1) (q : Fin n → Fin 3 → ℝ) (i : Fin n) :
    spatialGKernel (fun j => R *ᵥ q j) i = R *ᵥ spatialGKernel q i := by
  simp only [spatialGKernel, spaceLength_mulVec hR, Matrix.mulVec_smul]

theorem spatialFKernel_rotate (hR : Rᵀ * R = 1) (ν : Fin n → ℝ) (q : Fin n → Fin 3 → ℝ)
    (i : Fin n) :
    spatialFKernel ν (fun j => R *ᵥ q j) i = R *ᵥ spatialFKernel ν q i := by
  simp only [spatialFKernel, ← Matrix.mulVec_sub, spaceLength_mulVec hR, Matrix.mulVec_sum,
    Matrix.mulVec_smul]

/-- The Hamilton field of `H_μ` is rotation-equivariant at collision-free points. -/
theorem hamiltonianVectorField_spatial_rotate (hR : Rᵀ * R = 1) (ν : Fin n → ℝ) (μ : ℝ)
    {z : Phase (n * 3)} (hz : SpatialNoCollision z.1) :
    hamiltonianVectorField (spatialHamiltonian ν μ) (spatialRotatePhase R z) =
      spatialRotatePhase R (hamiltonianVectorField (spatialHamiltonian ν μ) z) := by
  have hz' : SpatialNoCollision (spatialRotatePhase R z).1 :=
    (spatialNoCollision_rotate_iff hR z.1).2 hz
  refine Prod.ext (eq_of_bodyVector3_eq fun i => ?_) (eq_of_bodyVector3_eq fun i => ?_)
  · show bodyVector3 (hamiltonianVectorField (spatialHamiltonian ν μ) (spatialRotatePhase R z)).1 i
      = bodyVector3 (rotateBlocks R (hamiltonianVectorField (spatialHamiltonian ν μ) z).1) i
    rw [bodyVector3_hamiltonianVectorField_spatial_fst ν μ hz',
      bodyVector3_rotateBlocks, bodyVector3_hamiltonianVectorField_spatial_fst ν μ hz]
    simp only [spatialRotatePhase, bodyVector3_rotateBlocks, Matrix.mulVec_add,
      Matrix.mulVec_smul, Matrix.mulVec_sum]
  · show bodyVector3 (hamiltonianVectorField (spatialHamiltonian ν μ) (spatialRotatePhase R z)).2 i
      = bodyVector3 (rotateBlocks R (hamiltonianVectorField (spatialHamiltonian ν μ) z).2) i
    rw [bodyVector3_hamiltonianVectorField_spatial_snd ν μ hz',
      bodyVector3_rotateBlocks, bodyVector3_hamiltonianVectorField_spatial_snd ν μ hz]
    simp only [spatialRotatePhase, bodyVector3_rotateBlocks, Matrix.mulVec_add,
      Matrix.mulVec_smul, spatialGKernel_rotate hR, spatialFKernel_rotate hR]

/-- Forward direction of rotation invariance of solutions. -/
theorem isSpatialMovingSolutionOn_rotate (hR : Rᵀ * R = 1) {ν : Fin n → ℝ} {μ : ℝ} {J : Set ℝ}
    {z : ℝ → Phase (n * 3)} (hz : IsSpatialMovingSolutionOn ν μ J z) :
    IsSpatialMovingSolutionOn ν μ J (fun t => spatialRotatePhase R (z t)) := by
  refine ⟨fun t ht => ⟨Set.mem_univ _, ?_, ?_⟩, fun t ht => ?_⟩
  · exact differentiableAt_spatialHamiltonian ν μ
      ((spatialNoCollision_rotate_iff hR (z t).1).2 (hz.2 t ht))
  · have h := (spatialRotatePhaseCLM (n := n) (R := R)).hasFDerivAt.comp_hasDerivAt t
      (hz.1 t ht).2.2
    rw [hamiltonianVectorField_spatial_rotate hR ν μ (hz.2 t ht)]
    exact h
  · exact (spatialNoCollision_rotate_iff hR (z t).1).2 (hz.2 t ht)

/-- **Rotation invariance of solutions** (for the alignment in `LP:MAIN L18`): for `R` with
`Rᵀ R = 1` (in particular every rotation, `det R = 1`), `z` is a spatial moving solution iff
`R ∘ z` is; `det R = 1` is not needed. -/
theorem isSpatialMovingSolutionOn_rotate_iff (hR : Rᵀ * R = 1)
    {ν : Fin n → ℝ} {μ : ℝ} {J : Set ℝ} {z : ℝ → Phase (n * 3)} :
    IsSpatialMovingSolutionOn ν μ J z ↔
      IsSpatialMovingSolutionOn ν μ J (fun t => spatialRotatePhase R (z t)) := by
  refine ⟨isSpatialMovingSolutionOn_rotate hR, fun h => ?_⟩
  have hR' : (Rᵀ)ᵀ * Rᵀ = 1 := by
    rw [Matrix.transpose_transpose]; exact mul_transpose_eq_one hR
  have h2 := isSpatialMovingSolutionOn_rotate (R := Rᵀ) hR' h
  have hback : (fun t => spatialRotatePhase Rᵀ (spatialRotatePhase R (z t))) = z := by
    funext t
    exact spatialRotatePhase_rotatePhase (R := R) (R' := Rᵀ) hR (z t)
  rw [hback] at h2
  exact h2

end KAM.Planetary.Spatial

end
