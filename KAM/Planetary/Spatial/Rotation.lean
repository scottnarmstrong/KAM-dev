/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Spatial.RotationAlgebra
public import KAM.Planetary.Spatial.Model
public import KAM.Planetary.Spatial.Elements

/-!
# Rotation invariance of the spatial model: the invariants

Source: rotation invariance for the alignment in `LP:MAIN L18` (`d = 3`); track LP,
non-frozen.

`spatialRotatePhase R z` applies `R` to every `q_i` and `p_i`.  For `Rᵀ R = 1`:
`spatialHamiltonian`, `SpatialNoCollision`, the Kepler energy, axis and action, and `|𝐞_i|` are
invariant; for `det R = 1` in addition `L_i ↦ R L_i`, `L ↦ R L` and `spatialStrongAMD` is invariant.
-/

@[expose] public noncomputable section

namespace KAM.Planetary.Spatial

open KAM.Planetary Matrix

variable {n : ℕ} {R : Matrix (Fin 3) (Fin 3) ℝ}

/-- Apply `R` to every body block of a coordinate vector. -/
def rotateBlocks (R : Matrix (Fin 3) (Fin 3) ℝ) (q : Fin (n * 3) → ℝ) : Fin (n * 3) → ℝ :=
  ofBodies3 (fun i => R *ᵥ bodyVector3 q i)

/-- Apply `R` to every `q_i` and every `p_i`. -/
def spatialRotatePhase (R : Matrix (Fin 3) (Fin 3) ℝ) (z : Phase (n * 3)) : Phase (n * 3) :=
  (rotateBlocks R z.1, rotateBlocks R z.2)

theorem bodyVector3_rotateBlocks (R : Matrix (Fin 3) (Fin 3) ℝ) (q : Fin (n * 3) → ℝ)
    (i : Fin n) : bodyVector3 (rotateBlocks R q) i = R *ᵥ bodyVector3 q i :=
  bodyVector3_ofBodies3 _ i

theorem eq_of_bodyVector3_eq {q q' : Fin (n * 3) → ℝ}
    (h : ∀ i, bodyVector3 q i = bodyVector3 q' i) : q = q' := by
  rw [← ofBodies3_bodyVector3 q, ← ofBodies3_bodyVector3 q']
  congr 1
  exact funext h

theorem rotateBlocks_rotateBlocks {R' : Matrix (Fin 3) (Fin 3) ℝ} (h : R' * R = 1)
    (q : Fin (n * 3) → ℝ) : rotateBlocks R' (rotateBlocks R q) = q := by
  refine eq_of_bodyVector3_eq fun i => ?_
  rw [bodyVector3_rotateBlocks, bodyVector3_rotateBlocks, Matrix.mulVec_mulVec, h,
    Matrix.one_mulVec]

theorem spatialRotatePhase_rotatePhase {R' : Matrix (Fin 3) (Fin 3) ℝ} (h : R' * R = 1)
    (z : Phase (n * 3)) : spatialRotatePhase R' (spatialRotatePhase R z) = z := by
  simp [spatialRotatePhase, rotateBlocks_rotateBlocks h]

section Invariants

variable (hR : Rᵀ * R = 1)
include hR

theorem spatialNoCollision_rotate_iff (q : Fin (n * 3) → ℝ) :
    SpatialNoCollision (rotateBlocks R q) ↔ SpatialNoCollision q := by
  simp only [SpatialNoCollision, bodyVector3_rotateBlocks, ← Matrix.mulVec_sub,
    spaceLength_mulVec hR]

theorem spatialKeplerEnergy_rotate (ν : Fin n → ℝ) (z : Phase (n * 3)) (i : Fin n) :
    spatialKeplerEnergy ν (spatialRotatePhase R z) i = spatialKeplerEnergy ν z i := by
  simp only [spatialKeplerEnergy, spatialRotatePhase, bodyVector3_rotateBlocks, spaceSq_mulVec hR,
    spaceLength_mulVec hR]

theorem spatialKeplerAxis_rotate (ν : Fin n → ℝ) (z : Phase (n * 3)) (i : Fin n) :
    spatialKeplerAxis ν (spatialRotatePhase R z) i = spatialKeplerAxis ν z i := by
  simp only [spatialKeplerAxis, spatialKeplerEnergy_rotate hR]

theorem spatialKeplerAction_rotate (ν : Fin n → ℝ) (z : Phase (n * 3)) (i : Fin n) :
    spatialKeplerAction ν (spatialRotatePhase R z) i = spatialKeplerAction ν z i := by
  simp only [spatialKeplerAction, spatialKeplerAxis_rotate hR]

/-- The eccentricity vector is equivariant. -/
theorem spatialKeplerEccVector_rotate (ν : Fin n → ℝ) (z : Phase (n * 3)) (i : Fin n) :
    spatialKeplerEccVector ν (spatialRotatePhase R z) i = R *ᵥ spatialKeplerEccVector ν z i := by
  simp only [spatialKeplerEccVector, spatialRotatePhase, bodyVector3_rotateBlocks,
    spaceSq_mulVec hR, spaceLength_mulVec hR, spaceDot_mulVec hR, Matrix.mulVec_sub,
    Matrix.mulVec_smul]

/-- `|𝐞_i|` is invariant. -/
theorem spaceLength_spatialKeplerEccVector_rotate (ν : Fin n → ℝ) (z : Phase (n * 3))
    (i : Fin n) :
    spaceLength (spatialKeplerEccVector ν (spatialRotatePhase R z) i) =
      spaceLength (spatialKeplerEccVector ν z i) := by
  rw [spatialKeplerEccVector_rotate hR, spaceLength_mulVec hR]

variable (hdet : R.det = 1)
include hdet

theorem planetAngularMomentum3_rotate (z : Phase (n * 3)) (i : Fin n) :
    planetAngularMomentum3 (spatialRotatePhase R z) i = R *ᵥ planetAngularMomentum3 z i := by
  simp only [planetAngularMomentum3, spatialRotatePhase, bodyVector3_rotateBlocks,
    ← mulVec_spaceCross hR hdet]

theorem angularMomentum3_rotate (z : Phase (n * 3)) :
    angularMomentum3 (spatialRotatePhase R z) = R *ᵥ angularMomentum3 z := by
  simp only [angularMomentum3_eq_sum, planetAngularMomentum3_rotate hR hdet,
    Matrix.mulVec_sum]

theorem spatialStrongAMD_rotate (ν : Fin n → ℝ) (z : Phase (n * 3)) :
    spatialStrongAMD ν (spatialRotatePhase R z) = spatialStrongAMD ν z := by
  simp only [spatialStrongAMD, spatialKeplerAction_rotate hR, angularMomentum3_rotate hR hdet,
    spaceLength_mulVec hR]

end Invariants

end KAM.Planetary.Spatial

end
