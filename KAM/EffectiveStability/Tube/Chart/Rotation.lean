/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.Tube.Chart.Bracket
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# The modal rotation (T2-CONF, N2-Chart, target (A))

For a real matrix `A`, `rotMap A x = (A *ᵥ x.1, A *ᵥ x.2)` acts by the same matrix on positions and
momenta. For an orthogonal `V` (`Vᵀ * V = 1`), `R = rotMap Vᵀ` and `Rinv = rotMap V` are inverse to
each other and symplectic, so they transport rates along Hamiltonian vector fields.

* `rotMap_rotMap_transpose`, `rotMap_transpose_rotMap`: `Rinv ∘ R = id`, `R ∘ Rinv = id`.
* `symplecticForm_rotMap`: `rotMap A` is symplectic when `Aᵀ * A = 1`.
* `fderiv_comp_rotMap_apply_hamiltonianVectorField`:
  `fderiv ℝ (G ∘ R) x (X_H x) = fderiv ℝ G (R x) (X_{H ∘ Rinv} (R x))`.
* `contDiffAt_comp_rotMap`, `contDiffOn_comp_rotMap`, `differentiableAt_comp_rotMap`: regularity of
  `H ∘ rotMap A`.
-/

@[expose] public noncomputable section

namespace KAM.EffectiveStability.Tube

open KAM Matrix

variable {n : ℕ}

/-- The same matrix on positions and momenta: `x ↦ (A *ᵥ x.1, A *ᵥ x.2)`. -/
def rotMap (A : Matrix (Fin n) (Fin n) ℝ) (x : (Fin n → ℝ) × (Fin n → ℝ)) :
    (Fin n → ℝ) × (Fin n → ℝ) :=
  (A *ᵥ x.1, A *ᵥ x.2)

/-- `rotMap A` as a continuous linear map. -/
def rotCLM (A : Matrix (Fin n) (Fin n) ℝ) :
    (Fin n → ℝ) × (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) × (Fin n → ℝ) :=
  LinearMap.toContinuousLinearMap ((Matrix.mulVecLin A).prodMap (Matrix.mulVecLin A))

theorem rotCLM_apply (A : Matrix (Fin n) (Fin n) ℝ) (x : (Fin n → ℝ) × (Fin n → ℝ)) :
    rotCLM A x = rotMap A x := rfl

theorem rotMap_eq_rotCLM (A : Matrix (Fin n) (Fin n) ℝ) : rotMap A = ⇑(rotCLM A) := rfl

theorem hasFDerivAt_rotMap (A : Matrix (Fin n) (Fin n) ℝ) (x : (Fin n → ℝ) × (Fin n → ℝ)) :
    HasFDerivAt (rotMap A) (rotCLM A) x := by
  rw [rotMap_eq_rotCLM]
  exact (rotCLM A).hasFDerivAt

theorem fderiv_rotMap (A : Matrix (Fin n) (Fin n) ℝ) (x : (Fin n → ℝ) × (Fin n → ℝ)) :
    fderiv ℝ (rotMap A) x = rotCLM A :=
  (hasFDerivAt_rotMap A x).fderiv

theorem contDiff_rotMap (A : Matrix (Fin n) (Fin n) ℝ) {k : WithTop ℕ∞} :
    ContDiff ℝ k (rotMap A) := by
  rw [rotMap_eq_rotCLM]
  exact (rotCLM A).contDiff

theorem differentiable_rotMap (A : Matrix (Fin n) (Fin n) ℝ) : Differentiable ℝ (rotMap A) :=
  fun x => (hasFDerivAt_rotMap A x).differentiableAt

theorem rotMap_rotMap (A B : Matrix (Fin n) (Fin n) ℝ) (x : (Fin n → ℝ) × (Fin n → ℝ)) :
    rotMap A (rotMap B x) = rotMap (A * B) x := by
  simp [rotMap, Matrix.mulVec_mulVec]

theorem rotMap_one (x : (Fin n → ℝ) × (Fin n → ℝ)) : rotMap 1 x = x := by
  simp [rotMap]

/-- `Vᵀ * V = 1` implies `V * Vᵀ = 1` (square matrices). -/
theorem mul_transpose_eq_one {V : Matrix (Fin n) (Fin n) ℝ} (hV : Vᵀ * V = 1) : V * Vᵀ = 1 :=
  mul_eq_one_comm.1 hV

/-- `Rinv ∘ R = id`. -/
theorem rotMap_rotMap_transpose {V : Matrix (Fin n) (Fin n) ℝ} (hV : Vᵀ * V = 1)
    (x : (Fin n → ℝ) × (Fin n → ℝ)) : rotMap V (rotMap Vᵀ x) = x := by
  rw [rotMap_rotMap, mul_transpose_eq_one hV, rotMap_one]

/-- `R ∘ Rinv = id`. -/
theorem rotMap_transpose_rotMap {V : Matrix (Fin n) (Fin n) ℝ} (hV : Vᵀ * V = 1)
    (y : (Fin n → ℝ) × (Fin n → ℝ)) : rotMap Vᵀ (rotMap V y) = y := by
  rw [rotMap_rotMap, hV, rotMap_one]

/-- An orthogonal matrix preserves the dot product. -/
theorem dotProduct_mulVec_mulVec {A : Matrix (Fin n) (Fin n) ℝ} (hA : Aᵀ * A = 1)
    (a b : Fin n → ℝ) : (A *ᵥ a) ⬝ᵥ (A *ᵥ b) = a ⬝ᵥ b := by
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec, hA, Matrix.vecMul_one]

theorem symplecticForm_eq_dotProduct (u v : (Fin n → ℝ) × (Fin n → ℝ)) :
    symplecticForm u v = u.2 ⬝ᵥ v.1 - u.1 ⬝ᵥ v.2 := by
  simp [symplecticForm, dotProduct, Finset.sum_sub_distrib]

/-- `rotMap A` is symplectic when `Aᵀ * A = 1`. -/
theorem symplecticForm_rotMap {A : Matrix (Fin n) (Fin n) ℝ} (hA : Aᵀ * A = 1)
    (u v : (Fin n → ℝ) × (Fin n → ℝ)) :
    symplecticForm (rotMap A u) (rotMap A v) = symplecticForm u v := by
  simp only [symplecticForm_eq_dotProduct, rotMap, dotProduct_mulVec_mulVec hA]

theorem transpose_mul_transpose_eq_one {V : Matrix (Fin n) (Fin n) ℝ} (hV : Vᵀ * V = 1) :
    Vᵀᵀ * Vᵀ = 1 := by
  rw [Matrix.transpose_transpose, mul_transpose_eq_one hV]

/-- **Target (A): rotation transport.** For orthogonal `V`, `R = rotMap Vᵀ`, `Rinv = rotMap V`, `G`
differentiable at `R x` and `H` differentiable at `x`:
`fderiv ℝ (G ∘ R) x (X_H x) = fderiv ℝ G (R x) (X_{H ∘ Rinv} (R x))`. -/
theorem fderiv_comp_rotMap_apply_hamiltonianVectorField {V : Matrix (Fin n) (Fin n) ℝ}
    (hV : Vᵀ * V = 1) {G H : (Fin n → ℝ) × (Fin n → ℝ) → ℝ} {x : (Fin n → ℝ) × (Fin n → ℝ)}
    (hG : DifferentiableAt ℝ G (rotMap Vᵀ x)) (hH : DifferentiableAt ℝ H x) :
    fderiv ℝ (G ∘ rotMap Vᵀ) x (hamiltonianVectorField H x) =
      fderiv ℝ G (rotMap Vᵀ x) (hamiltonianVectorField (H ∘ rotMap V) (rotMap Vᵀ x)) := by
  have hx : rotMap V (rotMap Vᵀ x) = x := rotMap_rotMap_transpose hV x
  have hGR : DifferentiableAt ℝ (G ∘ rotMap Vᵀ) (rotMap V (rotMap Vᵀ x)) := by
    rw [hx]
    exact hG.comp x (differentiable_rotMap _ x)
  have key := fderiv_apply_hamiltonianVectorField_comp_symplectic
    (Ψ := rotMap V) (G := G ∘ rotMap Vᵀ) (H := H) (y := rotMap Vᵀ x)
    (differentiable_rotMap V _)
    (fun u v => by rw [fderiv_rotMap]; exact symplecticForm_rotMap hV u v) hGR (by rwa [hx])
  rw [hx] at key
  rw [key]
  have hcomp : (G ∘ rotMap Vᵀ) ∘ rotMap V = G := by
    funext y
    simp [rotMap_transpose_rotMap hV]
  rw [hcomp]

/-- Regularity of `H ∘ rotMap A` at a point. -/
theorem contDiffAt_comp_rotMap (A : Matrix (Fin n) (Fin n) ℝ) {H : (Fin n → ℝ) × (Fin n → ℝ) → ℝ}
    {k : WithTop ℕ∞} {y : (Fin n → ℝ) × (Fin n → ℝ)} (hH : ContDiffAt ℝ k H (rotMap A y)) :
    ContDiffAt ℝ k (H ∘ rotMap A) y :=
  hH.comp y (contDiff_rotMap A).contDiffAt

/-- Regularity of `H ∘ rotMap A` on the preimage of a set. -/
theorem contDiffOn_comp_rotMap (A : Matrix (Fin n) (Fin n) ℝ) {H : (Fin n → ℝ) × (Fin n → ℝ) → ℝ}
    {k : WithTop ℕ∞} {S : Set ((Fin n → ℝ) × (Fin n → ℝ))} (hH : ContDiffOn ℝ k H S) :
    ContDiffOn ℝ k (H ∘ rotMap A) (rotMap A ⁻¹' S) :=
  hH.comp (contDiff_rotMap A).contDiffOn fun _ hy => hy

/-- Differentiability of `H ∘ rotMap A` at a point. -/
theorem differentiableAt_comp_rotMap (A : Matrix (Fin n) (Fin n) ℝ)
    {H : (Fin n → ℝ) × (Fin n → ℝ) → ℝ} {y : (Fin n → ℝ) × (Fin n → ℝ)}
    (hH : DifferentiableAt ℝ H (rotMap A y)) : DifferentiableAt ℝ (H ∘ rotMap A) y :=
  hH.comp y (differentiable_rotMap A y)

/-- For orthogonal `V`, the preimage under `Rinv = rotMap V` is the image under `R = rotMap Vᵀ`. -/
theorem rotMap_preimage_eq_image {V : Matrix (Fin n) (Fin n) ℝ} (hV : Vᵀ * V = 1)
    (S : Set ((Fin n → ℝ) × (Fin n → ℝ))) : rotMap V ⁻¹' S = rotMap Vᵀ '' S := by
  ext y
  constructor
  · intro hy
    exact ⟨rotMap V y, hy, rotMap_transpose_rotMap hV y⟩
  · rintro ⟨x, hx, rfl⟩
    simpa [Set.mem_preimage, rotMap_rotMap_transpose hV x] using hx

end KAM.EffectiveStability.Tube

end
