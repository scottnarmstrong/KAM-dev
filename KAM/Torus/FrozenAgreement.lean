/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Torus.Objects
public import KAM.Matrix.Calculus
public import KAM.Matrix.Inverse
public import KAM.Strip.Bridges

/-!
# Agreement of the frozen definitions with the matrix objects

Blueprint Part 2, Lemma `bp:p2:frozen-agreement`. The frozen definitions `KAM.gramMatrix`,
`KAM.normalFrame`, `KAM.invarianceError`, `KAM.torsion` and `KAM.torsionAverage` are written with
pairs `ℂⁿ × ℂⁿ`, `dotℂ`, `omegaZero` and entrywise integrals. This file proves that they are the
matrix objects of `KAM/Torus/Objects.lean`:

* `KAM.Torus.gramMatrix_eq_tangentMat_transpose_mul`: `G = Lᵀ L`;
* `KAM.Torus.sumVec_normalFrame`: column `j` of `N` is `normalFrame K θ j`;
* `KAM.Torus.sumVec_invarianceError`: `E = X_h ∘ K - L ω`;
* `KAM.Torus.torsion_eq_mat`: `T = Nᵀ Ω₀ X_N`, given that `normalMat K` is differentiable at `θ`
  (`KAM.Torus.differentiableOn_normalMat` supplies this on an open strip where `K` is holomorphic
  and `det G` is a unit);
* `KAM.Torus.gramMatrix_mul_inv`, `KAM.Torus.inv_gramMatrix_mul`: `G G⁻¹ = G⁻¹ G = 1`;
* `KAM.Torus.torsionAverage_eq_avg`: `⟨T⟩ = avg T` when `T` is continuous on `ℝⁿ`;
* `KAM.Torus.frozen_agreement`: all of these, as the single node `bp:p2:frozen-agreement`.

The proofs work at the matrix level: the dictionary `sumVec` turns the dot product `dotℂ` into
`⬝ᵥ` and `omegaZero` into multiplication by `Ω₀`, and the derivative of a column of `N` is the
column of the derivative of the matrix-valued map `normalMat K` (`KAM.fderiv_matrix_apply`).
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator
open Matrix MeasureTheory Filter Topology

namespace KAM.Torus

variable {n : ℕ}

/-! ### The frozen objects, item by item -/

/-- Entries of `L = DK`: column `j` of `tangentMat K θ` is `sumVec (DK(θ) e_j)`. -/
theorem tangentMat_apply (K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)) (θ : Fin n → ℂ)
    (s : Fin n ⊕ Fin n) (j : Fin n) :
    tangentMat K θ s j = sumVec n (fderiv ℂ K θ (Pi.single j 1)) s := by
  have h := congrFun (colMat_mulVec (fderiv ℂ K θ) (Pi.single j 1)) s
  simpa [Matrix.mulVec_single_one, tangentMat] using h

/-- Blueprint `bp:p2:frozen-agreement` (item 1): the frozen Gram matrix is `G = Lᵀ L`. -/
theorem gramMatrix_eq_tangentMat_transpose_mul (K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ))
    (θ : Fin n → ℂ) : gramMatrix K θ = (tangentMat K θ)ᵀ * tangentMat K θ := by
  ext i j
  simp only [gramMatrix, dotℂ_eq_dotProduct_sumVec, Matrix.mul_apply, Matrix.transpose_apply,
    tangentMat_apply, dotProduct]

/-- The frozen `omegaZero` is multiplication by the matrix `Ω₀` on the `sumVec`-image. -/
theorem sumVec_omegaZero (u : (Fin n → ℂ) × (Fin n → ℂ)) :
    sumVec n (omegaZero u) = omegaZeroMatrix n *ᵥ sumVec n u := by
  obtain ⟨a, b⟩ := u
  rw [sumVec_apply, sumVec_apply, omegaZeroMatrix_mulVec_sumElim]
  rfl

/-- Blueprint `bp:p2:frozen-agreement` (item 2): column `j` of `N = Ω₀ L B` is the frozen
`normalFrame K θ j`. -/
theorem sumVec_normalFrame (K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)) (θ : Fin n → ℂ)
    (j : Fin n) : sumVec n (normalFrame K θ j) = fun s => normalMat K θ s j := by
  ext s
  simp only [normalFrame, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    sumVec_omegaZero, normalMat, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_comm]
  congr 1

/-- Blueprint `bp:p2:frozen-agreement` (item 3): the frozen invariance error is
`E = X_h ∘ K - L ω`. -/
theorem sumVec_invarianceError (h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ)
    (K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)) (ω : Fin n → ℝ) (θ : Fin n → ℂ) :
    sumVec n (invarianceError h K ω θ) =
      sumVec n (hamiltonianVectorFieldℂ h (K θ)) - tangentMat K θ *ᵥ (fun l => (ω l : ℂ)) := by
  rw [invarianceError, map_sub, tangentMat, colMat_mulVec]

/-! ### Holomorphy of `L`, `G`, `N` -/

/-- `L = DK` is holomorphic on an open strip where `K` is. -/
theorem differentiableOn_tangentMat {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {r : ℝ}
    (hK : DifferentiableOn ℂ K (complexStrip n r)) :
    DifferentiableOn ℂ (tangentMat K) (complexStrip n r) := by
  have hD := (holomorphic_regularity (isOpen_complexStrip n r) hK).1
  rw [differentiableOn_matrix_iff_entries]
  intro s j
  simp only [tangentMat_apply]
  have h1 : DifferentiableOn ℂ (fun θ => fderiv ℂ K θ (Pi.single j 1)) (complexStrip n r) :=
    hD.clm_apply (differentiableOn_const _)
  have h2 : DifferentiableOn ℂ (fun θ => sumVec n (fderiv ℂ K θ (Pi.single j 1)))
      (complexStrip n r) := (sumVecIso n).differentiable.comp_differentiableOn h1
  exact (differentiableOn_pi.1 h2) s

/-- The Gram matrix `G = Lᵀ L` is holomorphic on an open strip where `K` is. -/
theorem differentiableOn_gramMatrix {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {r : ℝ}
    (hK : DifferentiableOn ℂ K (complexStrip n r)) :
    DifferentiableOn ℂ (gramMatrix K) (complexStrip n r) := by
  have hL := differentiableOn_tangentMat hK
  have h : gramMatrix K = fun θ => (tangentMat K θ)ᵀ * tangentMat K θ :=
    funext (gramMatrix_eq_tangentMat_transpose_mul K)
  rw [h]
  exact hL.matrix_transpose.matrix_mul hL

/-- `N = Ω₀ L G⁻¹` is holomorphic on an open strip where `K` is holomorphic and `det G` is a
unit (`bp:p1:holomorphic-inverse` for `G⁻¹`). -/
theorem differentiableOn_normalMat {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {r : ℝ}
    (hK : DifferentiableOn ℂ K (complexStrip n r))
    (hG : ∀ θ ∈ complexStrip n r, IsUnit (gramMatrix K θ).det) :
    DifferentiableOn ℂ (normalMat K) (complexStrip n r) := by
  have hinv := (holomorphic_inverse (isOpen_complexStrip n r) (differentiableOn_gramMatrix hK)
    fun θ hθ => (hG θ hθ).ne_zero).1
  have hL := differentiableOn_tangentMat hK
  exact ((differentiableOn_const (omegaZeroMatrix n)).matrix_mul hL).matrix_mul hinv

/-! ### The torsion -/

/-- The derivative of a column of the frozen normal frame is the column of the derivative of
`normalMat K`. -/
theorem sumVec_fderiv_normalFrame {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}
    {θ : Fin n → ℂ} (hN : DifferentiableAt ℂ (normalMat K) θ) (j : Fin n) (v : Fin n → ℂ) :
    sumVec n (fderiv ℂ (fun θ' => normalFrame K θ' j) θ v) =
      fun s => fderiv ℂ (normalMat K) θ v s j := by
  rw [← fderiv_sumVec_apply]
  have h : (fun y => sumVec n (normalFrame K y j)) = fun y s => normalMat K y s j :=
    funext fun y => sumVec_normalFrame K y j
  rw [h, fderiv_pi (fun s => hN.matrix_apply s j)]
  ext s
  simp only [ContinuousLinearMap.pi_apply, fderiv_matrix_apply hN]

/-- Blueprint `bp:p2:frozen-agreement` (item 4, pointwise form): the frozen torsion is
`T = Nᵀ Ω₀ X_N` at every `θ` where `normalMat K` is differentiable. -/
theorem torsion_eq_mat (h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ)
    (K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)) (ω : Fin n → ℝ) {θ : Fin n → ℂ}
    (hN : DifferentiableAt ℂ (normalMat K) θ) :
    torsion h K ω θ = (normalMat K θ)ᵀ * omegaZeroMatrix n * normalFieldMat h K ω θ := by
  ext i j
  have hcol : sumVec n (fderiv ℂ (hamiltonianVectorFieldℂ h) (K θ) (normalFrame K θ j) -
      fderiv ℂ (fun θ' => normalFrame K θ' j) θ (fun l => (ω l : ℂ))) =
      fun s => normalFieldMat h K ω θ s j := by
    rw [map_sub, sumVec_fderiv_normalFrame hN]
    ext s
    have hA : sumVec n (fderiv ℂ (hamiltonianVectorFieldℂ h) (K θ) (normalFrame K θ j)) =
        linMat h K θ *ᵥ (fun s => normalMat K θ s j) := by
      rw [← sumVec_normalFrame, linMat, sqMat_mulVec]
    rw [Pi.sub_apply, hA, normalFieldMat, Matrix.sub_apply, Matrix.mul_apply]
    rfl
  simp only [torsion, dotℂ_eq_dotProduct_sumVec, sumVec_omegaZero, hcol, sumVec_normalFrame]
  rw [Matrix.mul_assoc, Matrix.mul_apply]
  simp only [dotProduct, Matrix.transpose_apply, Matrix.mulVec, Matrix.mul_apply]

/-! ### The inverse of the Gram matrix and the torsion average -/

/-- Blueprint `bp:p2:frozen-agreement` (item 5): `G G⁻¹ = 1` when `det G` is a unit. -/
theorem gramMatrix_mul_inv (K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)) {θ : Fin n → ℂ}
    (hG : IsUnit (gramMatrix K θ).det) : gramMatrix K θ * (gramMatrix K θ)⁻¹ = 1 :=
  Matrix.mul_nonsing_inv _ hG

/-- Blueprint `bp:p2:frozen-agreement` (item 5): `G⁻¹ G = 1` when `det G` is a unit. -/
theorem inv_gramMatrix_mul (K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)) {θ : Fin n → ℂ}
    (hG : IsUnit (gramMatrix K θ).det) : (gramMatrix K θ)⁻¹ * gramMatrix K θ = 1 :=
  Matrix.nonsing_inv_mul _ hG

/-- Blueprint `bp:p2:frozen-agreement` (item 6): the frozen `torsionAverage` is the average
`⟨T⟩ = avg T`, entrywise, as soon as `T` is continuous on `ℝⁿ` (`bp:p1:averages-matrix`). -/
theorem torsionAverage_eq_avg (h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ)
    (K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)) (ω : Fin n → ℝ)
    (hT : Continuous (fun x : Fin n → ℝ => torsion h K ω (fun i => (x i : ℂ)))) :
    torsionAverage h K ω = avg (torsion h K ω) :=
  Matrix.ext fun i j => (torusAverage_matrix_apply hT i j).symm

/-! ### The node -/

/-- Blueprint `bp:p2:frozen-agreement`. On an open strip where `K` is holomorphic with invertible
Gram matrix: the frozen `gramMatrix`, `normalFrame`, `invarianceError`, `torsion` are `LᵀL`, the
columns of `N`, `X_h ∘ K - Lω`, `Nᵀ Ω₀ X_N`; the frozen inverse is the inverse; and the frozen
`torsionAverage` is `⟨T⟩` whenever `T` is continuous on `ℝⁿ`. -/
theorem frozen_agreement (h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ)
    (K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)) (ω : Fin n → ℝ) {r : ℝ} (hr : 0 < r)
    (hK : DifferentiableOn ℂ K (complexStrip n r))
    (hG : ∀ θ ∈ complexStrip n r, IsUnit (gramMatrix K θ).det) :
    (∀ θ, gramMatrix K θ = (tangentMat K θ)ᵀ * tangentMat K θ) ∧
    (∀ θ j, sumVec n (normalFrame K θ j) = fun s => normalMat K θ s j) ∧
    (∀ θ, sumVec n (invarianceError h K ω θ) =
      sumVec n (hamiltonianVectorFieldℂ h (K θ)) - tangentMat K θ *ᵥ (fun l => (ω l : ℂ))) ∧
    (∀ θ ∈ complexStrip n r,
      torsion h K ω θ = (normalMat K θ)ᵀ * omegaZeroMatrix n * normalFieldMat h K ω θ) ∧
    (∀ θ ∈ complexStrip n r,
      gramMatrix K θ * (gramMatrix K θ)⁻¹ = 1 ∧ (gramMatrix K θ)⁻¹ * gramMatrix K θ = 1) ∧
    (Continuous (fun x : Fin n → ℝ => torsion h K ω (fun i => (x i : ℂ))) →
      torsionAverage h K ω = avg (torsion h K ω)) := by
  -- `0 < r` is the strip-width convention; no item needs it.
  have _hr : 0 < r := hr
  exact ⟨gramMatrix_eq_tangentMat_transpose_mul K, sumVec_normalFrame K,
    sumVec_invarianceError h K ω,
    fun θ hθ => torsion_eq_mat h K ω
      ((differentiableOn_normalMat hK hG).differentiableAt
        ((isOpen_complexStrip n r).mem_nhds hθ)),
    fun θ hθ => ⟨gramMatrix_mul_inv K (hG θ hθ), inv_gramMatrix_mul K (hG θ hθ)⟩,
    torsionAverage_eq_avg h K ω⟩

end KAM.Torus

end
