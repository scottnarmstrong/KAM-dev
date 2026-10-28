/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.SecularSpectrum.Norms

/-!
# Weyl's inequality for the sorted spectrum

Blueprint P, Part 10 (`bpP:p10:weyl`, `stepP:p10:weyl-mm`, `stepP:p10:weyl-pert`): the sorted
eigenvalues of Hermitian matrices move by at most the Euclidean operator norm of the perturbation.

The min-max step is a direct subspace-counting argument (`sorted_le_of_quad_le`): `n - 1` linear
conditions on `Fin n → ℝ` have a nonzero solution, which lies in the top eigenspace span of one
matrix and the bottom eigenspace span of the other.  Everything is stated with explicit
Euclidean quantities on `Fin n → ℝ`; `EuclideanSpace` appears only inside the proof of
`exists_eigenframe`, to reuse Mathlib's spectral theorem.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter Real Function
open scoped BigOperators Topology Matrix.Norms.Elementwise
namespace KAM.Planetary
open KAM KAM.Kepler

namespace SecularSpectrum
open SecularForm
variable {n : ℕ}

/-- Orthonormal eigenframe indexed by the sorted index: Parseval and the diagonal quadratic form. -/
lemma exists_eigenframe (M : Mat n) (hM : M.IsHermitian) :
    ∃ v : Fin n → Vec n, ∀ x : Vec n,
      (∑ j, (v j ⬝ᵥ x) ^ 2 = x ⬝ᵥ x) ∧
      (x ⬝ᵥ M.mulVec x = ∑ j, sorted M hM j * (v j ⬝ᵥ x) ^ 2) := by
  let b := hM.eigenvectorBasis
  let e : Fin (Fintype.card (Fin n)) ≃ Fin n := Fintype.equivOfCardEq (Fintype.card_fin _)
  let τ : Fin n ≃ Fin n :=
    Fin.revPerm.trans ((finCongr (Fintype.card_fin n).symm).trans e)
  have hτ : ∀ i, sorted M hM i = hM.eigenvalues (τ i) := by
    intro i
    simp [sorted, Matrix.IsHermitian.eigenvalues, τ, e]
  refine ⟨fun j => ⇑(b (τ j)), fun x => ?_⟩
  let x' : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 x
  have hin : ∀ k, (⇑(b k) ⬝ᵥ x) = inner ℝ (b k) x' := by
    intro k
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp [x', dotProduct_comm]
  constructor
  · have := b.sum_sq_norm_inner_right x'
    simp only [hin, Real.norm_eq_abs, sq_abs] at this ⊢
    rw [Equiv.sum_comp τ (fun k => (inner ℝ (b k) x') ^ 2), this]
    simp [x', EuclideanSpace.norm_eq, dotProduct, sq,
      Real.sq_sqrt (Finset.sum_nonneg fun i _ => mul_self_nonneg (x i))]
  · have hsym : M.transpose = M := by simpa using hM.eq
    have key : ∀ k, ⇑(b k) ⬝ᵥ M.mulVec x = hM.eigenvalues k * (b k ⬝ᵥ x) := by
      intro k
      rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hsym,
        hM.mulVec_eigenvectorBasis k, smul_dotProduct, smul_eq_mul]
    have := b.sum_inner_mul_inner x' (WithLp.toLp 2 (M.mulVec x))
    have hxy : ∀ k, inner ℝ x' (b k) = (⇑(b k) ⬝ᵥ x) := fun k => by
      rw [real_inner_comm, hin]
    have hy : ∀ k, inner ℝ (b k) (WithLp.toLp 2 (M.mulVec x) : EuclideanSpace ℝ (Fin n)) =
        hM.eigenvalues k * (b k ⬝ᵥ x) := fun k => by
      rw [← key, EuclideanSpace.inner_eq_star_dotProduct]
      simp [dotProduct_comm]
    simp only [hxy, hy] at this
    have h2 : inner ℝ x' (WithLp.toLp 2 (M.mulVec x) : EuclideanSpace ℝ (Fin n)) =
        x ⬝ᵥ M.mulVec x := by
      rw [EuclideanSpace.inner_eq_star_dotProduct]
      simp [x', dotProduct_comm]
    rw [h2] at this
    rw [← this, ← Equiv.sum_comp τ]
    exact Finset.sum_congr rfl fun j _ => by rw [hτ]; ring

end SecularSpectrum
end KAM.Planetary
end
