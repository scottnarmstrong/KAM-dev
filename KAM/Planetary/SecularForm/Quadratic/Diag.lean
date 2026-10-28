/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.SecularForm.Quadratic.Constants
public import KAM.Planetary.SecularSpectrum.Norms

/-!
# Quadratic part: the diagonalising rotation

Blueprint P, Part 8, `stepP:p8:qf-diag2` (package S8-Q). For `ϱ ∈ SO(n)` with
`Q_h = ϱ diag(σ) ϱᵀ`, the map `(ξ, η) ↦ (ϱᵀ ξ, ϱᵀ η)` is symplectic for the frozen form
`symplecticForm`, preserves `∑ (ξⱼ² + ηⱼ²)`, and with `Γ̃ⱼ = (ξ̃ⱼ² + η̃ⱼ²)/2` the quadratic part
`ξᵀ Q_h ξ + ηᵀ Q_h η` equals `∑ 2 σⱼ Γ̃ⱼ`. The three statements are separate lemmas
(`qfDiagSymplectic`, `qfDiagSumSq`, `qfDiagIdentity`), shaped for S9-Q's diagonalisation.
-/

@[expose] public noncomputable section
open scoped BigOperators Matrix.Norms.Elementwise
namespace KAM.Planetary
open KAM KAM.Planetary.SecularSpectrum

namespace SecularForm
variable {n : ℕ}

/-- `stepP:p8:qf-diag2`, symplecticity: the rotation `(ξ, η) ↦ (ϱᵀ ξ, ϱᵀ η)` preserves
`symplecticForm`. -/
theorem qfDiagSymplectic {ϱ : Mat n} (hϱ : isSO ϱ) (v w : Vec n × Vec n) :
    symplecticForm (ϱ.transpose.mulVec v.1, ϱ.transpose.mulVec v.2)
      (ϱ.transpose.mulVec w.1, ϱ.transpose.mulVec w.2) = symplecticForm v w := by
  have hm : ϱ * ϱ.transpose = 1 := mul_eq_one_comm.1 hϱ.1
  have key : ∀ x y : Vec n, (ϱ.transpose.mulVec x) ⬝ᵥ (ϱ.transpose.mulVec y) = x ⬝ᵥ y := by
    intro x y
    rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, Matrix.mulVec_mulVec, hm,
      Matrix.one_mulVec]
  have h1 := key v.2 w.1
  have h2 := key v.1 w.2
  simp only [symplecticForm]
  simp only [dotProduct] at h1 h2
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, h1, h2]

/-- `stepP:p8:qf-diag2`, sum of squares: `∑ (ξ̃ⱼ² + η̃ⱼ²) = ∑ (ξⱼ² + ηⱼ²)`. -/
theorem qfDiagSumSq {ϱ : Mat n} (hϱ : isSO ϱ) (ξ η : Vec n) :
    ∑ j, ((ϱ.transpose.mulVec ξ) j ^ 2 + (ϱ.transpose.mulVec η) j ^ 2) =
      ∑ j, (ξ j ^ 2 + η j ^ 2) := by
  have hm : ϱ * ϱ.transpose = 1 := mul_eq_one_comm.1 hϱ.1
  have key : ∀ x : Vec n, ∑ j, (ϱ.transpose.mulVec x) j ^ 2 = ∑ j, x j ^ 2 := by
    intro x
    have : (ϱ.transpose.mulVec x) ⬝ᵥ (ϱ.transpose.mulVec x) = x ⬝ᵥ x := by
      rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, Matrix.mulVec_mulVec, hm,
        Matrix.one_mulVec]
    simpa [dotProduct, sq] using this
  simp only [Finset.sum_add_distrib, key]

/-- `stepP:p8:qf-diag2`, the `2σΓ` identity: if `Q = ϱ diag(σ) ϱᵀ` then
`ξᵀ Q ξ + ηᵀ Q η = ∑ 2 σⱼ Γ̃ⱼ` with `Γ̃ⱼ = (ξ̃ⱼ² + η̃ⱼ²)/2`. -/
theorem qfDiagIdentity {ϱ : Mat n} (_hϱ : isSO ϱ) {σ : Vec n} {Q : Mat n}
    (hQ : Q = ϱ * Matrix.diagonal σ * ϱ.transpose) (ξ η : Vec n) :
    quad Q ξ + quad Q η =
      ∑ j, 2 * σ j * (((ϱ.transpose.mulVec ξ) j ^ 2 + (ϱ.transpose.mulVec η) j ^ 2) / 2) := by
  have hq : ∀ x : Vec n, quad Q x = ∑ j, σ j * (ϱ.transpose.mulVec x) j ^ 2 := by
    intro x
    have h : quad Q x = x ⬝ᵥ Q.mulVec x := by
      simp only [quad, dotProduct, Matrix.mulVec, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [h, hQ, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
      ← Matrix.mulVec_transpose]
    simp only [Matrix.mulVec_diagonal, dotProduct]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hq, hq, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

end SecularForm
end KAM.Planetary
end
