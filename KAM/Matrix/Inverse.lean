/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Data.Matrix.Basis
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Real and holomorphic matrix inverses

Blueprint Part 1, "Matrices" and "Holomorphic maps on open sets".

* `KAM.real_inverse` (`bp:p1:real-inverse`): the inverse of an invertible real matrix is real, and
  so is the inverse `A(θ)⁻¹` of an invertible matrix `A(θ)` that is real at every real `θ`.
  The proof is Cramer's rule (`Matrix.inv_def`): `A⁻¹ = (det A)⁻¹ adj A` and `det`, `adj` are
  polynomials with integer coefficients in the entries (`RingHom.map_det`,
  `RingHom.map_adjugate`). A complex matrix is *real* when it is `B.map Complex.ofReal` for a real
  matrix `B`, mirroring the frozen `KAM.IsRealOnReals`.
* `KAM.holomorphic_inverse` (`bp:p1:holomorphic-inverse`): if `A` is holomorphic on an open set
  with `det A ≠ 0` there, then `A⁻¹` is holomorphic and `D(A⁻¹) = -A⁻¹ (DA) A⁻¹`. Holomorphy of a
  matrix-valued function is `DifferentiableOn ℂ` for the matrix operator norm of
  `open scoped Matrix.Norms.Operator`, the one used by `KAM/Matrix/Neumann.lean`;
  `KAM.differentiableOn_matrix_iff_entries` says this is holomorphy of every entry. The inverse
  lemmas work for any finite matrix index type, including the sum indices of symplectic frames.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator

namespace KAM

/-! ### Real inverses (`bp:p1:real-inverse`) -/

section Real

variable {n : ℕ}

/-- The determinant of a real matrix viewed over `ℂ` is the real determinant. -/
theorem det_map_ofReal (B : Matrix (Fin n) (Fin n) ℝ) :
    (B.map Complex.ofReal).det = (B.det : ℂ) := by
  have h := RingHom.map_det Complex.ofRealHom B
  rw [RingHom.mapMatrix_apply] at h
  exact h.symm

/-- The adjugate of a real matrix viewed over `ℂ` is the real adjugate. -/
theorem adjugate_map_ofReal (B : Matrix (Fin n) (Fin n) ℝ) :
    (B.map Complex.ofReal).adjugate = B.adjugate.map Complex.ofReal := by
  have h := RingHom.map_adjugate Complex.ofRealHom B
  rw [RingHom.mapMatrix_apply, RingHom.mapMatrix_apply] at h
  exact h.symm

/-- Blueprint `step:p1:ri-adjugate`. For a real invertible matrix, `det A ≠ 0`, `det A` and
`adj A` are real, and `A⁻¹ = (det A)⁻¹ adj A` is real. -/
theorem real_inverse_adjugate {A : Matrix (Fin n) (Fin n) ℂ}
    (hreal : ∃ B : Matrix (Fin n) (Fin n) ℝ, A = B.map Complex.ofReal) (hA : IsUnit A) :
    A.det ≠ 0 ∧ (∃ r : ℝ, A.det = r) ∧
      (∃ C : Matrix (Fin n) (Fin n) ℝ, A.adjugate = C.map Complex.ofReal) ∧
      A⁻¹ = A.det⁻¹ • A.adjugate ∧
      ∃ B' : Matrix (Fin n) (Fin n) ℝ, A⁻¹ = B'.map Complex.ofReal := by
  obtain ⟨B, rfl⟩ := hreal
  have hdet : (B.map Complex.ofReal).det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).1 hA).ne_zero
  have hinv : (B.map Complex.ofReal)⁻¹ = (B.map Complex.ofReal).det⁻¹ •
      (B.map Complex.ofReal).adjugate := by
    rw [Matrix.inv_def, Ring.inverse_eq_inv']
  refine ⟨hdet, ⟨B.det, det_map_ofReal B⟩, ⟨B.adjugate, adjugate_map_ofReal B⟩, hinv,
    B.det⁻¹ • B.adjugate, ?_⟩
  rw [hinv, det_map_ofReal, adjugate_map_ofReal]
  ext i j
  simp

/-- Blueprint `bp:p1:real-inverse`. The inverse of an invertible real matrix is real; hence if
`A(θ)` is real for real `θ` and invertible, so is `A(θ)⁻¹`. Here `θ : Fin m → ℝ` is embedded in
`Fin m → ℂ` coordinatewise, as in the frozen `KAM.IsRealOnReals`. -/
theorem real_inverse :
    (∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ),
      (∃ B : Matrix (Fin n) (Fin n) ℝ, A = B.map Complex.ofReal) → IsUnit A →
        ∃ B' : Matrix (Fin n) (Fin n) ℝ, A⁻¹ = B'.map Complex.ofReal) ∧
    (∀ (m n : ℕ) (A : (Fin m → ℂ) → Matrix (Fin n) (Fin n) ℂ),
      (∀ θ : Fin m → ℝ, (∃ B : Matrix (Fin n) (Fin n) ℝ,
          A (fun i => (θ i : ℂ)) = B.map Complex.ofReal) ∧ IsUnit (A fun i => (θ i : ℂ))) →
        ∀ θ : Fin m → ℝ, ∃ B' : Matrix (Fin n) (Fin n) ℝ,
          (A fun i => (θ i : ℂ))⁻¹ = B'.map Complex.ofReal) :=
  ⟨fun _ _ hreal hA => (real_inverse_adjugate hreal hA).2.2.2.2,
    fun _ _ _ h θ => (real_inverse_adjugate (h θ).1 (h θ).2).2.2.2.2⟩

end Real

/-! ### Holomorphic inverses (`bp:p1:holomorphic-inverse`) -/

section Holomorphic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {V : Set E}

/-- A matrix-valued function is holomorphic (for the matrix operator norm) exactly when every
entry is. -/
theorem differentiableOn_matrix_iff_entries {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] {f : E → Matrix ι κ ℂ} :
    DifferentiableOn ℂ f V ↔ ∀ i j, DifferentiableOn ℂ (fun z => f z i j) V := by
  constructor
  · intro hf i j
    exact (LinearMap.toContinuousLinearMap
      (Matrix.entryLinearMap ℂ ℂ i j)).differentiable.comp_differentiableOn hf
  · intro hf
    have : f = fun z => ∑ i, ∑ j, f z i j • Matrix.single i j (1 : ℂ) := by
      funext z
      conv_lhs => rw [Matrix.matrix_eq_sum_single (f z)]
      simp [Matrix.smul_single]
    rw [this]
    exact DifferentiableOn.fun_sum fun i _ =>
      DifferentiableOn.fun_sum fun j _ => (hf i j).smul_const _

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {A : E → Matrix ι ι ℂ}

/-- Blueprint `step:p1:hi-holomorphic`. If `A` is holomorphic and `det A ≠ 0` on `V`, then
`A⁻¹ = (det A)⁻¹ adj A` is holomorphic on `V`. (Openness of `V` is not needed here.) -/
theorem holomorphic_inverse_differentiableOn (hA : DifferentiableOn ℂ A V)
    (hdet : ∀ z ∈ V, (A z).det ≠ 0) :
    (∀ z ∈ V, (A z)⁻¹ = (A z).det⁻¹ • (A z).adjugate) ∧
      DifferentiableOn ℂ (fun z => (A z)⁻¹) V := by
  refine ⟨fun z _ => by rw [Matrix.inv_def, Ring.inverse_eq_inv'], fun z hz => ?_⟩
  have hunit : IsUnit (A z) := (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 (hdet z hz))
  simp only [Matrix.nonsing_inv_eq_ringInverse]
  exact (hA z hz).inverse hunit

/-- Blueprint `step:p1:hi-derivative`. In every direction `v`,
`D(A⁻¹)(z) v = -A(z)⁻¹ (DA(z) v) A(z)⁻¹`. -/
theorem fderiv_matrix_inv_apply (hV : IsOpen V) (hA : DifferentiableOn ℂ A V)
    (hdet : ∀ z ∈ V, (A z).det ≠ 0) {z : E} (hz : z ∈ V) (v : E) :
    fderiv ℂ (fun w => (A w)⁻¹) z v = -((A z)⁻¹ * fderiv ℂ A z v * (A z)⁻¹) := by
  have hunit : IsUnit (A z) := (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 (hdet z hz))
  obtain ⟨u, hu⟩ := hunit
  have hAz : HasFDerivAt A (fderiv ℂ A z) z := (hA.differentiableAt (hV.mem_nhds hz)).hasFDerivAt
  have hinv : (A z)⁻¹ = ((u⁻¹ : (Matrix ι ι ℂ)ˣ) : Matrix ι ι ℂ) := by
    rw [Matrix.nonsing_inv_eq_ringInverse, ← hu, Ring.inverse_unit]
  have hg : HasFDerivAt Ring.inverse
      (-ContinuousLinearMap.mulLeftRight ℂ (Matrix ι ι ℂ) ↑u⁻¹ ↑u⁻¹) (A z) := by
    rw [← hu]
    exact hasFDerivAt_ringInverse (𝕜 := ℂ) u
  have hcomp := hg.comp z hAz
  have hfun : (fun w => (A w)⁻¹) = Ring.inverse ∘ A := by
    funext w
    exact Matrix.nonsing_inv_eq_ringInverse (A w)
  rw [hfun]
  refine (congrArg (fun L => L v) hcomp.fderiv).trans ?_
  rw [hinv]
  rfl

/-- Blueprint `bp:p1:holomorphic-inverse`. If `A` is holomorphic on an open set `V` with
`det A ≠ 0` there, then `A⁻¹` is holomorphic on `V` and `D(A⁻¹) = -A⁻¹ (DA) A⁻¹`, that is,
`D(A⁻¹)(z) v = -A(z)⁻¹ (DA(z) v) A(z)⁻¹` for all `z ∈ V` and directions `v`. -/
theorem holomorphic_inverse (hV : IsOpen V) (hA : DifferentiableOn ℂ A V)
    (hdet : ∀ z ∈ V, (A z).det ≠ 0) :
    DifferentiableOn ℂ (fun z => (A z)⁻¹) V ∧
      ∀ z ∈ V, ∀ v : E,
        fderiv ℂ (fun w => (A w)⁻¹) z v = -((A z)⁻¹ * fderiv ℂ A z v * (A z)⁻¹) :=
  ⟨(holomorphic_inverse_differentiableOn hA hdet).2,
    fun _ hz v => fderiv_matrix_inv_apply hV hA hdet hz v⟩

end Holomorphic

end KAM

end
