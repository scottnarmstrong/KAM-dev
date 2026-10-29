/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.SpinOrbit.Model
public import KAM.Frozen.Defs.HamiltonianVectorField
public import KAM.Frozen.Defs.HamiltonianVectorFieldC
public import KAM.Frozen.Defs.FrequencyMap
public import KAM.Frozen.Iso.Defs.BorderedHessian
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# The autonomous lunar Hamiltonian (track SO, package SO-MODEL)

Proposal §2.4, in exactly the conventions of track I's isoenergetic theorem (`IG1Body`):
phase space `(Fin 2 → ℂ) × (Fin 2 → ℂ)` with angles `θ = (q, φ)` first and actions `I = (p, J)`
second, and the Hamiltonian vector field `X_H = (∂_I H, -∂_θ H)` of the frozen
`KAM.hamiltonianVectorField` (real) and `KAM.hamiltonianVectorFieldℂ` (complex).

* `soHR`, `soHC`: `𝓗(q, φ, p, J) = J + p²/2 + V(q, φ)`, real and complex; `soHC_ofReal`.
* `fderiv_soHR_apply`, `fderiv_soHC_apply`: the full differential of `𝓗`.
* `soExtField`, `soExtFieldC`: the autonomous extension of the physical field `soField`:
  `(q̇, φ̇) = (p, 1)`, `(ṗ, J̇) = (-∂_q V, -∂_φ V)`.
* `hamiltonianVectorField_soHR`, `hamiltonianVectorFieldℂ_soHC`: `X_𝓗` equals it.
* `soBordered`, `det_soBordered`, `borderedHessian_soH0`, `det_borderedHessian_soH0`: the bordered
  matrix `((1,0,p),(0,0,1),(p,1,0))` has determinant `-1`, and it is the frozen
  `KAM.Iso.borderedHessian` of `h₀(p, J) = p²/2 + J` (index `Fin 2 ⊕ Unit`), whereas the
  Hessian block `((1,0),(0,0))` is singular.
-/

@[expose] public noncomputable section

open Real

namespace KAM.SpinOrbit

/-! ### A directional-derivative lemma -/

/-- For a function differentiable at `z`, the derivative along the line `t ↦ z + t v` at `t = 0` is
the differential applied to `v`. -/
theorem hasDerivAt_line {𝕜 E G : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    {f : E → G} {z : E} (hf : DifferentiableAt 𝕜 f z) (v : E) :
    HasDerivAt (fun t : 𝕜 => f (z + t • v)) (fderiv 𝕜 f z v) 0 := by
  have hl : HasDerivAt (fun t : 𝕜 => z + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : 𝕜)).smul_const v).const_add z
  exact hf.hasFDerivAt.comp_hasDerivAt_of_eq (0 : 𝕜) hl (by simp)

theorem fderiv_apply_eq_deriv_line {𝕜 E G : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    {f : E → G} {z : E} (hf : DifferentiableAt 𝕜 f z) (v : E) :
    fderiv 𝕜 f z v = deriv (fun t : 𝕜 => f (z + t • v)) 0 :=
  (hasDerivAt_line hf v).deriv.symm

/-! ### The Hamiltonians -/

/-- `𝓗(q, φ, p, J) = J + p²/2 + V(q, φ)` on `(θ, I) = ((q, φ), (p, J))`, real. -/
def soHR (z : (Fin 2 → ℝ) × (Fin 2 → ℝ)) : ℝ :=
  z.2 1 + z.2 0 ^ 2 / 2 + soV (z.1 0) (z.1 1)

/-- The same Hamiltonian on `(Fin 2 → ℂ) × (Fin 2 → ℂ)` (entire). -/
def soHC (z : (Fin 2 → ℂ) × (Fin 2 → ℂ)) : ℂ :=
  z.2 1 + z.2 0 ^ 2 / 2 + soVC (z.1 0) (z.1 1)

/-- The integrable part `h₀(p, J) = p²/2 + J`. -/
def soH0 (I : Fin 2 → ℂ) : ℂ := I 1 + I 0 ^ 2 / 2

theorem soHC_ofReal (z : (Fin 2 → ℝ) × (Fin 2 → ℝ)) :
    soHC ((fun i => (z.1 i : ℂ)), (fun i => (z.2 i : ℂ))) = (soHR z : ℝ) := by
  simp [soHC, soHR, soVC_ofReal]

theorem soHR_differentiable : Differentiable ℝ soHR := by
  unfold soHR soV; fun_prop

theorem soHC_differentiable : Differentiable ℂ soHC := by
  unfold soHC soVC; fun_prop

/-- The differential of `𝓗` (real): `d𝓗(v) = v_J + p v_p + ∂_qV v_q + ∂_φV v_φ`. -/
theorem fderiv_soHR_apply (z v : (Fin 2 → ℝ) × (Fin 2 → ℝ)) :
    fderiv ℝ soHR z v =
      v.2 1 + z.2 0 * v.2 0 + soVq (z.1 0) (z.1 1) * v.1 0 + soVφ (z.1 0) (z.1 1) * v.1 1 := by
  rw [fderiv_apply_eq_deriv_line (soHR_differentiable z)]
  have h1 : ∀ j : Fin 2, HasDerivAt (fun t : ℝ => (z + t • v).1 j) (v.1 j) 0 := fun j => by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (v.1 j)).const_add (z.1 j)
  have h2 : ∀ j : Fin 2, HasDerivAt (fun t : ℝ => (z + t • v).2 j) (v.2 j) 0 := fun j => by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (v.2 j)).const_add (z.2 j)
  have hV := hasDerivAt_soV_comp (h1 0) (h1 1)
  have hp := ((h2 0).pow 2).div_const 2
  have := ((h2 1).add hp).add hV
  simp only [soHR]
  refine this.deriv.trans ?_
  simp; ring

/-- The differential of `𝓗` (complex). -/
theorem fderiv_soHC_apply (z v : (Fin 2 → ℂ) × (Fin 2 → ℂ)) :
    fderiv ℂ soHC z v =
      v.2 1 + z.2 0 * v.2 0 + soVqC (z.1 0) (z.1 1) * v.1 0 + soVφC (z.1 0) (z.1 1) * v.1 1 := by
  rw [fderiv_apply_eq_deriv_line (soHC_differentiable z)]
  have h1 : ∀ j : Fin 2, HasDerivAt (fun t : ℂ => (z + t • v).1 j) (v.1 j) 0 := fun j => by
    simpa using ((hasDerivAt_id (0 : ℂ)).mul_const (v.1 j)).const_add (z.1 j)
  have h2 : ∀ j : Fin 2, HasDerivAt (fun t : ℂ => (z + t • v).2 j) (v.2 j) 0 := fun j => by
    simpa using ((hasDerivAt_id (0 : ℂ)).mul_const (v.2 j)).const_add (z.2 j)
  have hV := hasDerivAt_soVC_comp (h1 0) (h1 1)
  have hp := ((h2 0).pow 2).div_const 2
  have := ((h2 1).add hp).add hV
  simp only [soHC]
  refine this.deriv.trans ?_
  simp; ring

/-! ### The Hamiltonian vector field -/

/-- The autonomous extension of the physical field `soField` in `(θ, I)` order:
`(q̇, φ̇) = (p, 1)`, `(ṗ, J̇) = (-∂_q V, -∂_φ V)`; the `(q, p, φ)` components are `soField`. -/
def soExtField (z : (Fin 2 → ℝ) × (Fin 2 → ℝ)) : (Fin 2 → ℝ) × (Fin 2 → ℝ) :=
  (![(soField (z.1 0, z.2 0, z.1 1)).1, (soField (z.1 0, z.2 0, z.1 1)).2.2],
    ![(soField (z.1 0, z.2 0, z.1 1)).2.1, -soVφ (z.1 0) (z.1 1)])

/-- The complex counterpart of `soExtField`. -/
def soExtFieldC (z : (Fin 2 → ℂ) × (Fin 2 → ℂ)) : (Fin 2 → ℂ) × (Fin 2 → ℂ) :=
  (![z.2 0, 1], ![-soVqC (z.1 0) (z.1 1), -soVφC (z.1 0) (z.1 1)])

/-- The Hamiltonian vector field of `𝓗` (frozen convention `X_H = (∂_I H, -∂_θ H)`) is the
autonomous extension of the physical field. -/
theorem hamiltonianVectorField_soHR (z : (Fin 2 → ℝ) × (Fin 2 → ℝ)) :
    hamiltonianVectorField soHR z = soExtField z := by
  unfold hamiltonianVectorField soExtField
  simp only [soField_eq, fderiv_soHR_apply]
  refine Prod.ext ?_ ?_ <;> ext i <;> fin_cases i <;> simp

theorem hamiltonianVectorFieldℂ_soHC (z : (Fin 2 → ℂ) × (Fin 2 → ℂ)) :
    hamiltonianVectorFieldℂ soHC z = soExtFieldC z := by
  unfold hamiltonianVectorFieldℂ soExtFieldC
  simp only [fderiv_soHC_apply]
  refine Prod.ext ?_ ?_ <;> ext i <;> fin_cases i <;> simp

/-- The complex field is the complexification of the real one. -/
theorem soExtFieldC_ofReal (z : (Fin 2 → ℝ) × (Fin 2 → ℝ)) :
    soExtFieldC ((fun i => (z.1 i : ℂ)), (fun i => (z.2 i : ℂ))) =
      ((fun i => ((soExtField z).1 i : ℂ)), (fun i => ((soExtField z).2 i : ℂ))) := by
  unfold soExtFieldC soExtField
  simp only [soField_eq, soVqC_ofReal, soVφC_ofReal]
  refine Prod.ext ?_ ?_ <;> ext i <;> fin_cases i <;> simp

/-! ### The bordered matrix -/

/-- The bordered matrix `((1, 0, p), (0, 0, 1), (p, 1, 0))` of proposal §2.4 (Hessian block of
`h₀` in the `(p, J)` order, bordered by `∇h₀ = (p, 1)`). -/
def soBordered {R : Type*} [CommRing R] (p : R) : Matrix (Fin 3) (Fin 3) R :=
  !![1, 0, p; 0, 0, 1; p, 1, 0]

theorem det_soBordered {R : Type*} [CommRing R] (p : R) : (soBordered p).det = -1 := by
  simp [soBordered, Matrix.det_fin_three]

/-- The Hessian block `((1, 0), (0, 0))` of `h₀` is singular. -/
theorem det_soHessian0 {R : Type*} [CommRing R] : (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) R).det =
    0 := by
  simp [Matrix.det_fin_two]

/-- The index equivalence `Fin 3 ≃ Fin 2 ⊕ Unit` (the border is the last index). -/
def soBorderEquiv : Fin 3 ≃ Fin 2 ⊕ Unit where
  toFun i := if h : i.val < 2 then Sum.inl ⟨i.val, h⟩ else Sum.inr ()
  invFun := Sum.elim Fin.castSucc fun _ => 2
  left_inv := by decide
  right_inv := by decide

theorem fderiv_soH0Re_apply (I v : Fin 2 → ℝ) :
    fderiv ℝ (fun J : Fin 2 → ℝ => (soH0 fun j => (J j : ℂ)).re) I v = v 1 + I 0 * v 0 := by
  have hg : (fun J : Fin 2 → ℝ => (soH0 fun j => (J j : ℂ)).re) =
      fun J => J 1 + J 0 ^ 2 / 2 := by
    funext J; simp [soH0, ← Complex.ofReal_pow]
  rw [hg, fderiv_apply_eq_deriv_line (by fun_prop)]
  have h2 : ∀ j : Fin 2, HasDerivAt (fun t : ℝ => (I + t • v) j) (v j) 0 := fun j => by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (v j)).const_add (I j)
  have := (h2 1).add (((h2 0).pow 2).div_const 2)
  refine this.deriv.trans ?_
  simp; ring

theorem frequencyMap_soH0 (I : Fin 2 → ℝ) : frequencyMap soH0 I = ![I 0, 1] := by
  funext i
  unfold frequencyMap
  rw [fderiv_soH0Re_apply]
  fin_cases i <;> simp

theorem fderiv_frequencyMap_soH0 (I v : Fin 2 → ℝ) :
    fderiv ℝ (frequencyMap soH0) I v = ![v 0, 0] := by
  have hF : frequencyMap soH0 = fun J => ![J 0, 1] := funext frequencyMap_soH0
  rw [hF]
  have hdiff : DifferentiableAt ℝ (fun J : Fin 2 → ℝ => ![J 0, 1]) I := by
    refine differentiableAt_pi.2 fun i => ?_
    fin_cases i
    · simpa using differentiableAt_apply (0 : Fin 2) I
    · simp
  rw [fderiv_apply_eq_deriv_line hdiff]
  have : HasDerivAt (fun t : ℝ => (![(I + t • v) 0, 1] : Fin 2 → ℝ)) ![v 0, 0] 0 := by
    rw [hasDerivAt_pi]
    intro i
    fin_cases i
    · simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (v 0)).const_add (I 0)
    · simpa using hasDerivAt_const (0 : ℝ) (1 : ℝ)
  exact this.deriv

/-- The frozen bordered Hessian of `h₀(p, J) = p²/2 + J` is the matrix `soBordered p`
(indices `Fin 2 ⊕ Unit` versus `Fin 3`), `p = I 0`. -/
theorem borderedHessian_soH0 (I : Fin 2 → ℝ) :
    KAM.Iso.borderedHessian soH0 I =
      Matrix.reindex soBorderEquiv soBorderEquiv (soBordered (I 0)) := by
  ext i j
  rcases i with a | u <;> rcases j with b | w <;>
    simp only [KAM.Iso.borderedHessian, fderiv_frequencyMap_soH0, frequencyMap_soH0,
      Matrix.reindex_apply, Matrix.submatrix_apply]
  · fin_cases a <;> fin_cases b <;> simp [soBorderEquiv, soBordered]
  · fin_cases a <;> simp [soBorderEquiv, soBordered]
  · fin_cases b <;> simp [soBorderEquiv, soBordered]
  · simp [soBorderEquiv, soBordered]

/-- The determinant identity of proposal §2.4 for the frozen bordered Hessian: `det = -1`. -/
theorem det_borderedHessian_soH0 (I : Fin 2 → ℝ) : (KAM.Iso.borderedHessian soH0 I).det = -1 := by
  rw [borderedHessian_soH0, Matrix.det_reindex_self, det_soBordered]

end KAM.SpinOrbit

end
