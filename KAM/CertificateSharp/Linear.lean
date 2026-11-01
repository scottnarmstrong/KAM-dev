/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Frozen.Defs.InvarianceError
public import Mathlib.Analysis.Calculus.FDeriv.Equiv

/-!
# Linear symplectic changes of variables

A linear change of variables `L` of the phase space `ℂⁿ × ℂⁿ` that preserves the symplectic
pairing `ω(u, v) = Σ_i (u_Q,i v_P,i - u_P,i v_Q,i)` (`IsSymplectic`) and a linear change `A` of
the angles transform Hamiltonian data covariantly:

* `symplecticPairing_hamiltonianVectorFieldℂ`: `ω(X_H(z), w) = DH(z) w`, and
  `eq_of_symplecticPairing`: the pairing is nondegenerate;
* `hamiltonianVectorFieldℂ_comp`: `X_{H ∘ L} = L⁻¹ X_H ∘ L`;
* `invarianceError_comp`: `E(H ∘ L, L⁻¹ ∘ K ∘ A⁻¹, A ω)(θ) = L⁻¹ E(H, K, ω)(A⁻¹ θ)` for the
  invariance error `E(H, K, ω)(θ) = X_H(K θ) - DK(θ) ω`;
* `invarianceError_comp_symm`: the same identity read backwards,
  `E(H, L ∘ K' ∘ A, ω)(θ) = L E(H ∘ L, K', A ω)(A θ)` (transport to the original variables).

Every identity is unconditional: `fderiv` composes with continuous linear equivalences without a
differentiability premise (`ContinuousLinearEquiv.comp_fderiv`, `comp_right_fderiv`).
-/

@[expose] public noncomputable section

namespace KAM.CertificateSharp.Linear

open KAM

variable {n : ℕ}

/-- The symplectic pairing `ω(u, v) = Σ_i (u_Q,i v_P,i - u_P,i v_Q,i)` of `ℂⁿ × ℂⁿ`. -/
def symplecticPairing (u v : (Fin n → ℂ) × (Fin n → ℂ)) : ℂ :=
  ∑ i, (u.1 i * v.2 i - u.2 i * v.1 i)

/-- A map of `ℂⁿ × ℂⁿ` preserves the symplectic pairing. -/
def IsSymplectic (L : (Fin n → ℂ) × (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)) : Prop :=
  ∀ u v, symplecticPairing (L u) (L v) = symplecticPairing u v

/-- The pairing with the Hamiltonian vector field is the derivative: `ω(X_H(z), w) = DH(z) w`. -/
theorem symplecticPairing_hamiltonianVectorFieldℂ (H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ)
    (z w : (Fin n → ℂ) × (Fin n → ℂ)) :
    symplecticPairing (hamiltonianVectorFieldℂ H z) w = fderiv ℂ H z w := by
  have hw : w = ∑ i, (w.1 i • ((Pi.single i 1 : Fin n → ℂ), (0 : Fin n → ℂ)) +
      w.2 i • ((0 : Fin n → ℂ), (Pi.single i 1 : Fin n → ℂ))) := by
    refine Prod.ext (funext fun j => ?_) (funext fun j => ?_) <;>
      simp [Prod.fst_sum, Prod.snd_sum, Finset.sum_apply, Pi.single_apply]
  conv_rhs => rw [hw]
  simp only [map_sum, map_add, map_smul, smul_eq_mul, symplecticPairing,
    hamiltonianVectorFieldℂ]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- The symplectic pairing is nondegenerate. -/
theorem eq_of_symplecticPairing {u v : (Fin n → ℂ) × (Fin n → ℂ)}
    (h : ∀ w, symplecticPairing u w = symplecticPairing v w) : u = v := by
  refine Prod.ext (funext fun j => ?_) (funext fun j => ?_)
  · simpa [symplecticPairing, Pi.single_apply] using h ((0 : Fin n → ℂ), Pi.single j 1)
  · simpa [symplecticPairing, Pi.single_apply] using h (Pi.single j 1, (0 : Fin n → ℂ))

variable {L : ((Fin n → ℂ) × (Fin n → ℂ)) ≃L[ℂ] ((Fin n → ℂ) × (Fin n → ℂ))}

/-- The inverse of a symplectic linear equivalence is symplectic. -/
theorem IsSymplectic.symm (hL : IsSymplectic (n := n) L) : IsSymplectic L.symm := by
  intro u v
  rw [← hL, L.apply_symm_apply, L.apply_symm_apply]

/-- **Covariance of the Hamiltonian vector field**: `X_{H ∘ L}(z) = L⁻¹ X_H(L z)` for a symplectic
linear equivalence `L` (no differentiability premise). -/
theorem hamiltonianVectorFieldℂ_comp (hL : IsSymplectic (n := n) L)
    (H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) (z : (Fin n → ℂ) × (Fin n → ℂ)) :
    hamiltonianVectorFieldℂ (H ∘ L) z = L.symm (hamiltonianVectorFieldℂ H (L z)) := by
  apply L.injective
  rw [L.apply_symm_apply]
  refine eq_of_symplecticPairing fun w => ?_
  rw [← L.apply_symm_apply w, hL, symplecticPairing_hamiltonianVectorFieldℂ,
    symplecticPairing_hamiltonianVectorFieldℂ, L.comp_right_fderiv]
  rfl

/-- **The invariance error under a linear symplectic change of variables**: with `L` symplectic,
`A` a linear change of the angles and `ω' = A ω`,
`E(H ∘ L, L⁻¹ ∘ K ∘ A⁻¹, ω')(θ) = L⁻¹ E(H, K, ω)(A⁻¹ θ)`. -/
theorem invarianceError_comp (hL : IsSymplectic (n := n) L)
    (A : (Fin n → ℂ) ≃L[ℂ] (Fin n → ℂ)) (H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ)
    (K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)) {ω ω' : Fin n → ℝ}
    (hω : (fun i => (ω' i : ℂ)) = A fun i => (ω i : ℂ)) (θ : Fin n → ℂ) :
    invarianceError (H ∘ L) (L.symm ∘ K ∘ A.symm) ω' θ =
      L.symm (invarianceError H K ω (A.symm θ)) := by
  unfold invarianceError
  have hK : L.symm ∘ K ∘ A.symm = L.symm ∘ (K ∘ A.symm) := rfl
  rw [hamiltonianVectorFieldℂ_comp hL, hK, L.symm.comp_fderiv, A.symm.comp_right_fderiv, hω]
  simp

/-- **The invariance error read backwards** (transport to the original variables):
`E(H, L ∘ K' ∘ A, ω)(θ) = L E(H ∘ L, K', ω')(A θ)` for `ω' = A ω`. -/
theorem invarianceError_comp_symm (hL : IsSymplectic (n := n) L)
    (A : (Fin n → ℂ) ≃L[ℂ] (Fin n → ℂ)) (H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ)
    (K' : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)) {ω ω' : Fin n → ℝ}
    (hω : (fun i => (ω' i : ℂ)) = A fun i => (ω i : ℂ)) (θ : Fin n → ℂ) :
    invarianceError H (L ∘ K' ∘ A) ω θ = L (invarianceError (H ∘ L) K' ω' (A θ)) := by
  have hω' : (fun i => (ω i : ℂ)) = A.symm fun i => (ω' i : ℂ) := by
    rw [hω, A.symm_apply_apply]
  have h := invarianceError_comp hL.symm A.symm (H ∘ L) K' hω' θ
  have hH : (H ∘ L) ∘ L.symm = H := by
    funext z; simp
  rw [hH, L.symm_symm, A.symm_symm] at h
  exact h

end KAM.CertificateSharp.Linear

end
