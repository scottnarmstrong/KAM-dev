/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.Transfer

/-!
# Brackets in coordinates and their transport by symplectic maps (T2-CONF, N2-Chart)

The tube checker of program T2-CONF bounds the rates `fderiv ℝ G x (X_H x)` of observables `G` along
the Hamiltonian vector field `X_H = (∂H/∂p, -∂H/∂q)` (`KAM.hamiltonianVectorField`, `x = (q, p)`).
This file fixes the coordinate formula of such a rate and its transport through a symplectic map.

* `clm_prod_apply_eq_sum`: a real linear functional on `(Fin m → ℝ) × (Fin k → ℝ)` in coordinates.
* `bracketSum G H y = Σ_j (∂_{y.1 j} G · ∂_{y.2 j} H - ∂_{y.2 j} G · ∂_{y.1 j} H)`, positions first.
* `fderiv_apply_hamiltonianVectorField_eq_bracketSum`: `fderiv ℝ G y (X_H y) = bracketSum G H y`
  (no hypothesis: this pins the sign).
* `fderiv_apply_hamiltonianVectorField_comp_symplectic`: for `Ψ` differentiable at `y` with
  symplectic derivative, `fderiv ℝ G (Ψ y) (X_H (Ψ y)) = fderiv ℝ (G ∘ Ψ) y (X_{H ∘ Ψ} y)`.
* `fderiv_apply_hamiltonianVectorField_congr`: the rate depends only on the germs of `G` and `H`.
-/

@[expose] public noncomputable section

namespace KAM.EffectiveStability.Tube

open KAM Filter Topology

/-- A real linear functional on `(Fin m → ℝ) × (Fin k → ℝ)` in coordinates. -/
theorem clm_prod_apply_eq_sum {m k : ℕ} (ℓ : (Fin m → ℝ) × (Fin k → ℝ) →L[ℝ] ℝ)
    (a : Fin m → ℝ) (b : Fin k → ℝ) :
    ℓ (a, b) = ∑ i, a i * ℓ (Pi.single i 1, 0) + ∑ i, b i * ℓ (0, Pi.single i 1) := by
  have ha : ((a, b) : (Fin m → ℝ) × (Fin k → ℝ)) =
      ∑ i, a i • ((Pi.single i 1 : Fin m → ℝ), (0 : Fin k → ℝ)) +
        ∑ i, b i • ((0 : Fin m → ℝ), (Pi.single i 1 : Fin k → ℝ)) := by
    ext j
    · simp [Prod.fst_sum, Finset.sum_apply, Pi.single_apply]
    · simp [Prod.snd_sum, Finset.sum_apply, Pi.single_apply]
  rw [ha, map_add, map_sum, map_sum]
  simp only [map_smul, smul_eq_mul]

variable {n : ℕ}

/-- The coordinate bracket `Σ_j (∂_{y.1 j} G · ∂_{y.2 j} H - ∂_{y.2 j} G · ∂_{y.1 j} H)`, with the
first factor `y.1` as positions and the second `y.2` as momenta. -/
def bracketSum (G H : (Fin n → ℝ) × (Fin n → ℝ) → ℝ) (y : (Fin n → ℝ) × (Fin n → ℝ)) : ℝ :=
  ∑ j, (fderiv ℝ G y (Pi.single j 1, 0) * fderiv ℝ H y (0, Pi.single j 1) -
    fderiv ℝ G y (0, Pi.single j 1) * fderiv ℝ H y (Pi.single j 1, 0))

/-- **The sign.** The rate of `G` along `X_H` is the coordinate bracket `bracketSum G H`. -/
theorem fderiv_apply_hamiltonianVectorField_eq_bracketSum (G H : (Fin n → ℝ) × (Fin n → ℝ) → ℝ)
    (y : (Fin n → ℝ) × (Fin n → ℝ)) :
    fderiv ℝ G y (hamiltonianVectorField H y) = bracketSum G H y := by
  rw [hamiltonianVectorField, clm_prod_apply_eq_sum, bracketSum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- **Symplectic transport of rates.** If `Ψ` is differentiable at `y` with a symplectic derivative
and `G`, `H` are differentiable at `Ψ y`, then the rate of `G` along `X_H` at `Ψ y` is the rate of
`G ∘ Ψ` along `X_{H ∘ Ψ}` at `y`. -/
theorem fderiv_apply_hamiltonianVectorField_comp_symplectic
    {Ψ : (Fin n → ℝ) × (Fin n → ℝ) → (Fin n → ℝ) × (Fin n → ℝ)}
    {G H : (Fin n → ℝ) × (Fin n → ℝ) → ℝ} {y : (Fin n → ℝ) × (Fin n → ℝ)}
    (hΨ : DifferentiableAt ℝ Ψ y)
    (hsymp : ∀ u v, symplecticForm (fderiv ℝ Ψ y u) (fderiv ℝ Ψ y v) = symplecticForm u v)
    (hG : DifferentiableAt ℝ G (Ψ y)) (hH : DifferentiableAt ℝ H (Ψ y)) :
    fderiv ℝ G (Ψ y) (hamiltonianVectorField H (Ψ y)) =
      fderiv ℝ (G ∘ Ψ) y (hamiltonianVectorField (H ∘ Ψ) y) := by
  rw [fderiv_comp y hG hΨ, ContinuousLinearMap.comp_apply,
    fderiv_chart_apply_hamiltonianVectorField hH hΨ hsymp]

/-- The rate of `G` along `X_H` at `y` depends only on the germs of `G` and `H` at `y`. -/
theorem fderiv_apply_hamiltonianVectorField_congr {G G' H H' : (Fin n → ℝ) × (Fin n → ℝ) → ℝ}
    {y : (Fin n → ℝ) × (Fin n → ℝ)} (hG : G =ᶠ[𝓝 y] G') (hH : H =ᶠ[𝓝 y] H') :
    fderiv ℝ G y (hamiltonianVectorField H y) = fderiv ℝ G' y (hamiltonianVectorField H' y) := by
  simp only [hamiltonianVectorField, hG.fderiv_eq, hH.fderiv_eq]

/-- Pointwise agreement on an open neighbourhood gives agreement of germs. -/
theorem eventuallyEq_of_eqOn_isOpen {α : Type*} {F F' : (Fin n → ℝ) × (Fin n → ℝ) → α}
    {U : Set ((Fin n → ℝ) × (Fin n → ℝ))} {y : (Fin n → ℝ) × (Fin n → ℝ)} (hU : IsOpen U)
    (hy : y ∈ U) (h : ∀ y' ∈ U, F y' = F' y') : F =ᶠ[𝓝 y] F' :=
  eventuallyEq_of_mem (hU.mem_nhds hy) h

end KAM.EffectiveStability.Tube

end
