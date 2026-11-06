/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.Tube.Chart.LocalInverse
public import KAM.EffectiveStability.Tube.Chart.ShiftSymm

/-!
# The tube chart: rates of observables in `(u, φ)` (T2-CONF, N2-Chart, target (E))

The composite chart `x ↦ (u, φ)` of the tube checker: rotation `R = rotMap Vᵀ` (`V` orthogonal),
polar chart inverse `polarInv`, then the shift `shiftChart B`:
`tubeChart V B x = shiftChart B (polarInv (rotMap Vᵀ x))`.

* `fderiv_apply_hamiltonianVectorField_eq_reducedBracket` (target (E)): if
  `G (Rinv (polar y)) = f (shiftChart B y)` and `H (Rinv (polar y)) = h̃ (shiftChart B y)` for all
  `y` with positive actions, then at any `x` with `polar y = R x`, `y` with positive actions,
  `fderiv ℝ G x (X_H x) = reducedBracket f h̃ (shiftChart B y)`
  `= Σ_a (D_a f · ∂_{φ_a} h̃ - ∂_{φ_a} f · D_a h̃) (u, φ)`.
* `fderiv_apply_hamiltonianVectorField_eq_reducedBracket_tubeChart`: the same at the canonical chart
  image `tubeChart V B x`, for every `x` whose rotated modes are all nonzero.
* `fderiv_apply_hamiltonianVectorField_eq_reducedBracket_of_gradient`: the same with the symmetry
  hypothesis discharged for a gradient shift `B_l = c_l + ∂_{θ_l} S`.
-/

@[expose] public noncomputable section

namespace KAM.EffectiveStability.Tube

open KAM Filter Topology Matrix

theorem shiftChart_apply (B : (Fin 2 → ℝ) → (Fin 3 → ℝ)) (y : (Fin 3 → ℝ) × (Fin 3 → ℝ)) :
    shiftChart B y = (y.1 - B (phiOf y.2), phiOf y.2) := rfl

/-- The composite chart `x ↦ (u, φ) = shiftChart B (polarInv (rotMap Vᵀ x))`. -/
def tubeChart (V : Matrix (Fin 3) (Fin 3) ℝ) (B : (Fin 2 → ℝ) → (Fin 3 → ℝ))
    (x : (Fin 3 → ℝ) × (Fin 3 → ℝ)) : (Fin 3 → ℝ) × (Fin 2 → ℝ) :=
  shiftChart B (polarInv (rotMap Vᵀ x))

/-- **Target (E): the composite rate formula.** Let `V` be orthogonal, `f`, `h̃` functions of
`(u, φ)`, and `G`, `H` functions on phase space with `G (rotMap V (polar y)) = f (shiftChart B y)`
and `H (rotMap V (polar y)) = h̃ (shiftChart B y)` for every `y` with positive actions. At a point
`x` with `polar y = rotMap Vᵀ x` for some `y` with positive actions, if `f`, `h̃` are
differentiable at `(u, φ) = shiftChart B y`, `B` at `φ`, and `∂_{θ_i} B_l = ∂_{θ_l} B_i` at `φ`,
then `fderiv ℝ G x (X_H x) = Σ_a (D_a f · ∂_{φ_a} h̃ - ∂_{φ_a} f · D_a h̃) (u, φ)`. (`G` and `H` are
then differentiable at `x`, by the local inverse of the polar chart.) -/
theorem fderiv_apply_hamiltonianVectorField_eq_reducedBracket {V : Matrix (Fin 3) (Fin 3) ℝ}
    (hV : Vᵀ * V = 1) {B : (Fin 2 → ℝ) → (Fin 3 → ℝ)} {f h : (Fin 3 → ℝ) × (Fin 2 → ℝ) → ℝ}
    {G H : (Fin 3 → ℝ) × (Fin 3 → ℝ) → ℝ}
    (hGf : ∀ y ∈ actionPos 3, G (rotMap V (polar y)) = f (shiftChart B y))
    (hHh : ∀ y ∈ actionPos 3, H (rotMap V (polar y)) = h (shiftChart B y))
    {x y : (Fin 3 → ℝ) × (Fin 3 → ℝ)} (hy : y ∈ actionPos 3) (hxy : polar y = rotMap Vᵀ x)
    (hf : DifferentiableAt ℝ f (shiftChart B y)) (hh : DifferentiableAt ℝ h (shiftChart B y))
    (hB : DifferentiableAt ℝ B (phiOf y.2))
    (hsym : ∀ i l : Fin 3, fderiv ℝ B (phiOf y.2) (phiOf (Pi.single i 1)) l =
      fderiv ℝ B (phiOf y.2) (phiOf (Pi.single l 1)) i) :
    fderiv ℝ G x (hamiltonianVectorField H x) = reducedBracket f h (shiftChart B y) := by
  have hx : rotMap V (polar y) = x := by rw [hxy, rotMap_rotMap_transpose hV]
  have hG : DifferentiableAt ℝ G x := differentiableAt_of_comp_rotMap_polar hV hGf hy hxy
    (hf.comp y (differentiableAt_shiftChart hB))
  have hH : DifferentiableAt ℝ H x := differentiableAt_of_comp_rotMap_polar hV hHh hy hxy
    (hh.comp y (differentiableAt_shiftChart hB))
  have hG₁ : DifferentiableAt ℝ (G ∘ rotMap V) (polar y) :=
    differentiableAt_comp_rotMap V (by rwa [hx])
  have hH₁ : DifferentiableAt ℝ (H ∘ rotMap V) (polar y) :=
    differentiableAt_comp_rotMap V (by rwa [hx])
  -- rotation
  have e1 := fderiv_comp_rotMap_apply_hamiltonianVectorField hV (G := G ∘ rotMap V) (x := x)
    (by rwa [← hxy]) hH
  have hGG : (G ∘ rotMap V) ∘ rotMap Vᵀ = G := by
    funext z
    simp [rotMap_rotMap_transpose hV]
  rw [hGG, ← hxy] at e1
  -- polar chart
  rw [e1, fderiv_apply_hamiltonianVectorField_polar hy hG₁ hH₁]
  -- the identities near `y`
  rw [fderiv_apply_hamiltonianVectorField_congr (G := (G ∘ rotMap V) ∘ polar)
    (H := (H ∘ rotMap V) ∘ polar) (G' := f ∘ shiftChart B) (H' := h ∘ shiftChart B)
    (eventuallyEq_of_eqOn_isOpen isOpen_actionPos hy fun y' hy' => hGf y' hy')
    (eventuallyEq_of_eqOn_isOpen isOpen_actionPos hy fun y' hy' => hHh y' hy'),
    fderiv_apply_hamiltonianVectorField_eq_bracketSum]
  -- shift and angle reduction
  exact bracketSum_comp_shiftChart hf hh hB hsym

/-- **Target (E) at the canonical chart image.** For `x` whose rotated modes are all nonzero, the
rate is the reduced bracket at `tubeChart V B x`. -/
theorem fderiv_apply_hamiltonianVectorField_eq_reducedBracket_tubeChart
    {V : Matrix (Fin 3) (Fin 3) ℝ} (hV : Vᵀ * V = 1) {B : (Fin 2 → ℝ) → (Fin 3 → ℝ)}
    {f h : (Fin 3 → ℝ) × (Fin 2 → ℝ) → ℝ} {G H : (Fin 3 → ℝ) × (Fin 3 → ℝ) → ℝ}
    (hGf : ∀ y ∈ actionPos 3, G (rotMap V (polar y)) = f (shiftChart B y))
    (hHh : ∀ y ∈ actionPos 3, H (rotMap V (polar y)) = h (shiftChart B y))
    {x : (Fin 3 → ℝ) × (Fin 3 → ℝ)}
    (hx : ∀ j, 0 < (rotMap Vᵀ x).1 j ^ 2 + (rotMap Vᵀ x).2 j ^ 2)
    (hf : DifferentiableAt ℝ f (tubeChart V B x)) (hh : DifferentiableAt ℝ h (tubeChart V B x))
    (hB : DifferentiableAt ℝ B (tubeChart V B x).2)
    (hsym : ∀ i l : Fin 3, fderiv ℝ B (tubeChart V B x).2 (phiOf (Pi.single i 1)) l =
      fderiv ℝ B (tubeChart V B x).2 (phiOf (Pi.single l 1)) i) :
    fderiv ℝ G x (hamiltonianVectorField H x) = reducedBracket f h (tubeChart V B x) :=
  fderiv_apply_hamiltonianVectorField_eq_reducedBracket hV hGf hHh (polarInv_mem_actionPos hx)
    (polar_polarInv _) hf hh hB hsym

/-- **Target (E), gradient shift.** As `fderiv_apply_hamiltonianVectorField_eq_reducedBracket`,
with the symmetry hypothesis discharged for `B φ' l = c l + ∂_{θ_l} S φ'` near `φ`, `S` `C²` at
`φ`. -/
theorem fderiv_apply_hamiltonianVectorField_eq_reducedBracket_of_gradient
    {V : Matrix (Fin 3) (Fin 3) ℝ} (hV : Vᵀ * V = 1) {B : (Fin 2 → ℝ) → (Fin 3 → ℝ)}
    {S : (Fin 2 → ℝ) → ℝ} {c : Fin 3 → ℝ} {f h : (Fin 3 → ℝ) × (Fin 2 → ℝ) → ℝ}
    {G H : (Fin 3 → ℝ) × (Fin 3 → ℝ) → ℝ}
    (hGf : ∀ y ∈ actionPos 3, G (rotMap V (polar y)) = f (shiftChart B y))
    (hHh : ∀ y ∈ actionPos 3, H (rotMap V (polar y)) = h (shiftChart B y))
    {x y : (Fin 3 → ℝ) × (Fin 3 → ℝ)} (hy : y ∈ actionPos 3) (hxy : polar y = rotMap Vᵀ x)
    (hf : DifferentiableAt ℝ f (shiftChart B y)) (hh : DifferentiableAt ℝ h (shiftChart B y))
    (hB : DifferentiableAt ℝ B (phiOf y.2)) (hS : ContDiffAt ℝ 2 S (phiOf y.2))
    (hBS : B =ᶠ[𝓝 (phiOf y.2)] fun φ' l => c l + fderiv ℝ S φ' (phiOf (Pi.single l 1))) :
    fderiv ℝ G x (hamiltonianVectorField H x) = reducedBracket f h (shiftChart B y) :=
  fderiv_apply_hamiltonianVectorField_eq_reducedBracket hV hGf hHh hy hxy hf hh hB
    (shift_symm_of_gradient hS hBS)

end KAM.EffectiveStability.Tube

end
