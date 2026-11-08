/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.Tube.Chart.Composite

/-!
# Observables defined through the tube chart (T2-CONF, N2-Chart)

A literal observable `f` of `(u, φ)`, `2π`-periodic in `φ`, defines the phase-space observable
`x ↦ f (tubeChart V B x)` (for a `2π`-periodic shift `B`). Although `tubeChart` uses `Complex.arg`,
this observable satisfies the chart identity of target (E) on all of `actionPos`, is as smooth as
`f` and `B` on the punctured set (for orthogonal `V`), and, under the Hamiltonian identity,
differentiability and symmetry hypotheses of the rate theorem, its rate along `X_H` is the reduced
bracket.

* `comp_tubeChart_rotMap_polar`: `f (tubeChart V B (rotMap V (polar y))) = f (shiftChart B y)` for
  `y ∈ actionPos 3`.
* `contDiffAt_comp_tubeChart`, `differentiableAt_comp_tubeChart`: regularity at points whose
  rotated modes are all nonzero.
* `fderiv_comp_tubeChart_apply_hamiltonianVectorField`: the rate formula for such observables.
-/

@[expose] public noncomputable section

namespace KAM.EffectiveStability.Tube

open KAM Filter Topology Matrix Real

/-- The integer shift of the reduced angles induced by integer shifts of the angles. -/
theorem phiOf_add_two_pi (θ : Fin 3 → ℝ) (k : Fin 3 → ℤ) :
    phiOf (θ + fun j => 2 * π * k j) =
      phiOf θ + fun a => 2 * π * (![k 0 - k 2, k 1 - k 2] a : ℤ) := by
  ext a
  fin_cases a <;> simp [phiOf] <;> ring

/-- With a `2π`-periodic `B`, shifting the angles by `2πk` shifts `(u, φ)` by `(0, 2πm)`. -/
theorem shiftChart_add_two_pi {B : (Fin 2 → ℝ) → (Fin 3 → ℝ)}
    (hBper : ∀ (φ : Fin 2 → ℝ) (m : Fin 2 → ℤ), B (φ + fun a => 2 * π * m a) = B φ)
    (y : (Fin 3 → ℝ) × (Fin 3 → ℝ)) (k : Fin 3 → ℤ) :
    shiftChart B (y.1, y.2 + fun j => 2 * π * k j) =
      ((shiftChart B y).1,
        (shiftChart B y).2 + fun a => 2 * π * (![k 0 - k 2, k 1 - k 2] a : ℤ)) := by
  simp only [shiftChart, phiOf_add_two_pi, hBper]

/-- **The chart identity for observables defined through `tubeChart`.** For `2π`-periodic `B` and
`f` (in `φ`), `f (tubeChart V B (rotMap V (polar y))) = f (shiftChart B y)` on `actionPos 3`. -/
theorem comp_tubeChart_rotMap_polar {V : Matrix (Fin 3) (Fin 3) ℝ} (hV : Vᵀ * V = 1)
    {B : (Fin 2 → ℝ) → (Fin 3 → ℝ)} {α : Type*} {f : (Fin 3 → ℝ) × (Fin 2 → ℝ) → α}
    (hBper : ∀ (φ : Fin 2 → ℝ) (m : Fin 2 → ℤ), B (φ + fun a => 2 * π * m a) = B φ)
    (hfper : ∀ (u : Fin 3 → ℝ) (φ : Fin 2 → ℝ) (m : Fin 2 → ℤ),
      f (u, φ + fun a => 2 * π * m a) = f (u, φ))
    {y : (Fin 3 → ℝ) × (Fin 3 → ℝ)} (hy : y ∈ actionPos 3) :
    f (tubeChart V B (rotMap V (polar y))) = f (shiftChart B y) := by
  obtain ⟨h1, h2⟩ := polarInv_polar hy
  choose k hk using h2
  have hpi : polarInv (polar y) = (y.1, y.2 + fun j => 2 * π * k j) := by
    refine Prod.ext h1 (funext fun j => ?_)
    simp [hk j]
  rw [tubeChart, rotMap_transpose_rotMap hV, hpi, shiftChart_add_two_pi hBper, hfper]

/-- `polarInv` of the rotated point lies in `actionPos` and is a polar preimage of it. -/
theorem polarInv_rotMap_mem {V : Matrix (Fin 3) (Fin 3) ℝ} {x : (Fin 3 → ℝ) × (Fin 3 → ℝ)}
    (hx : ∀ j, 0 < (rotMap Vᵀ x).1 j ^ 2 + (rotMap Vᵀ x).2 j ^ 2) :
    polarInv (rotMap Vᵀ x) ∈ actionPos 3 ∧ polar (polarInv (rotMap Vᵀ x)) = rotMap Vᵀ x :=
  ⟨polarInv_mem_actionPos hx, polar_polarInv _⟩

/-- **Regularity of observables defined through `tubeChart`.** If `f` is `C^k` (`k ≠ 0`) at
`tubeChart V B x` and `B` is `C^k` at its `φ`, then `x ↦ f (tubeChart V B x)` is `C^k` at every `x`
whose rotated modes are all nonzero (periodicity removes the branch cut of `arg`). -/
theorem contDiffAt_comp_tubeChart {V : Matrix (Fin 3) (Fin 3) ℝ} (hV : Vᵀ * V = 1)
    {B : (Fin 2 → ℝ) → (Fin 3 → ℝ)} {f : (Fin 3 → ℝ) × (Fin 2 → ℝ) → ℝ} {k : WithTop ℕ∞}
    (hk : k ≠ 0)
    (hBper : ∀ (φ : Fin 2 → ℝ) (m : Fin 2 → ℤ), B (φ + fun a => 2 * π * m a) = B φ)
    (hfper : ∀ (u : Fin 3 → ℝ) (φ : Fin 2 → ℝ) (m : Fin 2 → ℤ),
      f (u, φ + fun a => 2 * π * m a) = f (u, φ))
    {x : (Fin 3 → ℝ) × (Fin 3 → ℝ)}
    (hx : ∀ j, 0 < (rotMap Vᵀ x).1 j ^ 2 + (rotMap Vᵀ x).2 j ^ 2)
    (hf : ContDiffAt ℝ k f (tubeChart V B x)) (hB : ContDiffAt ℝ k B (tubeChart V B x).2) :
    ContDiffAt ℝ k (fun x => f (tubeChart V B x)) x := by
  obtain ⟨hy, hxy⟩ := polarInv_rotMap_mem hx
  set y := polarInv (rotMap Vᵀ x)
  have hφ : ContDiff ℝ k (fun y : (Fin 3 → ℝ) × (Fin 3 → ℝ) => phiOf y.2) := by
    rw [phiOf_eq_phiCLM]
    exact phiCLM.contDiff.comp contDiff_snd
  have hsc : ContDiffAt ℝ k (shiftChart B) y :=
    (contDiffAt_fst.sub (hB.comp y hφ.contDiffAt)).prodMk hφ.contDiffAt
  exact contDiffAt_of_comp_rotMap_polar hV hk
    (fun y' hy' => comp_tubeChart_rotMap_polar hV hBper hfper hy') hy hxy (hf.comp y hsc)

/-- **Differentiability of observables defined through `tubeChart`** (as
`contDiffAt_comp_tubeChart`, with differentiability). -/
theorem differentiableAt_comp_tubeChart {V : Matrix (Fin 3) (Fin 3) ℝ} (hV : Vᵀ * V = 1)
    {B : (Fin 2 → ℝ) → (Fin 3 → ℝ)} {f : (Fin 3 → ℝ) × (Fin 2 → ℝ) → ℝ}
    (hBper : ∀ (φ : Fin 2 → ℝ) (m : Fin 2 → ℤ), B (φ + fun a => 2 * π * m a) = B φ)
    (hfper : ∀ (u : Fin 3 → ℝ) (φ : Fin 2 → ℝ) (m : Fin 2 → ℤ),
      f (u, φ + fun a => 2 * π * m a) = f (u, φ))
    {x : (Fin 3 → ℝ) × (Fin 3 → ℝ)}
    (hx : ∀ j, 0 < (rotMap Vᵀ x).1 j ^ 2 + (rotMap Vᵀ x).2 j ^ 2)
    (hf : DifferentiableAt ℝ f (tubeChart V B x)) (hB : DifferentiableAt ℝ B (tubeChart V B x).2) :
    DifferentiableAt ℝ (fun x => f (tubeChart V B x)) x := by
  obtain ⟨hy, hxy⟩ := polarInv_rotMap_mem hx
  exact differentiableAt_of_comp_rotMap_polar hV
    (fun y' hy' => comp_tubeChart_rotMap_polar hV hBper hfper hy') hy hxy
    (hf.comp (polarInv (rotMap Vᵀ x)) (differentiableAt_shiftChart hB))

/-- **The rate of an observable defined through `tubeChart`.** For `2π`-periodic `B` and `f`, a
Hamiltonian `H` with `H (rotMap V (polar y)) = h̃ (shiftChart B y)` on `actionPos 3`, and `x` whose
rotated modes are all nonzero, with `f`, `h̃` differentiable at `(u, φ) = tubeChart V B x`, `B`
differentiable at `φ` and `∂_{θ_i} B_l = ∂_{θ_l} B_i` at `φ`:
`fderiv ℝ (f ∘ tubeChart V B) x (X_H x) = Σ_a (D_a f · ∂_{φ_a} h̃ - ∂_{φ_a} f · D_a h̃) (u, φ)`. -/
theorem fderiv_comp_tubeChart_apply_hamiltonianVectorField {V : Matrix (Fin 3) (Fin 3) ℝ}
    (hV : Vᵀ * V = 1) {B : (Fin 2 → ℝ) → (Fin 3 → ℝ)} {f h : (Fin 3 → ℝ) × (Fin 2 → ℝ) → ℝ}
    {H : (Fin 3 → ℝ) × (Fin 3 → ℝ) → ℝ}
    (hBper : ∀ (φ : Fin 2 → ℝ) (m : Fin 2 → ℤ), B (φ + fun a => 2 * π * m a) = B φ)
    (hfper : ∀ (u : Fin 3 → ℝ) (φ : Fin 2 → ℝ) (m : Fin 2 → ℤ),
      f (u, φ + fun a => 2 * π * m a) = f (u, φ))
    (hHh : ∀ y ∈ actionPos 3, H (rotMap V (polar y)) = h (shiftChart B y))
    {x : (Fin 3 → ℝ) × (Fin 3 → ℝ)}
    (hx : ∀ j, 0 < (rotMap Vᵀ x).1 j ^ 2 + (rotMap Vᵀ x).2 j ^ 2)
    (hf : DifferentiableAt ℝ f (tubeChart V B x)) (hh : DifferentiableAt ℝ h (tubeChart V B x))
    (hB : DifferentiableAt ℝ B (tubeChart V B x).2)
    (hsym : ∀ i l : Fin 3, fderiv ℝ B (tubeChart V B x).2 (phiOf (Pi.single i 1)) l =
      fderiv ℝ B (tubeChart V B x).2 (phiOf (Pi.single l 1)) i) :
    fderiv ℝ (fun x => f (tubeChart V B x)) x (hamiltonianVectorField H x) =
      reducedBracket f h (tubeChart V B x) :=
  fderiv_apply_hamiltonianVectorField_eq_reducedBracket_tubeChart hV
    (fun _ hy' => comp_tubeChart_rotMap_polar hV hBper hfper hy') hHh hx hf hh hB hsym

end KAM.EffectiveStability.Tube

end
