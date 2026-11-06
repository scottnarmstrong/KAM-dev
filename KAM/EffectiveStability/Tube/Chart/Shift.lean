/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.Tube.Chart.Bracket
public import Mathlib.Data.Fin.VecNotation

/-!
# The gradient shift and the angle reduction (T2-CONF, N2-Chart, target (D))

Three modes, actions `I : Fin 3 → ℝ` (positions) and angles `θ : Fin 3 → ℝ` (momenta). The reduced
angles are `φ = phiOf θ = (θ₀ - θ₂, θ₁ - θ₂)`, and the shifted actions are `u = I - B(φ)` for a
differentiable `B : (Fin 2 → ℝ) → (Fin 3 → ℝ)`:
`shiftChart B (I, θ) = (I - B (phiOf θ), phiOf θ)`.

On functions of `φ` the angle derivatives act as `∂_{θ_i} = fderiv · (phiOf (Pi.single i 1))`, i.e.
`∂_{θ₀} = ∂_{φ₀}`, `∂_{θ₁} = ∂_{φ₁}`, `∂_{θ₂} = -∂_{φ₀} - ∂_{φ₁}`. The symmetry hypothesis
`∂_{θ_i} B_l = ∂_{θ_l} B_i` (all `i, l : Fin 3`) is what makes the shift canonical: it holds for
`B_l = Ī_l + ∂_{θ_l} S` with `S` a `C²` function of `φ` (`shift_symm_of_gradient`).

* `bracketSum_comp_shiftChart` (target (D)): for `f`, `h̃` functions of `(u, φ)`,
  `bracketSum (f ∘ shiftChart B) (h̃ ∘ shiftChart B) (I, θ) = reducedBracket f h̃ (u, φ)`, where
  `reducedBracket f h̃ = Σ_{a=0,1} (D_a f · ∂_{φ_a} h̃ - ∂_{φ_a} f · D_a h̃)`,
  `D_a = ∂_{u_a} - ∂_{u_2}`.
-/

@[expose] public noncomputable section

namespace KAM.EffectiveStability.Tube

open KAM Filter Topology

/-- The reduced angles `φ = (θ₀ - θ₂, θ₁ - θ₂)`. -/
def phiOf (θ : Fin 3 → ℝ) : Fin 2 → ℝ := ![θ 0 - θ 2, θ 1 - θ 2]

@[simp] theorem phiOf_apply_zero (θ : Fin 3 → ℝ) : phiOf θ 0 = θ 0 - θ 2 := rfl

@[simp] theorem phiOf_apply_one (θ : Fin 3 → ℝ) : phiOf θ 1 = θ 1 - θ 2 := rfl

/-- `phiOf` as a linear map. -/
def phiLin : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) where
  toFun := phiOf
  map_add' a b := by
    ext i
    fin_cases i <;> simp [phiOf] <;> ring
  map_smul' c a := by
    ext i
    fin_cases i <;> simp [phiOf] <;> ring

/-- `phiOf` as a continuous linear map. -/
def phiCLM : (Fin 3 → ℝ) →L[ℝ] (Fin 2 → ℝ) := LinearMap.toContinuousLinearMap phiLin

theorem phiCLM_apply (θ : Fin 3 → ℝ) : phiCLM θ = phiOf θ := rfl

theorem phiOf_eq_phiCLM : phiOf = ⇑phiCLM := funext fun θ => (phiCLM_apply θ).symm

/-- The projection `(I, θ) ↦ I`. -/
abbrev fstI : (Fin 3 → ℝ) × (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ) := ContinuousLinearMap.fst ℝ _ _

/-- The projection `(I, θ) ↦ θ`. -/
abbrev sndθ : (Fin 3 → ℝ) × (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ) := ContinuousLinearMap.snd ℝ _ _

/-- The shift chart `(I, θ) ↦ (u, φ) = (I - B (phiOf θ), phiOf θ)`. -/
def shiftChart (B : (Fin 2 → ℝ) → (Fin 3 → ℝ)) (y : (Fin 3 → ℝ) × (Fin 3 → ℝ)) :
    (Fin 3 → ℝ) × (Fin 2 → ℝ) :=
  (y.1 - B (phiOf y.2), phiOf y.2)

/-- The derivative of `shiftChart B`, given a derivative `B'` of `B`. -/
def shiftD (B' : (Fin 2 → ℝ) →L[ℝ] (Fin 3 → ℝ)) :
    (Fin 3 → ℝ) × (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ) × (Fin 2 → ℝ) :=
  (fstI - B'.comp (phiCLM.comp sndθ)).prod
    (phiCLM.comp sndθ)

theorem hasFDerivAt_shiftChart {B : (Fin 2 → ℝ) → (Fin 3 → ℝ)} {y : (Fin 3 → ℝ) × (Fin 3 → ℝ)}
    (hB : DifferentiableAt ℝ B (phiOf y.2)) :
    HasFDerivAt (shiftChart B) (shiftD (fderiv ℝ B (phiOf y.2))) y := by
  have hφ : HasFDerivAt (fun y : (Fin 3 → ℝ) × (Fin 3 → ℝ) => phiOf y.2)
      (phiCLM.comp sndθ) y := by
    rw [phiOf_eq_phiCLM]
    exact (phiCLM.comp sndθ).hasFDerivAt
  have hBφ : HasFDerivAt (fun y : (Fin 3 → ℝ) × (Fin 3 → ℝ) => B (phiOf y.2))
      ((fderiv ℝ B (phiOf y.2)).comp (phiCLM.comp sndθ)) y :=
    hB.hasFDerivAt.comp y hφ
  exact (hasFDerivAt_fst.sub hBφ).prodMk hφ

theorem differentiableAt_shiftChart {B : (Fin 2 → ℝ) → (Fin 3 → ℝ)}
    {y : (Fin 3 → ℝ) × (Fin 3 → ℝ)} (hB : DifferentiableAt ℝ B (phiOf y.2)) :
    DifferentiableAt ℝ (shiftChart B) y :=
  (hasFDerivAt_shiftChart hB).differentiableAt

/-- The reduced bracket `Σ_{a=0,1} (D_a f · ∂_{φ_a} h - ∂_{φ_a} f · D_a h)` at `p = (u, φ)`, with
`D_a = ∂_{u_a} - ∂_{u_2}` and `∂_{φ_a}` the partial derivative in the second argument. -/
def reducedBracket (f h : (Fin 3 → ℝ) × (Fin 2 → ℝ) → ℝ) (p : (Fin 3 → ℝ) × (Fin 2 → ℝ)) : ℝ :=
  ∑ a : Fin 2,
    ((fderiv ℝ f p (Pi.single a.castSucc 1, 0) - fderiv ℝ f p (Pi.single 2 1, 0)) *
        fderiv ℝ h p (0, Pi.single a 1) -
      fderiv ℝ f p (0, Pi.single a 1) *
        (fderiv ℝ h p (Pi.single a.castSucc 1, 0) - fderiv ℝ h p (Pi.single 2 1, 0)))

private theorem fderiv_comp_shiftChart_apply {f : (Fin 3 → ℝ) × (Fin 2 → ℝ) → ℝ}
    {B : (Fin 2 → ℝ) → (Fin 3 → ℝ)} {y : (Fin 3 → ℝ) × (Fin 3 → ℝ)}
    (hf : DifferentiableAt ℝ f (shiftChart B y)) (hB : DifferentiableAt ℝ B (phiOf y.2))
    (w : (Fin 3 → ℝ) × (Fin 3 → ℝ)) :
    fderiv ℝ (f ∘ shiftChart B) y w =
      fderiv ℝ f (shiftChart B y) (shiftD (fderiv ℝ B (phiOf y.2)) w) := by
  rw [(hf.hasFDerivAt.comp y (hasFDerivAt_shiftChart hB)).fderiv]
  rfl

private theorem shiftD_single_fst (B' : (Fin 2 → ℝ) →L[ℝ] (Fin 3 → ℝ)) (j : Fin 3) :
    shiftD B' (Pi.single j 1, 0) = (Pi.single j 1, 0) := by
  simp [shiftD]

private theorem shiftD_single_snd (B' : (Fin 2 → ℝ) →L[ℝ] (Fin 3 → ℝ)) (j : Fin 3) :
    shiftD B' (0, Pi.single j 1) = (-B' (phiOf (Pi.single j 1)), phiOf (Pi.single j 1)) := by
  simp [shiftD, phiCLM_apply]

/-- **Target (D): shift and angle reduction.** For `f`, `h̃` differentiable at `(u, φ) =
shiftChart B y`, `B` differentiable at `φ` with the symmetry `∂_{θ_i} B_l = ∂_{θ_l} B_i`, the
canonical bracket of `g = f ∘ shiftChart B` and `h = h̃ ∘ shiftChart B` at `y = (I, θ)` is the
reduced bracket of `f` and `h̃` at `(u, φ)`. -/
theorem bracketSum_comp_shiftChart {f h : (Fin 3 → ℝ) × (Fin 2 → ℝ) → ℝ}
    {B : (Fin 2 → ℝ) → (Fin 3 → ℝ)} {y : (Fin 3 → ℝ) × (Fin 3 → ℝ)}
    (hf : DifferentiableAt ℝ f (shiftChart B y)) (hh : DifferentiableAt ℝ h (shiftChart B y))
    (hB : DifferentiableAt ℝ B (phiOf y.2))
    (hsym : ∀ i l : Fin 3, fderiv ℝ B (phiOf y.2) (phiOf (Pi.single i 1)) l =
      fderiv ℝ B (phiOf y.2) (phiOf (Pi.single l 1)) i) :
    bracketSum (f ∘ shiftChart B) (h ∘ shiftChart B) y = reducedBracket f h (shiftChart B y) := by
  have h01 := hsym 0 1
  have h02 := hsym 0 2
  have h12 := hsym 1 2
  simp only [bracketSum, reducedBracket, fderiv_comp_shiftChart_apply hf hB,
    fderiv_comp_shiftChart_apply hh hB, shiftD_single_fst, shiftD_single_snd]
  simp only [clm_prod_apply_eq_sum (fderiv ℝ f (shiftChart B y)) (-_) (phiOf _),
    clm_prod_apply_eq_sum (fderiv ℝ h (shiftChart B y)) (-_) (phiOf _)]
  simp only [Fin.sum_univ_three, Fin.sum_univ_two, Pi.neg_apply, phiOf_apply_zero,
    phiOf_apply_one, Pi.single_apply]
  simp
  set fu : Fin 3 → ℝ := fun i => fderiv ℝ f (shiftChart B y) (Pi.single i 1, 0) with hfu
  set hu : Fin 3 → ℝ := fun i => fderiv ℝ h (shiftChart B y) (Pi.single i 1, 0) with hhu
  have e : ∀ i, fderiv ℝ f (shiftChart B y) (Pi.single i 1, 0) = fu i := fun i => rfl
  have e' : ∀ i, fderiv ℝ h (shiftChart B y) (Pi.single i 1, 0) = hu i := fun i => rfl
  simp only [e, e']
  linear_combination (hu 0 * fu 1 - fu 0 * hu 1) * h01 + (hu 0 * fu 2 - fu 0 * hu 2) * h02 +
    (hu 1 * fu 2 - hu 2 * fu 1) * h12
