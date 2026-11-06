/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.Tube.Chart.Rotation
public import KAM.EffectiveStability.Tube.Chart.Polar
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

/-!
# Regularity through the polar chart (T2-CONF, N2-Chart)

The polar chart has a symplectic, hence invertible, derivative on `actionPos`, so it has a smooth
local inverse there (inverse function theorem). Consequently a function `G` on phase space is as
regular at `polar y` as its pull-back `G ∘ polar` is at `y`, and with the rotation, at `x` with
`polar y = rotMap Vᵀ x` as `G ∘ rotMap V ∘ polar` is at `y`. This lets an observable be defined
through `polarInv` (which uses `Complex.arg`, discontinuous on a slit) and still be shown smooth.

* `contDiffAt_of_comp_polar`, `differentiableAt_of_comp_polar`;
* `contDiffAt_of_comp_rotMap_polar`, `differentiableAt_of_comp_rotMap_polar`.
-/

@[expose] public noncomputable section

namespace KAM.EffectiveStability.Tube

open KAM Filter Topology Matrix

variable {n : ℕ}

/-- The derivative of `polar` on `actionPos` as a continuous linear equivalence. -/
def polarEquiv {y : (Fin n → ℝ) × (Fin n → ℝ)} (hy : y ∈ actionPos n) :
    ((Fin n → ℝ) × (Fin n → ℝ)) ≃L[ℝ] ((Fin n → ℝ) × (Fin n → ℝ)) :=
  ContinuousLinearEquiv.ofBijective (fderiv ℝ polar y)
    (LinearMap.ker_eq_bot.mpr (bijective_of_symplectic (symplecticForm_fderiv_polar hy)).1)
    (LinearMap.range_eq_top.mpr (bijective_of_symplectic (symplecticForm_fderiv_polar hy)).2)

theorem hasFDerivAt_polarEquiv {y : (Fin n → ℝ) × (Fin n → ℝ)} (hy : y ∈ actionPos n) :
    HasFDerivAt polar ((polarEquiv hy : _ ≃L[ℝ] _) : _ →L[ℝ] _) y := by
  rw [polarEquiv, ContinuousLinearEquiv.coe_ofBijective]
  exact (differentiableAt_polar hy).hasFDerivAt

/-- A local inverse of `polar` near `polar y`: it is `C^k` at `polar y`, sends `polar y` to `y`,
lands in `actionPos` and inverts `polar` near `polar y`. -/
theorem exists_polar_localInverse {y : (Fin n → ℝ) × (Fin n → ℝ)} (hy : y ∈ actionPos n)
    {k : WithTop ℕ∞} (hk : k ≠ 0) :
    ∃ ψ : (Fin n → ℝ) × (Fin n → ℝ) → (Fin n → ℝ) × (Fin n → ℝ),
      ContDiffAt ℝ k ψ (polar y) ∧ ψ (polar y) = y ∧
        ∀ᶠ z in 𝓝 (polar y), ψ z ∈ actionPos n ∧ polar (ψ z) = z := by
  have hpol : ContDiffAt ℝ k polar y := contDiffAt_polar hy
  have hf' := hasFDerivAt_polarEquiv hy
  refine ⟨hpol.localInverse hf' hk, hpol.to_localInverse hf' hk,
    hpol.localInverse_apply_image hf' hk, ?_⟩
  have hcont : ContinuousAt (hpol.localInverse hf' hk) (polar y) :=
    (hpol.to_localInverse hf' hk).continuousAt
  have hmem : ∀ᶠ z in 𝓝 (polar y), hpol.localInverse hf' hk z ∈ actionPos n := by
    apply hcont.preimage_mem_nhds
    rw [hpol.localInverse_apply_image hf' hk]
    exact isOpen_actionPos.mem_nhds hy
  have hinv : ∀ᶠ z in 𝓝 (polar y), polar (hpol.localInverse hf' hk z) = z :=
    (hpol.hasStrictFDerivAt' hf' hk).eventually_right_inverse
  exact hmem.and hinv

/-- `G` is `C^k` at `polar y` if `G ∘ polar` agrees on `actionPos` with a `g` that is `C^k` at
`y`. -/
theorem contDiffAt_of_comp_polar {G g : (Fin n → ℝ) × (Fin n → ℝ) → ℝ} {k : WithTop ℕ∞}
    (hk : k ≠ 0) (hGg : ∀ y' ∈ actionPos n, G (polar y') = g y')
    {y : (Fin n → ℝ) × (Fin n → ℝ)} (hy : y ∈ actionPos n) (hg : ContDiffAt ℝ k g y) :
    ContDiffAt ℝ k G (polar y) := by
  obtain ⟨ψ, hψ, hψy, hev⟩ := exists_polar_localInverse hy hk
  have hgψ : ContDiffAt ℝ k (g ∘ ψ) (polar y) := by
    refine ContDiffAt.comp (polar y) ?_ hψ
    rwa [hψy]
  refine hgψ.congr_of_eventuallyEq ?_
  filter_upwards [hev] with z hz
  rw [Function.comp_apply, ← hGg _ hz.1, hz.2]

/-- `G` is differentiable at `polar y` if `G ∘ polar` agrees on `actionPos` with a `g` that is
differentiable at `y`. -/
theorem differentiableAt_of_comp_polar {G g : (Fin n → ℝ) × (Fin n → ℝ) → ℝ}
    (hGg : ∀ y' ∈ actionPos n, G (polar y') = g y')
    {y : (Fin n → ℝ) × (Fin n → ℝ)} (hy : y ∈ actionPos n) (hg : DifferentiableAt ℝ g y) :
    DifferentiableAt ℝ G (polar y) := by
  obtain ⟨ψ, hψ, hψy, hev⟩ := exists_polar_localInverse hy (k := 1) one_ne_zero
  have hgψ : DifferentiableAt ℝ (g ∘ ψ) (polar y) := by
    refine DifferentiableAt.comp (polar y) ?_ (hψ.differentiableAt one_ne_zero)
    rwa [hψy]
  refine hgψ.congr_of_eventuallyEq ?_
  filter_upwards [hev] with z hz
  rw [Function.comp_apply, ← hGg _ hz.1, hz.2]

/-- `G` is `C^k` at `x` if `G ∘ rotMap V ∘ polar` agrees on `actionPos` with a `g` that is `C^k`
at `y`, where `polar y = rotMap Vᵀ x` and `V` is orthogonal. -/
theorem contDiffAt_of_comp_rotMap_polar {V : Matrix (Fin n) (Fin n) ℝ} (hV : Vᵀ * V = 1)
    {G g : (Fin n → ℝ) × (Fin n → ℝ) → ℝ} {k : WithTop ℕ∞} (hk : k ≠ 0)
    (hGg : ∀ y' ∈ actionPos n, G (rotMap V (polar y')) = g y')
    {x y : (Fin n → ℝ) × (Fin n → ℝ)} (hy : y ∈ actionPos n) (hxy : polar y = rotMap Vᵀ x)
    (hg : ContDiffAt ℝ k g y) : ContDiffAt ℝ k G x := by
  have h1 : ContDiffAt ℝ k (G ∘ rotMap V) (rotMap Vᵀ x) := by
    rw [← hxy]
    exact contDiffAt_of_comp_polar hk hGg hy hg
  have h2 := contDiffAt_comp_rotMap Vᵀ h1
  have hGG : (G ∘ rotMap V) ∘ rotMap Vᵀ = G := by
    funext z
    simp [rotMap_rotMap_transpose hV]
  rwa [hGG] at h2

/-- `G` is differentiable at `x` if `G ∘ rotMap V ∘ polar` agrees on `actionPos` with a `g` that
is differentiable at `y`, where `polar y = rotMap Vᵀ x` and `V` is orthogonal. -/
theorem differentiableAt_of_comp_rotMap_polar {V : Matrix (Fin n) (Fin n) ℝ} (hV : Vᵀ * V = 1)
    {G g : (Fin n → ℝ) × (Fin n → ℝ) → ℝ}
    (hGg : ∀ y' ∈ actionPos n, G (rotMap V (polar y')) = g y')
    {x y : (Fin n → ℝ) × (Fin n → ℝ)} (hy : y ∈ actionPos n) (hxy : polar y = rotMap Vᵀ x)
    (hg : DifferentiableAt ℝ g y) : DifferentiableAt ℝ G x := by
  have h1 : DifferentiableAt ℝ (G ∘ rotMap V) (rotMap Vᵀ x) := by
    rw [← hxy]
    exact differentiableAt_of_comp_polar hGg hy hg
  have h2 := differentiableAt_comp_rotMap Vᵀ h1
  have hGG : (G ∘ rotMap V) ∘ rotMap Vᵀ = G := by
    funext z
    simp [rotMap_rotMap_transpose hV]
  rwa [hGG] at h2

end KAM.EffectiveStability.Tube

end
