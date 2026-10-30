/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-!
# Complexification and real analyticity: the generic part

Blueprint-W `bpW:w1:complexification-lemma` (ii), (iii) (package W1-ANALYTIC). This is
source-faithful infrastructure used by several nodes; the dependency graph is still being built.

If `f` is `ℂ`-analytic at `ℓ x` between complex normed spaces and `ℓ`, `π` are continuous
`ℝ`-linear, then `π ∘ f ∘ ℓ` is `ℝ`-analytic at `x` (`KAM.Wave.analyticAt_comp_realLinear`). For a
real-linear section pair `ι : V → F₁`, `re : F₂ → G` with `re ∘ ι₂ = id` and `f` real on reals, the
real part `re ∘ f ∘ ι₁` is `ℝ`-analytic, `ι₂ ∘ (re ∘ f ∘ ι₁) = f ∘ ι₁` and its derivative is
`re (D f (ι₁ y) (ι₁ h))` (`KAM.Wave.analyticAt_real_part`). The concrete maps `ι`, `re` on `ℓ²`
are in `KAM/Wave/Analytic/ComplexificationLp.lean`.
-/

@[expose] public section

open Filter Topology

namespace KAM.Wave

variable {V G : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  {F₁ F₂ : Type*} [NormedAddCommGroup F₁] [NormedSpace ℂ F₁]
  [NormedAddCommGroup F₂] [NormedSpace ℂ F₂]

/-- Blueprint `bpW:w1:complexification-lemma` (ii). -/
theorem analyticAt_comp_realLinear (ℓ : V →L[ℝ] F₁) (π : F₂ →L[ℝ] G) {f : F₁ → F₂} {x : V}
    (hf : AnalyticAt ℂ f (ℓ x)) : AnalyticAt ℝ (fun y => π (f (ℓ y))) x :=
  (π.analyticAt _).comp ((hf.restrictScalars (𝕜 := ℝ)).comp (ℓ.analyticAt x))

/-- Blueprint `bpW:w1:complexification-lemma` (iii): the real part of a `ℂ`-analytic map that is
real on reals is `ℝ`-analytic, recovers the map, and has derivative `re ∘ Df ∘ ι`. -/
theorem analyticAt_real_part (ι₁ : V →L[ℝ] F₁) (ι₂ : G →L[ℝ] F₂) (re₂ : F₂ →L[ℝ] G)
    (hre : ∀ w, re₂ (ι₂ w) = w) {f : F₁ → F₂} {y : V} (hf : AnalyticAt ℂ f (ι₁ y))
    (hreal : ∀ᶠ y' in 𝓝 y, ∃ w, f (ι₁ y') = ι₂ w) :
    AnalyticAt ℝ (fun y' => re₂ (f (ι₁ y'))) y ∧
      (∀ᶠ y' in 𝓝 y, ι₂ (re₂ (f (ι₁ y'))) = f (ι₁ y')) ∧
      ∀ h : V, fderiv ℝ (fun y' => re₂ (f (ι₁ y'))) y h = re₂ (fderiv ℂ f (ι₁ y) (ι₁ h)) := by
  refine ⟨analyticAt_comp_realLinear ι₁ re₂ hf, ?_, fun h => ?_⟩
  · filter_upwards [hreal] with y' ⟨w, hw⟩
    rw [hw, hre]
  · have hd : DifferentiableAt ℂ f (ι₁ y) := hf.differentiableAt
    have h1 : HasFDerivAt (fun y' => re₂ (f (ι₁ y')))
        (re₂.comp (((fderiv ℂ f (ι₁ y)).restrictScalars ℝ).comp ι₁)) y := by
      have := (re₂.hasFDerivAt (x := f (ι₁ y))).comp y
        (((hd.restrictScalars ℝ).hasFDerivAt).comp y (ι₁.hasFDerivAt (x := y)))
      rwa [hd.fderiv_restrictScalars ℝ] at this
    rw [h1.fderiv]
    rfl

end KAM.Wave
