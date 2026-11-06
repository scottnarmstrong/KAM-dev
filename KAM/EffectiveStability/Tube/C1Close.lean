/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Module.Basic

/-!
# `C¹` closeness of functions on the angle plane (T2-CONF interface)

The shared interface of the SJSU gate-2 tube checker (program T2-CONF, D74;
`docs/explorations/sjsu-g2-gates.md`). Models of functions of the two reduced angles
`φ = (q₁ - q₃, q₂ - q₃)` (2π-periodic functions on `Fin 2 → ℝ`) are compared with their approximants
(finite trigonometric polynomials) in the `C¹` sup sense: values and both partial derivatives.

* `C1Close f g e₀ e₁`: `f` and `g` are differentiable, `|f - g| ≤ e₀` everywhere, and every partial
  derivative of `f - g` is bounded by `e₁` everywhere.
-/

@[expose] public section

namespace KAM.EffectiveStability.Tube

/-- `f` is `C¹`-close to `g`: both are differentiable on `Fin 2 → ℝ`, `|f φ - g φ| ≤ e₀` for every
`φ`, and `|∂_a f φ - ∂_a g φ| ≤ e₁` for every `φ` and both directions `a`. -/
def C1Close (f g : (Fin 2 → ℝ) → ℝ) (e₀ e₁ : ℝ) : Prop :=
  Differentiable ℝ f ∧ Differentiable ℝ g ∧ (∀ φ, |f φ - g φ| ≤ e₀) ∧
    ∀ φ (a : Fin 2), |fderiv ℝ f φ (Pi.single a 1) - fderiv ℝ g φ (Pi.single a 1)| ≤ e₁

end KAM.EffectiveStability.Tube

end
