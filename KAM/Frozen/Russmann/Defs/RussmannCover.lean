/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.Analysis.Complex.Basic
public import KAM.Frozen.Defs.IsDiophantine
public import KAM.Frozen.Defs.IsInvariantLagrangianTorus
public import KAM.Frozen.Defs.RealHamiltonian

/-!
# Frozen definition `KAM.Russmann.russmannCover`

Owner-approved on 2026-10-30 (R-HEAD with Q1(d), docs/tracks/R/RULINGS.md R1). This file is
frozen: it is hashed in `manifest/frozen-anchors.json`; any change needs an owner-approved
versioned successor. Source: Rus01 Thm 1.7, p. 126 (the invariant tori with Diophantine
frequencies `ω*(b)`, `b ∈ H`); ruling Q3 for the content of "invariant torus". This is
`KAM.kamCover` without the clause `frequencyMap h I₀ = ω`: under Rüssmann's weak non-degeneracy
the frequency of the torus near `θ ↦ (θ, I₀)` is shifted, so it is not tied to `∇h(I₀)`.
-/

@[expose] public noncomputable section

namespace KAM.Russmann

open KAM

/-- The points lying on the KAM tori of Rüssmann's theorem for `H = h + f`: invariant Lagrangian
tori (`IsInvariantLagrangianTorus`) with some `(γ, τ)`-Diophantine frequency `ω`, whose actions
stay within `r₀` of `B`, and which lie within `δ` of an unperturbed torus `θ ↦ (θ, I₀)` with
`I₀ ∈ B`. Unlike `KAM.kamCover`, the frequency `ω` is not required to equal `∇h(I₀)`. -/
def russmannCover {n : ℕ} (h : (Fin n → ℂ) → ℂ) (f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ)
    (B : Set (Fin n → ℝ)) (r₀ τ δ : ℝ) : Set ((Fin n → ℝ) × (Fin n → ℝ)) :=
  {z | ∃ (K : (Fin n → ℝ) → (Fin n → ℝ) × (Fin n → ℝ)) (ω : Fin n → ℝ) (γ : ℝ) (I₀ : Fin n → ℝ),
    0 < γ ∧ IsDiophantine γ τ ω ∧ IsInvariantLagrangianTorus (realHamiltonian h f) ω K ∧
    (∀ θ, ∃ J ∈ B, ‖(K θ).2 - J‖ < r₀) ∧
    I₀ ∈ B ∧ (∀ θ, ‖K θ - (θ, I₀)‖ ≤ δ) ∧ z ∈ Set.range K}

end KAM.Russmann

end
