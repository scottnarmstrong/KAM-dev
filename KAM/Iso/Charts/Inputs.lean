/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Frozen.Defs.ComplexStrip
public import KAM.Frozen.Defs.GramMatrix
public import KAM.Frozen.Defs.HamiltonianVectorFieldC
public import KAM.Frozen.Defs.InvarianceError
public import KAM.Frozen.Defs.IsDiophantine
public import KAM.Frozen.Defs.IsPrimaryOnStrip
public import KAM.Frozen.Defs.IsRealOnReals
public import KAM.Frozen.Iso.Defs.EnergyAverage
public import KAM.Frozen.Iso.Defs.ExtendedTorsionAverage
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# The frozen I-G1 and G3 as definitions (`bpI:p0:g1`, `K:bp:p0:g3`)

Definitions only. This module imports frozen definitions and Mathlib only; it imports
no frozen theorem and no provider.

* `KAM.Iso.Charts.IG1Body`: the body of the frozen `KAM.Iso.isoenergetic_kam` after
  `∃ C₁ C₂ C₃, 0 < C₁ ∧ 0 < C₂ ∧ 0 < C₃ ∧`, verbatim.
* `KAM.Iso.Charts.IG1Statement`: the type of the frozen `KAM.Iso.isoenergetic_kam` (I-G1), stated
  through `IG1Body`.
* `KAM.Iso.Charts.G3Statement`: the type of the frozen `KAM.volume_not_diophantine_le` (G3).

Part 3 consumes I-G1 and G3 as the premises `IG1Statement` and `G3Statement` (in `∀`
form, like the premise `GValid`); `Apost/G1` states `g1_explicit` through `IG1Body`. That these
are the frozen types is checked, outside the tree, by `rfl` against the anchors.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace KAM.Iso.Charts

open KAM

/-- The body of the frozen I-G1 after `∃ C₁ C₂ C₃, 0 < C₁ ∧ 0 < C₂ ∧ 0 < C₃ ∧`, verbatim. -/
def IG1Body (n : ℕ) (τ ρ ρinf M σK σB σT μ γbar σω ν : ℝ) (ωstar : Fin n → ℝ) (C₁ C₂ C₃ : ℝ) :
    Prop :=
  ∀ (D : Set ((Fin n → ℂ) × (Fin n → ℂ))) (H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ)
    (K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)) (s γ e E₀ : ℝ),
    IsOpen D → (∀ z ∈ D, ∀ k : Fin n → ℤ, (z.1 + (fun i => (k i : ℂ)), z.2) ∈ D) →
    DifferentiableOn ℂ H D → (∀ z ∈ D, ∀ k : Fin n → ℤ, H (z.1 + (fun i => (k i : ℂ)), z.2) = H z) →
    (∀ θ I : Fin n → ℝ, ((fun i => (θ i : ℂ)), (fun i => (I i : ℂ))) ∈ D →
      (H ((fun i => (θ i : ℂ)), (fun i => (I i : ℂ)))).im = 0) →
    (∀ z ∈ D, ‖fderiv ℂ H z‖ ≤ M ∧ ‖hamiltonianVectorFieldℂ H z‖ ≤ M ∧
      ‖fderiv ℂ (hamiltonianVectorFieldℂ H) z‖ ≤ M ∧
      ‖iteratedFDeriv ℂ 2 (hamiltonianVectorFieldℂ H) z‖ ≤ M ∧ ‖iteratedFDeriv ℂ 2 H z‖ ≤ M) →
    DifferentiableOn ℂ K (complexStrip n ρ) → IsPrimaryOnStrip K ρ → IsRealOnReals K →
    (∀ θ ∈ complexStrip n ρ, Metric.ball (K θ) μ ⊆ D) →
    (∀ θ ∈ complexStrip n ρ, ‖fderiv ℂ K θ‖ ≤ σK - μ) →
    (∀ θ ∈ complexStrip n ρ, IsUnit (gramMatrix K θ).det ∧
      ∀ i, ∑ j, ‖(gramMatrix K θ)⁻¹ i j‖ ≤ σB - μ) →
    IsUnit (KAM.Iso.extendedTorsionAverage H K (s • ωstar)).det →
    (∀ i, ∑ j, ‖(KAM.Iso.extendedTorsionAverage H K (s • ωstar))⁻¹ i j‖ ≤ σT - μ) →
    1 < s → s < σω → ν ≤ (s - 1) * ‖ωstar‖ → ν ≤ (σω - s) * ‖ωstar‖ →
    0 < γ → γ ≤ γbar → IsDiophantine γ τ ωstar → 0 ≤ e →
    (∀ θ ∈ complexStrip n ρ, ‖invarianceError H K (s • ωstar) θ‖ ≤ e) →
    ‖KAM.Iso.energyAverage H K - (E₀ : ℂ)‖ ≤ e →
    C₁ * e / (γ ^ 4 * ρ ^ (4 * τ)) < 1 →
    ∃ (Kinf : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)) (sinf : ℝ),
      1 < sinf ∧ sinf < σω ∧ DifferentiableOn ℂ Kinf (complexStrip n ρinf) ∧
      IsPrimaryOnStrip Kinf ρinf ∧ IsRealOnReals Kinf ∧
      (∀ θ ∈ complexStrip n ρinf, invarianceError H Kinf (sinf • ωstar) θ = 0) ∧
      (∀ θ ∈ complexStrip n ρinf, H (Kinf θ) = (E₀ : ℂ)) ∧
      (∀ θ ∈ complexStrip n ρinf, Metric.ball (Kinf θ) (μ / 2) ⊆ D) ∧
      (∀ θ ∈ complexStrip n ρinf, ‖fderiv ℂ Kinf θ‖ ≤ σK - μ / 2) ∧
      (∀ θ ∈ complexStrip n ρinf, ‖Kinf θ - K θ‖ ≤ C₂ * e / (γ ^ 2 * ρ ^ (2 * τ))) ∧
      ‖sinf • ωstar - s • ωstar‖ ≤ C₃ * e / (γ ^ 2 * ρ ^ (2 * τ))

/-- The type of the frozen `KAM.Iso.isoenergetic_kam` (I-G1). -/
def IG1Statement : Prop :=
  ∀ {n : ℕ}, 2 ≤ n → ∀ {τ : ℝ}, (n : ℝ) - 1 ≤ τ → ∀ {ρ ρinf : ℝ}, 0 < ρinf → ρinf < ρ →
    ∀ {M σK σB σT μ γbar σω ν : ℝ}, 0 < M → 0 < σK → 0 < σB → 0 < σT → 0 < μ → 0 < γbar →
    1 < σω → 0 < ν → ∀ ωstar : Fin n → ℝ, ωstar ≠ 0 →
    ∃ C₁ C₂ C₃ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ 0 < C₃ ∧
      IG1Body n τ ρ ρinf M σK σB σT μ γbar σω ν ωstar C₁ C₂ C₃

/-- The type of the frozen `KAM.volume_not_diophantine_le` (G3). -/
def G3Statement : Prop :=
  ∀ {n : ℕ} {τ : ℝ}, (n : ℝ) - 1 < τ → ∀ {Ω : Set (Fin n → ℝ)}, Bornology.IsBounded Ω →
    ∃ C : ℝ, ∀ α : ℝ, 0 < α → volume {ω ∈ Ω | ¬ IsDiophantine α τ ω} ≤ ENNReal.ofReal (C * α)

end KAM.Iso.Charts

end
