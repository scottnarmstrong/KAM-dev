/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.WeakKAM.IterationFacts

/-! # P11B iteration: stage predicates and coherent prefixes

`IterPre` collects the fields of `SelectionIteration` about the index `ν` itself (chain,
remainder, normal form); `IterPost` collects those about the step `ν → ν + 1`. `IterPrefix ν c`
says both hold up to `ν`. `ChainAgree` records that a chain extension does not change the
data a prefix reads, so the predicates transfer along a coherent sequence of chains.
-/

@[expose] public noncomputable section
open Set Real MeasureTheory Filter Function
open scoped BigOperators Topology
namespace KAM.Planetary
open KAM KAM.Kepler
variable {n : ℕ}

/-- The fields of `SelectionIteration` at the index `ν`. -/
structure IterPre (d : SelectionData n) (f : SelectionPhaseC n → ℂ) (a : SelectionSchedule n)
    (c : SelectionChain n) (ν : ℕ) : Prop where
  chain : SelectionFiniteChain d a c ν
  energy_holo : DifferentiableOn ℂ (selectionEnergy c ν)
    (actionNbhd (c.K ν) (selectiont a ν))
  frequency_derivative : ∀ b ∈ actionNbhd (c.K ν) (selectiont a ν),
    ‖fderiv ℂ (selectionFrequency d c ν) b‖ ≤ 2 * d.C₁
  remainder_holo : DifferentiableOn ℂ (c.R ν)
    (selectionDomain (selectionr a ν) (selections a ν) (actionNbhd (c.K ν) (selectiont a ν)))
  remainder_bound : ∀ x ∈ selectionDomain (selectionr a ν) (selections a ν)
    (actionNbhd (c.K ν) (selectiont a ν)), ‖c.R ν x‖ ≤ selectionε a ν
  remainder_periodic : ∀ x ∈ selectionDomain (selectionr a ν) (selections a ν)
    (actionNbhd (c.K ν) (selectiont a ν)), ∀ k : Fin n → ℤ,
    c.R ν ((x.1.1 + (fun i => (k i : ℂ)), x.1.2), x.2) = c.R ν x
  remainder_real : ∀ z : Phase n, ∀ b : SelectionR n,
    (phaseToC z, selectionReal b) ∈ selectionDomain (selectionr a ν) (selections a ν)
      (actionNbhd (c.K ν) (selectiont a ν)) → (c.R ν (phaseToC z, selectionReal b)).im = 0
  normal_form : ∀ x ∈ selectionDomain (selectionr a ν) (selections a ν)
    (actionNbhd (c.K ν) (selectiont a ν)),
    selectionInitial d f (selectionCompose c x.2 ν x.1, x.2) =
      selectionEnergy c ν x.2 +
        (∑ i, selectionFrequency d c ν x.2 i * x.1.2 i) + c.R ν x

/-- The fields of `SelectionIteration` describing the step `ν → ν + 1`. -/
structure IterPost (d : SelectionData n) (a : SelectionSchedule n)
    (c : SelectionChain n) (ν : ℕ) : Prop where
  increment_holo : DifferentiableOn ℂ (c.Δh ν) (actionNbhd (c.K ν) (selectiont a ν))
  increment_real : ∀ b : SelectionR n,
    selectionReal b ∈ actionNbhd (c.K ν) (selectiont a ν) → (c.Δh ν (selectionReal b)).im = 0
  energy_bound : ∀ b ∈ actionNbhd (c.K ν) (selectiont a ν), ‖c.Δh ν b‖ ≤ 2 * selectionε a ν
  map_holo : DifferentiableOn ℂ (fun x : SelectionPoint n => c.X ν x.2 x.1)
    (selectionDomain (selectionr a (ν + 1)) (selections a (ν + 1))
      (actionNbhd (c.K (ν + 1)) (selectiont a (ν + 1))))
  map_domain : ∀ x ∈ selectionDomain (selectionr a (ν + 1)) (selections a (ν + 1))
    (actionNbhd (c.K (ν + 1)) (selectiont a (ν + 1))),
    (c.X ν x.2 x.1, x.2) ∈ selectionDomain (selectionr a (ν + 1) + selectionσ a ν)
      (selections a ν) (actionNbhd (c.K (ν + 1)) (selectiont a (ν + 1)))
  map_periodic : ∀ x ∈ selectionDomain (selectionr a (ν + 1)) (selections a (ν + 1))
    (actionNbhd (c.K (ν + 1)) (selectiont a (ν + 1))), ∀ k : Fin n → ℤ,
    c.X ν x.2 (x.1 + ((fun i => (k i : ℂ)), 0)) = c.X ν x.2 x.1 + ((fun i => (k i : ℂ)), 0)
  map_real : ∀ z : Phase n, ∀ b : SelectionR n,
    (phaseToC z, selectionReal b) ∈ selectionDomain (selectionr a (ν + 1))
      (selections a (ν + 1)) (actionNbhd (c.K (ν + 1)) (selectiont a (ν + 1))) →
    ∃ w : Phase n, c.X ν (selectionReal b) (phaseToC z) = phaseToC w
  map_symplectic : ∀ x ∈ selectionDomain (selectionr a (ν + 1))
    (selections a (ν + 1)) (actionNbhd (c.K (ν + 1)) (selectiont a (ν + 1))),
    ∀ u v : SelectionPhaseC n,
    Canonical.symplFormC (fderiv ℂ (c.X ν x.2) x.1 u) (fderiv ℂ (c.X ν x.2) x.1 v) =
      Canonical.symplFormC u v
  map_angle_bound : ∀ x ∈ selectionDomain (selectionr a (ν + 1))
    (selections a (ν + 1)) (actionNbhd (c.K (ν + 1)) (selectiont a (ν + 1))),
    ‖(c.X ν x.2 x.1).1 - x.1.1‖ ≤ selectionA a ν
  map_action_bound : ∀ x ∈ selectionDomain (selectionr a (ν + 1))
    (selections a (ν + 1)) (actionNbhd (c.K (ν + 1)) (selectiont a (ν + 1))),
    ‖(c.X ν x.2 x.1).2 - x.1.2‖ ≤ selectionAlpha a ν
  map_derivative_bound : ∀ x ∈ selectionDomain (selectionr a (ν + 1))
    (selections a (ν + 1)) (actionNbhd (c.K (ν + 1)) (selectiont a (ν + 1))),
    ‖fderiv ℂ (c.X ν x.2) x.1 - ContinuousLinearMap.id ℂ (SelectionPhaseC n)‖
      ≤ selectionMapBudget a ν
  map_parameter_bound : ∀ t' : ℝ, 0 < t' → t' < selectiont a (ν + 1) →
    ∀ z : SelectionPhaseC n, z.1 ∈ complexStrip n (selectionr a (ν + 1)) →
    ‖z.2‖ < selections a (ν + 1) → ∀ b ∈ actionNbhd (c.K (ν + 1)) t', ∀ j : ℕ,
    ‖iteratedFDeriv ℂ j (fun b' => c.X ν b' z - z) b‖ ≤
      (j : ℝ) ^ j * max (selectionA a ν) (selectionAlpha a ν) /
        (selectiont a (ν + 1) - t') ^ j
  map_affine : ∀ b ∈ actionNbhd (c.K (ν + 1)) (selectiont a (ν + 1)),
    ∃ Θ : SelectionC n → SelectionC n,
    ∃ A : SelectionC n → (SelectionC n →L[ℂ] SelectionC n),
    ∃ v : SelectionC n → SelectionC n,
    ∀ z : SelectionPhaseC n, z.1 ∈ complexStrip n (selectionr a (ν + 1)) →
      ‖z.2‖ < selections a (ν + 1) → c.X ν b z = (Θ z.1, A z.1 z.2 + v z.1)
  map_injective : ∀ b ∈ actionNbhd (c.K (ν + 1)) (selectiont a (ν + 1)),
    InjOn (c.X ν b) {z | z.1 ∈ complexStrip n (selectionr a (ν + 1)) ∧
      ‖z.2‖ < selections a (ν + 1)}
  real_angle_derivative : ∀ b : SelectionR n,
    selectionReal b ∈ actionNbhd (c.K (ν + 1)) (selectiont a (ν + 1)) → ∀ θ,
    ‖fderiv ℝ (fun v : SelectionR n =>
        selectionRe ((c.X ν (selectionReal b) (selectionReal v, 0)).1)) θ -
      ContinuousLinearMap.id ℝ (SelectionR n)‖ ≤ Real.exp (selectionRealBudget a ν) - 1

/-- A finite coherent prefix of an iteration. -/
def IterPrefix (d : SelectionData n) (f : SelectionPhaseC n → ℂ) (a : SelectionSchedule n)
    (c : SelectionChain n) (ν : ℕ) : Prop :=
  ∀ j ≤ ν, IterPre d f a c j ∧ (j < ν → IterPost d a c j)

end KAM.Planetary

end
