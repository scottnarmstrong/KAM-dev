/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.WeakKAM.Budgets

/-! # P11B iteration: the output record `SelectionIteration`

The exact normal-form and simple-map outputs of the inductive lemma (signature record); never an
assumption of a source export.
-/

@[expose] public noncomputable section
open Set Real MeasureTheory Filter Function
open scoped BigOperators Topology
namespace KAM.Planetary
open KAM KAM.Kepler
variable {n : ℕ}

/-- Exact normal-form and simple-map outputs; never an assumption of a source export. -/
structure SelectionIteration (d : SelectionData n) (f : SelectionPhaseC n → ℂ)
    (a : SelectionSchedule n) extends SelectionChain n where
  chain : ∀ ν, SelectionFiniteChain d a toSelectionChain ν
  energy_holo : ∀ ν, DifferentiableOn ℂ (selectionEnergy toSelectionChain ν)
    (actionNbhd (K ν) (selectiont a ν))
  increment_holo : ∀ ν, DifferentiableOn ℂ (Δh ν) (actionNbhd (K ν) (selectiont a ν))
  increment_real : ∀ ν, ∀ b : SelectionR n,
    selectionReal b ∈ actionNbhd (K ν) (selectiont a ν) → (Δh ν (selectionReal b)).im = 0
  energy_bound : ∀ ν, ∀ b ∈ actionNbhd (K ν) (selectiont a ν), ‖Δh ν b‖ ≤ 2 * selectionε a ν
  frequency_derivative : ∀ ν, ∀ b ∈ actionNbhd (K ν) (selectiont a ν),
    ‖fderiv ℂ (selectionFrequency d toSelectionChain ν) b‖ ≤ 2 * d.C₁
  remainder_holo : ∀ ν, DifferentiableOn ℂ (R ν)
    (selectionDomain (selectionr a ν) (selections a ν) (actionNbhd (K ν) (selectiont a ν)))
  remainder_bound : ∀ ν, ∀ x ∈ selectionDomain (selectionr a ν) (selections a ν)
    (actionNbhd (K ν) (selectiont a ν)), ‖R ν x‖ ≤ selectionε a ν
  remainder_periodic : ∀ ν, ∀ x ∈ selectionDomain (selectionr a ν) (selections a ν)
    (actionNbhd (K ν) (selectiont a ν)), ∀ k : Fin n → ℤ,
    R ν ((x.1.1 + (fun i => (k i : ℂ)), x.1.2), x.2) = R ν x
  remainder_real : ∀ ν, ∀ z : Phase n, ∀ b : SelectionR n,
    (phaseToC z, selectionReal b) ∈ selectionDomain (selectionr a ν) (selections a ν)
      (actionNbhd (K ν) (selectiont a ν)) → (R ν (phaseToC z, selectionReal b)).im = 0
  normal_form : ∀ ν, ∀ x ∈ selectionDomain (selectionr a ν) (selections a ν)
    (actionNbhd (K ν) (selectiont a ν)),
    selectionInitial d f (selectionCompose toSelectionChain x.2 ν x.1, x.2) =
      selectionEnergy toSelectionChain ν x.2 +
        (∑ i, selectionFrequency d toSelectionChain ν x.2 i * x.1.2 i) + R ν x
  map_holo : ∀ ν, DifferentiableOn ℂ (fun x : SelectionPoint n => X ν x.2 x.1)
    (selectionDomain (selectionr a (ν + 1)) (selections a (ν + 1))
      (actionNbhd (K (ν + 1)) (selectiont a (ν + 1))))
  map_domain : ∀ ν, ∀ x ∈ selectionDomain (selectionr a (ν + 1)) (selections a (ν + 1))
    (actionNbhd (K (ν + 1)) (selectiont a (ν + 1))),
    (X ν x.2 x.1, x.2) ∈ selectionDomain (selectionr a (ν + 1) + selectionσ a ν)
      (selections a ν) (actionNbhd (K (ν + 1)) (selectiont a (ν + 1)))
  map_periodic : ∀ ν, ∀ x ∈ selectionDomain (selectionr a (ν + 1)) (selections a (ν + 1))
    (actionNbhd (K (ν + 1)) (selectiont a (ν + 1))), ∀ k : Fin n → ℤ,
    X ν x.2 (x.1 + ((fun i => (k i : ℂ)), 0)) = X ν x.2 x.1 + ((fun i => (k i : ℂ)), 0)
  map_real : ∀ ν, ∀ z : Phase n, ∀ b : SelectionR n,
    (phaseToC z, selectionReal b) ∈ selectionDomain (selectionr a (ν + 1))
      (selections a (ν + 1)) (actionNbhd (K (ν + 1)) (selectiont a (ν + 1))) →
    ∃ w : Phase n, X ν (selectionReal b) (phaseToC z) = phaseToC w
  map_symplectic : ∀ ν, ∀ x ∈ selectionDomain (selectionr a (ν + 1))
    (selections a (ν + 1)) (actionNbhd (K (ν + 1)) (selectiont a (ν + 1))),
    ∀ u v : SelectionPhaseC n,
    Canonical.symplFormC (fderiv ℂ (X ν x.2) x.1 u) (fderiv ℂ (X ν x.2) x.1 v) =
      Canonical.symplFormC u v

  map_angle_bound : ∀ ν, ∀ x ∈ selectionDomain (selectionr a (ν + 1))
    (selections a (ν + 1)) (actionNbhd (K (ν + 1)) (selectiont a (ν + 1))),
    ‖(X ν x.2 x.1).1 - x.1.1‖ ≤ selectionA a ν
  map_action_bound : ∀ ν, ∀ x ∈ selectionDomain (selectionr a (ν + 1))
    (selections a (ν + 1)) (actionNbhd (K (ν + 1)) (selectiont a (ν + 1))),
    ‖(X ν x.2 x.1).2 - x.1.2‖ ≤ selectionAlpha a ν
  map_derivative_bound : ∀ ν, ∀ x ∈ selectionDomain (selectionr a (ν + 1))
    (selections a (ν + 1)) (actionNbhd (K (ν + 1)) (selectiont a (ν + 1))),
    ‖fderiv ℂ (X ν x.2) x.1 - ContinuousLinearMap.id ℂ (SelectionPhaseC n)‖
      ≤ selectionMapBudget a ν
  map_parameter_bound : ∀ ν, ∀ t' : ℝ, 0 < t' → t' < selectiont a (ν + 1) →
    ∀ z : SelectionPhaseC n, z.1 ∈ complexStrip n (selectionr a (ν + 1)) →
    ‖z.2‖ < selections a (ν + 1) → ∀ b ∈ actionNbhd (K (ν + 1)) t', ∀ j : ℕ,
    ‖iteratedFDeriv ℂ j (fun c => X ν c z - z) b‖ ≤
      (j : ℝ) ^ j * max (selectionA a ν) (selectionAlpha a ν) /
        (selectiont a (ν + 1) - t') ^ j

  map_affine : ∀ ν, ∀ b ∈ actionNbhd (K (ν + 1)) (selectiont a (ν + 1)),
    ∃ Θ : SelectionC n → SelectionC n,
    ∃ A : SelectionC n → (SelectionC n →L[ℂ] SelectionC n),
    ∃ v : SelectionC n → SelectionC n,
    ∀ z : SelectionPhaseC n, z.1 ∈ complexStrip n (selectionr a (ν + 1)) →
      ‖z.2‖ < selections a (ν + 1) → X ν b z = (Θ z.1, A z.1 z.2 + v z.1)
  map_injective : ∀ ν, ∀ b ∈ actionNbhd (K (ν + 1)) (selectiont a (ν + 1)),
    InjOn (X ν b) {z | z.1 ∈ complexStrip n (selectionr a (ν + 1)) ∧
      ‖z.2‖ < selections a (ν + 1)}
  /-- Requires the B10 real-collar supplier; canonical_step_real on S.E alone is insufficient. -/
  real_angle_derivative : ∀ ν, ∀ b : SelectionR n,
    selectionReal b ∈ actionNbhd (K (ν + 1)) (selectiont a (ν + 1)) → ∀ θ,
    ‖fderiv ℝ (fun v : SelectionR n =>
        selectionRe ((X ν (selectionReal b) (selectionReal v, 0)).1)) θ -
      ContinuousLinearMap.id ℝ (SelectionR n)‖ ≤ Real.exp (selectionRealBudget a ν) - 1

end KAM.Planetary

end
