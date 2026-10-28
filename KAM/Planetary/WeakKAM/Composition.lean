/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.WeakKAM.CompositionBound
public import KAM.Planetary.WeakKAM.SelectionRecord

/-! # P11B composition: the output record `SelectionComposition`

The finite compositions `X₀ ∘ ⋯ ∘ X_{ν-1}` with one common chosen chain (`bpP:p11a:composition`):
holomorphy, domain, derivative product recursion, angle/action/increment bounds, periodicity,
symplecticity and reality. `selectionComp_*` prove each field for an iteration at a schedule with
budget context; `composition` assembles the record from a parameter selection.
-/

@[expose] public noncomputable section
open Set Real MeasureTheory Filter Function
open scoped BigOperators Topology
namespace KAM.Planetary
open KAM KAM.Kepler
variable {n : ℕ}


/-- Finite compositions with one common chosen chain. -/
structure SelectionComposition (d : SelectionData n) (f : SelectionPhaseC n → ℂ)
    (a : SelectionSchedule n) extends SelectionOutput d f a where
  composition_holo : ∀ ν, DifferentiableOn ℂ
    (fun x : SelectionPoint n => selectionCompose toSelectionChain x.2 ν x.1)
    (selectionDomain (selectionr a ν) (selections a ν) (actionNbhd (K ν) (selectiont a ν)))
  composition_domain : ∀ ν, ∀ x ∈ selectionDomain (selectionr a ν) (selections a ν)
    (actionNbhd (K ν) (selectiont a ν)),
    (selectionCompose toSelectionChain x.2 ν x.1, x.2) ∈
      selectionDomain a.strip a.s₀ (actionNbhd d.K a.t₀)
  composition_derivative : ∀ ν, ∀ x ∈ selectionDomain (selectionr a ν) (selections a ν)
    (actionNbhd (K ν) (selectiont a ν)),
    ‖fderiv ℂ (selectionCompose toSelectionChain x.2 ν) x.1 -
      ContinuousLinearMap.id ℂ (SelectionPhaseC n)‖ ≤
      Real.exp (∑ j ∈ Finset.range ν, selectionMapBudget a j) - 1
  composition_small : ∀ ν, ∀ x ∈ selectionDomain (selectionr a ν) (selections a ν)
    (actionNbhd (K ν) (selectiont a ν)),
    ‖fderiv ℂ (selectionCompose toSelectionChain x.2 ν) x.1 -
      ContinuousLinearMap.id ℂ (SelectionPhaseC n)‖ ≤ (2 : ℝ)⁻¹ ^ 11
  composition_angle : ∀ ν, ∀ x ∈ selectionDomain (selectionr a ν) (selections a ν)
    (actionNbhd (K ν) (selectiont a ν)),
    ‖(selectionCompose toSelectionChain x.2 ν x.1).1 - x.1.1‖ ≤
      ∑ j ∈ Finset.range ν, selectionA a j
  composition_action : ∀ ν, ∀ x ∈ selectionDomain (selectionr a ν) (selections a ν)
    (actionNbhd (K ν) (selectiont a ν)),
    ‖(selectionCompose toSelectionChain x.2 ν x.1).2 - x.1.2‖ ≤
      ∑ j ∈ Finset.range ν, selectionAlpha a j
  composition_increment : ∀ ν, ∀ x ∈ selectionDomain (selectionr a (ν + 1))
    (selections a (ν + 1)) (actionNbhd (K (ν + 1)) (selectiont a (ν + 1))),
    ‖selectionCompose toSelectionChain x.2 (ν + 1) x.1 -
      selectionCompose toSelectionChain x.2 ν x.1‖ ≤
      (1 + (2 : ℝ)⁻¹ ^ 11) * max (selectionA a ν) (selectionAlpha a ν)

  composition_periodic : ∀ ν, ∀ x ∈ selectionDomain (selectionr a ν) (selections a ν)
    (actionNbhd (K ν) (selectiont a ν)), ∀ k : Fin n → ℤ,
    selectionCompose toSelectionChain x.2 ν (x.1 + ((fun i => (k i : ℂ)), 0)) =
      selectionCompose toSelectionChain x.2 ν x.1 + ((fun i => (k i : ℂ)), 0)
  composition_symplectic : ∀ ν, ∀ x ∈ selectionDomain (selectionr a ν) (selections a ν)
    (actionNbhd (K ν) (selectiont a ν)), ∀ u v : SelectionPhaseC n,
    Canonical.symplFormC (fderiv ℂ (selectionCompose toSelectionChain x.2 ν) x.1 u)
      (fderiv ℂ (selectionCompose toSelectionChain x.2 ν) x.1 v) = Canonical.symplFormC u v
  composition_real : ∀ ν, ∀ z : Phase n, ∀ b : SelectionR n,
    (phaseToC z, selectionReal b) ∈ selectionDomain (selectionr a ν) (selections a ν)
      (actionNbhd (K ν) (selectiont a ν)) →
    ∃ w : Phase n, selectionCompose toSelectionChain (selectionReal b) ν (phaseToC z) = phaseToC w

def sec_comp_data (c : SelectionChain n) (b : SelectionC n) := selectionCompose c b

section Qualitative
variable {d : SelectionData n} {f : SelectionPhaseC n → ℂ} {a : SelectionSchedule n}

theorem selectionComp_domain (cx : WeakBudgetCtx d a) (o : SelectionIteration d f a) (ν : ℕ) :
    ∀ x ∈ selectionCompDom a o.K ν,
    (selectionCompose o.toSelectionChain x.2 ν x.1, x.2) ∈
      selectionDomain a.strip a.s₀ (actionNbhd d.K a.t₀) := by
  induction ν with
  | zero =>
    rintro ⟨z, b⟩ hx
    have hr : selectionr a 0 = a.strip := by simp [selectionr]
    have hs : selections a 0 = a.s₀ := by simp [selections]
    have ht : selectiont a 0 = a.t₀ := by simp [selectiont]
    have h0 : selectionCompDom a o.K 0 = selectionDomain a.strip a.s₀ (actionNbhd d.K a.t₀) := by
      show selectionDomain (selectionr a 0) (selections a 0)
        (actionNbhd (o.K 0) (selectiont a 0)) = _
      rw [hr, hs, ht, (o.chain 0).initial]
    exact h0 ▸ hx
  | succ ν ih =>
    intro x hx
    exact ih _ (selectionComp_map_mem cx o ν hx)

theorem selectionComp_periodic (cx : WeakBudgetCtx d a) (o : SelectionIteration d f a) (ν : ℕ) :
    ∀ x ∈ selectionCompDom a o.K ν, ∀ k : Fin n → ℤ,
    selectionCompose o.toSelectionChain x.2 ν (x.1 + ((fun i => (k i : ℂ)), 0)) =
      selectionCompose o.toSelectionChain x.2 ν x.1 + ((fun i => (k i : ℂ)), 0) := by
  induction ν with
  | zero =>
    intro x _ k
    rfl
  | succ ν ih =>
    intro x hx k
    have h1 := o.map_periodic ν x hx k
    have h2 := ih _ (selectionComp_map_mem cx o ν hx) k
    simp only at h2
    show selectionCompose o.toSelectionChain x.2 ν (o.X ν x.2 (x.1 + _)) = _
    rw [h1]
    exact h2

theorem selectionComp_symplectic (cx : WeakBudgetCtx d a) (o : SelectionIteration d f a)
    (ν : ℕ) : ∀ x ∈ selectionCompDom a o.K ν, ∀ u v : SelectionPhaseC n,
    Canonical.symplFormC (fderiv ℂ (selectionCompose o.toSelectionChain x.2 ν) x.1 u)
      (fderiv ℂ (selectionCompose o.toSelectionChain x.2 ν) x.1 v) =
        Canonical.symplFormC u v := by
  induction ν with
  | zero =>
    intro x _ u v
    simp [selectionCompose]
  | succ ν ih =>
    rintro ⟨z, b⟩ hx u v
    rw [selectionComp_fderiv_succ cx o ν hx]
    simp only [ContinuousLinearMap.comp_apply]
    rw [ih _ (selectionComp_map_mem cx o ν hx)]
    exact o.map_symplectic ν (z, b) hx u v

theorem selectionComp_real (cx : WeakBudgetCtx d a) (o : SelectionIteration d f a) (ν : ℕ) :
    ∀ z : Phase n, ∀ b : SelectionR n,
    (phaseToC z, selectionReal b) ∈ selectionCompDom a o.K ν →
    ∃ w : Phase n, selectionCompose o.toSelectionChain (selectionReal b) ν (phaseToC z) =
      phaseToC w := by
  induction ν with
  | zero =>
    intro z b _
    exact ⟨z, rfl⟩
  | succ ν ih =>
    intro z b hx
    obtain ⟨w0, hw0⟩ := o.map_real ν z b hx
    have hy := selectionComp_map_mem cx o ν hx
    simp only at hy
    rw [hw0] at hy
    obtain ⟨w, hw⟩ := ih w0 b hy
    exact ⟨w, by rw [← hw, ← hw0]; rfl⟩

/-- Assemble the composition record from the parameter selection (source `composition`). -/
theorem selectionComposition_of_output (cx : WeakBudgetCtx d a) (o : SelectionOutput d f a) :
    Nonempty (SelectionComposition d f a) :=
  ⟨{ o with
     composition_holo := fun ν => selectionComp_holo cx o.toSelectionIteration ν
     composition_domain := fun ν => selectionComp_domain cx o.toSelectionIteration ν
     composition_derivative := fun ν => selectionComp_derivative cx o.toSelectionIteration ν
     composition_small := fun ν => selectionComp_small cx o.toSelectionIteration ν
     composition_angle := fun ν => selectionComp_angle cx o.toSelectionIteration ν
     composition_action := fun ν => selectionComp_action cx o.toSelectionIteration ν
     composition_increment := fun ν => selectionComp_increment cx o.toSelectionIteration ν
     composition_periodic := fun ν => selectionComp_periodic cx o.toSelectionIteration ν
     composition_symplectic := fun ν => selectionComp_symplectic cx o.toSelectionIteration ν
     composition_real := fun ν => selectionComp_real cx o.toSelectionIteration ν }⟩

end Qualitative

end KAM.Planetary

end
