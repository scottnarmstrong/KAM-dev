/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.WeakKAM.IterationAux
public import KAM.Planetary.WeakKAM.Initial

/-! # P11B iteration: the base case `(P₀)`

`stepP:p11a:il-p0`: the chain of length zero (`K₀ = K`, no increments) with the initial
remainder `R₀` of `initial`.
-/

@[expose] public noncomputable section
open Set Real MeasureTheory Filter Function
open scoped BigOperators Topology
namespace KAM.Planetary
open KAM KAM.Kepler
variable {n : ℕ}

/-- The chain of length zero: `K_j = K`, trivial increments and maps, `R = R₀` of `initial`. -/
def selectionBaseChain (d : SelectionData n) (f : SelectionPhaseC n → ℂ) : SelectionChain n where
  K := fun _ => d.K
  Δω := fun _ _ => 0
  Δh := fun _ _ => 0
  X := fun _ _ z => z
  R := fun _ x => selectionInitial d f x - ∑ i, fderiv ℂ d.h x.2 (Pi.single i 1) * x.1.2 i

theorem selectionr_zero (a : SelectionSchedule n) : selectionr a 0 = a.strip := by
  simp [selectionr]

theorem selections_zero (a : SelectionSchedule n) : selections a 0 = a.s₀ := by
  simp [selections]

theorem selectiont_zero (a : SelectionSchedule n) : selectiont a 0 = a.t₀ := by
  simp [selectiont]

theorem selectionε_zero (a : SelectionSchedule n) : selectionε a 0 = a.ε₀ := by
  simp [selectionε]

theorem iterPre_base {d : SelectionData n} {a : SelectionSchedule n} (c : WeakBudgetCtx d a)
    (f : SelectionPhaseC n → ℂ) {ε : ℝ} (hf : SelectionPerturbation d f ε)
    (hε₀ : ε + n / 2 * d.C₁ * a.s₀ ^ 2 ≤ a.ε₀) :
    IterPre d f a (selectionBaseChain d f) 0 := by
  have h := c.hyp
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast h.hn
  have hsq : 1 ≤ Real.sqrt n := by simpa using Real.sqrt_le_sqrt hn
  have hθ := d.theta_pos
  have ht : a.t₀ ≤ d.ϑ := c.adm.t_le.trans (div_le_self hθ.le hsq)
  have hs : a.s₀ ≤ d.ϑ := by
    have h2 : a.t₀ / (8 * n) ≤ a.t₀ := div_le_self h.ht.le (by linarith)
    linarith [c.adm.radius]
  obtain ⟨i1, i2, i3, i4⟩ := initial d f ε a.t₀ a.s₀ hf h.ht ht h.hs hs
  have hch : SelectionFiniteChain d a (selectionBaseChain d f) 0 := by
    refine ⟨⟨rfl, fun j _ => d.compact, fun j _ => ?_, fun j hj => by omega,
      fun j hj => by omega, fun j hj => by omega, fun j hj => by omega⟩,
      fun j hj => by omega⟩
    exact nonempty_of_measure_ne_zero d.positive_measure.ne'
  have hdom : selectionDomain (selectionr a 0) (selections a 0)
      (actionNbhd ((selectionBaseChain d f).K 0) (selectiont a 0)) =
      selectionDomain d.strip a.s₀ (actionNbhd d.K a.t₀) := by
    rw [selectionr_zero, selections_zero, selectiont_zero, c.hstrip]
    rfl
  have hE : selectionEnergy (selectionBaseChain d f) 0 = fun _ => 0 := by
    funext b; simp [selectionEnergy]
  refine ⟨hch, ?_, selection_frequency_derivative_le c hch.toSelectionExtensionChain, ?_, ?_,
    ?_, ?_, ?_⟩
  · rw [hE]; exact differentiableOn_const _
  · rw [hdom]; exact i1
  · rw [hdom]
    intro x hx
    refine (i2 x hx).trans ?_
    rw [selectionε_zero]
    exact hε₀
  · rw [hdom]
    intro x hx k
    have := i3 x hx k
    simp only [selectionBaseChain]
    rw [this]
  · rw [hdom]
    intro z b hz
    have hb : selectionReal b ∈ actionNbhd d.K a.t₀ := hz.2.2
    have hV : selectionReal b ∈ actionNbhd d.K (2 * d.ϑ) :=
      selectionCollar_mono (subset_refl _) (by linarith) hb
    simp only [selectionBaseChain, Complex.sub_im, Complex.im_sum]
    rw [i4 z b hz, zero_sub, neg_eq_zero]
    refine Finset.sum_eq_zero fun i _ => ?_
    simp [Complex.mul_im, selection_gradient_real d hV i, phaseToC]
  · intro x hx
    simp [selectionCompose, selectionEnergy, selectionFrequency, selectionBaseChain]

end KAM.Planetary

end
