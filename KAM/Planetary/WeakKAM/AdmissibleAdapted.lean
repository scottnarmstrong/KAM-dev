/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.WeakKAM.Admissible

/-! # P11B weak-KAM admissible parameters: A7 at the adapted radius

`stepP:p11a:fr-list`: the initial-remainder inequality A7 for the radius adapted to `ε`,
the companion of `adm_choice_initial` (fixed schedule) and of `free_radius` (A1--A6).
-/

@[expose] public noncomputable section
open Set Real MeasureTheory Filter Function
open scoped BigOperators Topology
namespace KAM.Planetary
open KAM KAM.Kepler
variable {n : ℕ}

/-- `stepP:p11a:fr-list` (A7 at the adapted radius): for `selectionAdapted d ε` the initial
remainder is bounded by `ε₀ = ε + n C₁ s₀² / 2` on the initial domain, in the form
`adm_choice_initial` states it for the fixed schedule. Proved by applying `initial` as
`iterPre_base` does. -/
theorem adm_choice_initial_adapted (d : SelectionData n) (f : SelectionPhaseC n → ℂ) (ε : ℝ)
    (hf : SelectionPerturbation d f ε) (he : 0 < ε) (hsmall : ε ≤ selectionAdmissible d) :
    (selectionAdapted d ε).ε₀ = ε + n / 2 * d.C₁ * (selectionAdapted d ε).s₀ ^ 2 ∧
    ∀ x ∈ selectionDomain d.strip (selectionAdapted d ε).s₀
        (actionNbhd d.K (selectionAdapted d ε).t₀),
      ‖selectionInitial d f x - ∑ i, fderiv ℂ d.h x.2 (Pi.single i 1) * x.1.2 i‖
        ≤ (selectionAdapted d ε).ε₀ := by
  obtain ⟨hA, hs, -, hε, -, -⟩ := free_radius d ε he hsmall
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast d.n_pos
  have hθ := d.theta_pos
  have hsq : 1 ≤ Real.sqrt n := by simpa using Real.sqrt_le_sqrt hn
  have ht : (selectionAdapted d ε).t₀ ≤ d.ϑ := hA.t_le.trans (div_le_self hθ.le hsq)
  have hs' : (selectionAdapted d ε).s₀ ≤ d.ϑ := by
    have h1 := hA.radius
    have h2 : (selectionAdapted d ε).t₀ / (8 * n) ≤ (selectionAdapted d ε).t₀ :=
      div_le_self hA.t_pos.le (by linarith)
    linarith
  refine ⟨hε, fun x hx => ?_⟩
  exact ((initial d f ε _ _ hf hA.t_pos ht hs hs').2.1 x hx).trans hε.ge

end KAM.Planetary
