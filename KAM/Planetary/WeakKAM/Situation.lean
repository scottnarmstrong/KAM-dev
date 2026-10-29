/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.WeakKAM.Evaluation

/-!
# The standing situation (S) of Part 11a-4 (GAP-E, `bpP:p11a:situation`)

`StandingSituation d f ε` is the literal standing situation (S): the selection data `d`
(with `γ = selectionGamma d`, i.e. `γ_*(ε*)/2`), `0 < ε ≤ ε_adm`, `|f| ≤ ε` (with the
perturbation's holomorphy, periodicity and reality), the adapted schedule (`T₀, t₀` of
`adm_params`, the radius `s₀(ε)` of `free_radius`, `ε₀ = 2 ε`) and the iteration of the
inductive lemma with `K_∞ ⊇ H_∞` and `ω_*` of the parameter selection (a `SelectionOutput`).
No conclusion (Diophantine property, tori, Lipschitz bound) is assumed. The signed
`situation` of `Evaluation` is untouched.
-/

@[expose] public noncomputable section
namespace KAM.Planetary

variable {n : ℕ}

/-- The standing situation (S), as data: the hypotheses of (S) and the iteration it takes. -/
structure StandingSituation (d : SelectionData n) (f : SelectionPhaseC n → ℂ) (ε : ℝ) where
  eps_pos : 0 < ε
  eps_le : ε ≤ selectionAdmissible d
  perturbation : SelectionPerturbation d f ε
  iteration : SelectionOutput d f (selectionAdapted d ε)

/-- The schedule of (S): `γ`, `T₀`, `t₀` of `adm_params`, `ε₀ = 2 ε` and the radius of
`free_radius`, with its scalar admissibility. -/
theorem standingSituation_schedule (d : SelectionData n) (ε : ℝ) (he : 0 < ε)
    (hsmall : ε ≤ selectionAdmissible d) :
    (selectionAdapted d ε).γ = selectionGamma d ∧
    (selectionAdapted d ε).T₀ = (adm_params d ε).T₀ ∧
    (selectionAdapted d ε).t₀ = (adm_params d ε).t₀ ∧
    (selectionAdapted d ε).ε₀ = 2 * ε ∧
    (selectionAdapted d ε).s₀ = Real.sqrt (2 * ε / (n * d.C₁)) ∧
    SelectionAdmissibility d (selectionAdapted d ε) ∧ 0 < (selectionAdapted d ε).s₀ :=
  ⟨rfl, rfl, rfl, rfl, rfl, (free_radius d ε he hsmall).1, (free_radius d ε he hsmall).2.1⟩

/-- The delivered selection output satisfies (S). -/
def standingSituation_of_selection {d : SelectionData n} {f : SelectionPhaseC n → ℂ} {ε : ℝ}
    (he : 0 < ε) (hsmall : ε ≤ selectionAdmissible d) (hf : SelectionPerturbation d f ε)
    (o : SelectionOutput d f (selectionAdapted d ε)) : StandingSituation d f ε :=
  ⟨he, hsmall, hf, o⟩

/-- The delivered evaluation output (hence the limit and displacement outputs) satisfies (S). -/
def standingSituation_of_evaluation {d : SelectionData n} {f : SelectionPhaseC n → ℂ} {ε : ℝ}
    (he : 0 < ε) (hsmall : ε ≤ selectionAdmissible d) (hf : SelectionPerturbation d f ε)
    (o : SelectionEvaluationOutput d f ε) : StandingSituation d f ε :=
  ⟨he, hsmall, hf, o.toSelectionOutput⟩

/-- (S) holds for every datum and perturbation with `0 < ε ≤ ε_adm`, `|f| ≤ ε`; its iteration
is the one delivered by `parameter_selection_adapted`, and the same situation carries the
evaluation output. -/
theorem standingSituation_exists (d : SelectionData n) (ε : ℝ) (he : 0 < ε)
    (hsmall : ε ≤ selectionAdmissible d) (f : SelectionPhaseC n → ℂ)
    (hf : SelectionPerturbation d f ε) :
    Nonempty (StandingSituation d f ε) ∧
      ∀ o : SelectionEvaluationOutput d f ε,
        (standingSituation_of_evaluation he hsmall hf o).iteration = o.toSelectionOutput := by
  refine ⟨?_, fun o => rfl⟩
  obtain ⟨o⟩ := parameter_selection_adapted d ε he hsmall f hf
  exact ⟨standingSituation_of_selection he hsmall hf o⟩

end KAM.Planetary

end
