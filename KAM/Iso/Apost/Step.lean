/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Iso.Apost.NewtonError
public import KAM.Iso.Apost.Torsion
import KAM.Iso.Apost.ConstantsArith
import Mathlib.Tactic.Linarith

/-!
# Part 2 (isoenergetic iteration): the isoenergetic KAM step

Blueprint node `bpI:p2:step`
(`KAM.Iso.Apost.step`). For an `IsoAdmissible` torus `K` (at the frequency `ω = s ω*`),
`0 < δ ≤ 1`, `4δ < r` and the step smallness `ĉ_step ε/(γ⁴ δ^{2a}) ≤ min {1, β}`, the Newton map
`K̄ = isoNewtonMap … (r - 2δ)` and the new frequency `ω̄ = s̄ ω*` (`s̄ = isoNewS …`) satisfy the
conclusions (a)-(e) of `bpI:p2:step` with `d = dStep`.

This is an assembly, mirroring `KAM.Apost.step`:

* `st-small`: `KAM.Iso.Apost.Arith.iso_step_small` turns the smallness hypothesis into
  `C_sym ε/(γ δ^{κ+1}) ≤ 1/2`, `d ≤ β/2` and `2𝔪 C_{Δ𝖳} d/δ² ≤ 1`; the frequency bound `γ ≤ Θ`
  is `IsoAdmissible.freq`.
* `st-error`: `correction` (the size of `ΔK` and of `s̄ω* - sω*`) and `newton_error` (the new error
  and the new energy error).
* `st-ball`, `st-perturb`: `torsion_step` (regularity, primary and real properties, the ball margin,
  the frame of `K̄` and the new averaged extended torsion).
-/

@[expose] public section

open scoped Matrix.Norms.Operator
open Matrix

namespace KAM.Iso.Apost

open KAM KAM.Torus KAM.Apost KAM.Iso.Linear

section Step

variable {n : ℕ} {τ M σK σB σT σω ν γ : ℝ} {ωstar : Fin n → ℝ}
  {D : Set ((Fin n → ℂ) × (Fin n → ℂ))} {H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}

/-- `bpI:p2:step` (a)–(e), `K̄ = isoNewtonMap … (r - 2δ)`, `s̄ = isoNewS …`, `d = dStep`. -/
theorem step (hS : IsoStanding n τ M σK σB σT σω ν ωstar D H γ) {E₀ r β ε δ s : ℝ}
    {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}
    (hK : IsoAdmissible σK σB σT D H ωstar E₀ r β ε s K) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (h4δ : 4 * δ < r)
    (hsmall : hatcStep n τ M σK σB σT * ε / (γ ^ 4 * δ ^ (2 * aExp n τ)) ≤ min 1 β) :
    (DifferentiableOn ℂ (isoNewtonMap H K ωstar E₀ s (r - 2 * δ)) (complexStrip n (r - 2 * δ)) ∧
      IsPrimaryOnStrip (isoNewtonMap H K ωstar E₀ s (r - 2 * δ)) (r - 2 * δ) ∧
      IsRealOnReals (isoNewtonMap H K ωstar E₀ s (r - 2 * δ))) ∧
    ((∀ θ ∈ complexStrip n (r - 2 * δ),
        ‖isoNewtonMap H K ωstar E₀ s (r - 2 * δ) θ - K θ‖ ≤ dStep n τ M σK σB σT γ ε δ) ∧
      dStep n τ M σK σB σT γ ε δ ≤ β / 2 ∧
      (∀ θ ∈ complexStrip n (r - 2 * δ), Metric.ball (isoNewtonMap H K ωstar E₀ s (r - 2 * δ) θ)
        (β - dStep n τ M σK σB σT γ ε δ) ⊆ D) ∧
      ‖isoNewS H K ωstar E₀ s • ωstar - s • ωstar‖ ≤ dStep n τ M σK σB σT γ ε δ) ∧
    ((∀ θ ∈ complexStrip n (r - 2 * δ),
        ‖invarianceError H (isoNewtonMap H K ωstar E₀ s (r - 2 * δ))
          (isoNewS H K ωstar E₀ s • ωstar) θ‖ ≤
          hatCE n τ M σK σB σT * ε ^ 2 / (γ ^ 4 * δ ^ (2 * aExp n τ))) ∧
      ‖KAM.Iso.energyAverage H (isoNewtonMap H K ωstar E₀ s (r - 2 * δ)) - (E₀ : ℂ)‖ ≤
        hatCE n τ M σK σB σT * ε ^ 2 / (γ ^ 4 * δ ^ (2 * aExp n τ))) ∧
    (∀ θ ∈ complexStrip n (r - 3 * δ),
      ‖fderiv ℂ (isoNewtonMap H K ωstar E₀ s (r - 2 * δ)) θ - fderiv ℂ K θ‖ ≤
        n * dStep n τ M σK σB σT γ ε δ / δ ∧
      IsUnit (gramMatrix (isoNewtonMap H K ωstar E₀ s (r - 2 * δ)) θ).det ∧
      ‖(gramMatrix (isoNewtonMap H K ωstar E₀ s (r - 2 * δ)) θ)⁻¹ - (gramMatrix K θ)⁻¹‖ ≤
        C_B n M σK σB σT * dStep n τ M σK σB σT γ ε δ / δ) ∧
    (IsUnit (KAM.Iso.extendedTorsionAverage H (isoNewtonMap H K ωstar E₀ s (r - 2 * δ))
        (isoNewS H K ωstar E₀ s • ωstar)).det ∧
      ‖(KAM.Iso.extendedTorsionAverage H (isoNewtonMap H K ωstar E₀ s (r - 2 * δ))
          (isoNewS H K ωstar E₀ s • ωstar))⁻¹ -
        (KAM.Iso.extendedTorsionAverage H K (s • ωstar))⁻¹‖ ≤
        2 * mSize M σK σB σT ^ 2 * CDTbord n M σK σB σT * dStep n τ M σK σB σT γ ε δ / δ ^ 2) := by
  have hP := hS.toParams
  have hγ := hS.gamma_pos
  have hr := hK.r_pos
  have hβ0 := hK.β_pos
  have h2δ : 2 * δ < r := by linarith
  -- step `st-small`
  obtain ⟨hγω, hω⟩ := hK.freq hS
  have hγΘ : γ ≤ Theta n M σK σB σT := hγω.trans hω
  obtain ⟨hs1, hs2, hs3⟩ := Arith.iso_step_small hP hγ hγΘ hδ hδ1 hK.ε_nonneg hsmall
  have hdβ : dStep n τ M σK σB σT γ ε δ < β := by linarith
  -- steps `st-error`, `st-ball`, `st-perturb`
  obtain ⟨-, -, -, -, hcd, hcs⟩ := correction hS hK hδ hδ1 h2δ
  obtain ⟨-, -, -, -, hE, hEn⟩ := newton_error hS hK hδ hδ1 h2δ hdβ hs1
  obtain ⟨⟨hdiff, hprim, hreal⟩, hball, hframe, -, -, htunit, htinv⟩ :=
    torsion_step hS hK hδ hδ1 h4δ hdβ hs3
  refine ⟨⟨hdiff, hprim, hreal⟩,
    ⟨fun θ hθ => ?_, hs2, hball, hcs⟩, ⟨hE, hEn⟩,
    fun θ hθ => ⟨(hframe θ hθ).1, (hframe θ hθ).2.2.1, (hframe θ hθ).2.2.2.2⟩, htunit, htinv⟩
  rw [TorsionAux.isoNewtonMap_of_mem hθ, add_sub_cancel_left]
  exact hcd θ hθ

end Step

end KAM.Iso.Apost
