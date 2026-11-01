/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Iteration.PrepStep
public import KAM.Wave.KamStep.StepOmegaBridge
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# W6: the normal frequency shift of the preparatory step with the weight `J`
(`bpW:w6:prep-step` (ii))

Off the frontier: source-faithful infrastructure used by several nodes. The dependency graph is
still being built. Blueprint label `bpW:w6:prep-step` (ii).

W6-ITER's `W6PrepHyp.shift_Omega` has the weight `J^{1/2} = (j+2)^{p_+-p}` of W5's clause (iii)
(deviation D2). Through W5's frequency bridge (`StepHypMod.core_OmegaPlus_eq`: the new normal
frequencies of the modified step are those of the `p+1` Taylor family `StepHypMod.R1`), the
blueprint's weight `J = (j+2)^{(p+1)-p}` holds (`StepHypMod.OmegaPlus_tail_bound_J`,
`StepHypMod.OmegaPlus_tail_lip_J`):

* `W6PrepHyp.shift_Omega_J`: `J (|Ω̂_{P,J}| + λ |Ω̂_{P,J}|^ℒ) ≤ 3ε` on `Π ∖ Ξ` (W7 index,
  `J = normLab n = n + 3`), as a sup bound `c₀` and a Lipschitz bound `c₁` with `c₀ + λ c₁ ≤ 3ε`.
-/

@[expose] public noncomputable section

open Real

namespace KAM.Wave

namespace W6PrepHyp

variable {m : ℝ} {hm : 0 < m} {Pi : Set (Fin 2 → ℝ)} {α r ε : ℝ}
  {P : (Fin 2 → ℝ) → KamPhase → ℂ} {X : (Fin 2 → ℝ) → KamPhase → KamPhase}

/-- **(ii), `Ω`, with the blueprint's weight `J`** (`bpW:w6:prep-step` (ii); W7 index,
`J = n + 3`): `J (|Ω̂_{P,J}| + λ |Ω̂_{P,J}|^ℒ) ≤ 3ε` on `Π ∖ Ξ`, `λ = α/M`. -/
theorem shift_Omega_J (H : W6PrepHyp m hm Pi α r ε P X) :
    ∃ c₀ c₁ : ℝ, 0 ≤ c₀ ∧ 0 ≤ c₁ ∧ c₀ + α / w6M m hm * c₁ ≤ 3 * ε ∧
      (∀ ξ ∈ Pi \ prepSet m hm Pi α, ∀ n : ℕ,
        normLab n * |w6Om7 (H.Om0 ξ) n - omegaNor m hm ξ n| ≤ c₀) ∧
      ∀ ξ ∈ Pi \ prepSet m hm Pi α, ∀ ζ ∈ Pi \ prepSet m hm Pi α, ∀ n : ℕ,
        normLab n * |(w6Om7 (H.Om0 ξ) n - omegaNor m hm ξ n) -
          (w6Om7 (H.Om0 ζ) n - omegaNor m hm ζ n)| ≤ c₁ * ‖ξ - ζ‖ := by
  have := H.factR
  set G := H.prepStepHyp
  obtain ⟨h0, h1, hs, -, -⟩ := G.split_spec
  have e : ((1 : ℝ) + 1 - 1) = 1 := by norm_num
  have hN : ∀ ξ n, omegaNor m hm ξ n = waveFreqNor m hm ξ n.succPNat := fun ξ n => by
    rw [waveFreqNor_eq_omegaNor, Nat.natPred_succPNat]
  have hJ : ∀ n : ℕ, normLab n = (((n.succPNat : ℕ+) : ℝ) + 2) ^ ((1 : ℝ) + 1 - 1) := fun n => by
    rw [e, Real.rpow_one, W6Stage.normLab_eq_succPNat]
  refine ⟨3 * stepE0 ε H.w6PrepE0, 3 * stepE1 H.w6PrepE0 H.w6PrepE1, by positivity,
    by positivity, by nlinarith, fun ξ hξ n => ?_, fun ξ hξ ζ hζ n => ?_⟩
  · rw [hN, hJ]
    exact G.hyp.OmegaPlus_tail_bound_J hξ n.succPNat
  · rw [hN, hN, hJ]
    have := G.hyp.OmegaPlus_tail_lip_J hξ hζ n.succPNat
    exact this.trans_eq (by ring)

end W6PrepHyp

end KAM.Wave
