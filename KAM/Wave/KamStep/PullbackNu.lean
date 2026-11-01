/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.KamStep.StepPlus
public import KAM.Wave.KamStep.PullbackAbstract
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The operator `N_t` at the small scale (blueprint-W `bpW:w5:pullback` step `p-inv`)

Off-frontier, source-faithful infrastructure (W5-STEP); the dependency graph is still being built.

`stepNu ρ y = |y|_ρ`. For the flow of `ι Z` and `w ∈ D(s-3σ, r/4)`:
`ν_{ηr}(N_t(w) y) ≤ (8M/(σ η²)) ν_{ηr}(y)` and, for two fields with `|Z - Z'| ≤ N₁`,
`ν_{ηr}((N_t - N'_t) y) ≤ (16 N₁/(σ η²)) ν_{ηr}(y)`.
-/

@[expose] public noncomputable section

open Set Metric

namespace KAM.Wave

open KAM

/-- The norm `|·|_ρ` as a function on `StepPhase r`. -/
def stepNu (ρ : ℝ) {r : ℝ} (y : StepPhase r) : ℝ := kamNorm ρ (StepPhase.toK y)

theorem stepNu_add {ρ r : ℝ} (hρ : 0 < ρ) (x y : StepPhase r) :
    stepNu ρ (x + y) ≤ stepNu ρ x + stepNu ρ y := kamNorm_add_le hρ _ _

theorem stepNu_neg {ρ r : ℝ} (x : StepPhase r) : stepNu ρ (-x) = stepNu ρ x := kamNorm_neg _

theorem stepNu_nonneg {ρ r : ℝ} (hρ : 0 < ρ) (x : StepPhase r) : 0 ≤ stepNu ρ x :=
  kamNorm_nonneg hρ.le _

variable {a p pb s r σ η M : ℝ} [Fact (0 < r)]

/-- `|·|_r ≤ |·|_{ηr}` and `|·|_{ηr} ≤ η⁻² |·|_r`. -/
theorem stepNu_mono {y : StepPhase r} (hη0 : 0 < η) (hη1 : η ≤ 1) :
    ‖y‖ ≤ stepNu (η * r) y ∧ stepNu (η * r) y ≤ η⁻¹ ^ 2 * ‖y‖ := by
  have hr : 0 < r := Fact.out
  refine ⟨?_, ?_⟩
  · exact kamNorm_le_of_le_radius (by positivity) (by nlinarith) _
  · have := kamNorm_le_ratio_sq (r₁ := η * r) (r₂ := r) (by positivity) (by nlinarith)
      (StepPhase.toK y)
    have e : (r / (η * r)) ^ 2 = η⁻¹ ^ 2 := by field_simp
    rw [e] at this
    exact this

end KAM.Wave
