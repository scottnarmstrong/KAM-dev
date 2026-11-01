/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.KamStep.StepPlus
public import KAM.Wave.KamStep.PullbackAbstract
public import KAM.Wave.KamStep.FlowStepBounds
public import KAM.Wave.KamStep.NewHamTransport
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

section N

variable {ι : StepPhase r →L[ℂ] StepPhase r} {Z Z' : StepPhase r → StepPhase r}
  {V U : Set (StepPhase r)} {δ : ℝ}

theorem stepNu_transNop_le (hη0 : 0 < η) (hη1 : η ≤ 1) (hι : ∀ g, ‖ι g‖ ≤ ‖g‖)
    (h : FlowHyp (smoothField ι Z) V U M δ) (hZ : DifferentiableOn ℂ Z V)
    (hb : ∀ z ∈ V, ‖Z z‖ ≤ M) {w : StepPhase r} {ρ' : ℝ} (hρ' : 0 < ρ') (hball : ball w ρ' ⊆ U)
    {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) (y : StepPhase r) :
    stepNu (η * r) (transNop ι Z t w y) ≤ η⁻¹ ^ 2 * (M / ρ') * stepNu (η * r) y := by
  have h1 := flowII_deriv h hZ hb hρ' hball ht
  have hy := (stepNu_mono (y := y) hη0 hη1).1
  have hw := (stepNu_mono (y := transNop ι Z t w y) hη0 hη1).2
  have h2 : ‖transNop ι Z t w y‖ ≤ M / ρ' * ‖y‖ := by
    unfold transNop
    simp only [ContinuousLinearMap.comp_apply]
    exact ((fderiv ℂ (smoothDisp ι Z t) w).le_opNorm _).trans
      (mul_le_mul h1 (hι y) (norm_nonneg _) (by have := h.M_pos; positivity))
  calc _ ≤ η⁻¹ ^ 2 * ‖transNop ι Z t w y‖ := hw
    _ ≤ η⁻¹ ^ 2 * (M / ρ' * ‖y‖) := by gcongr
    _ ≤ η⁻¹ ^ 2 * (M / ρ' * stepNu (η * r) y) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hy
          (by have := h.M_pos; positivity)) (by positivity)
    _ = _ := by ring

theorem stepNu_transNop_sub_le (hη0 : 0 < η) (hη1 : η ≤ 1) (hι : ∀ g, ‖ι g‖ ≤ ‖g‖)
    (h : FlowHyp (smoothField ι Z) V U M δ) (h' : FlowHyp (smoothField ι Z') V U M δ)
    (hZ : DifferentiableOn ℂ Z V) (hb : ∀ z ∈ V, ‖Z z‖ ≤ M) (hZ' : DifferentiableOn ℂ Z' V)
    (hb' : ∀ z ∈ V, ‖Z' z‖ ≤ M) (hL : M / δ ≤ 1 / 64) {N₁ : ℝ} (hN₁ : 0 ≤ N₁)
    (hZZ : ∀ z ∈ V, ‖Z z - Z' z‖ ≤ N₁) {w : StepPhase r} {ρ' : ℝ} (hρ' : 0 < ρ')
    (hball : ball w ρ' ⊆ U) {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) (y : StepPhase r) :
    stepNu (η * r) (transNop ι Z t w y - transNop ι Z' t w y) ≤
      η⁻¹ ^ 2 * (2 * N₁ / ρ') * stepNu (η * r) y := by
  have h1 := flowII_deriv_sub h h' hZ hb hZ' hb' hι hL hN₁ hZZ hρ' hball ht
  have hy := (stepNu_mono (y := y) hη0 hη1).1
  have hw := (stepNu_mono (y := transNop ι Z t w y - transNop ι Z' t w y) hη0 hη1).2
  have h2 : ‖transNop ι Z t w y - transNop ι Z' t w y‖ ≤ 2 * N₁ / ρ' * ‖y‖ := by
    unfold transNop
    simp only [ContinuousLinearMap.comp_apply]
    rw [← sub_apply]
    exact ((fderiv ℂ (smoothDisp ι Z t) w - fderiv ℂ (smoothDisp ι Z' t) w).le_opNorm _).trans
      (mul_le_mul h1 (hι y) (norm_nonneg _) (by positivity))
  calc _ ≤ η⁻¹ ^ 2 * ‖transNop ι Z t w y - transNop ι Z' t w y‖ := hw
    _ ≤ η⁻¹ ^ 2 * (2 * N₁ / ρ' * ‖y‖) := by gcongr
    _ ≤ η⁻¹ ^ 2 * (2 * N₁ / ρ' * stepNu (η * r) y) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hy (by positivity)) (by positivity)
    _ = _ := by ring

end N

end KAM.Wave
