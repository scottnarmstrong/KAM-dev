/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.KamStep.StepFieldBound
public import KAM.Wave.KamStep.StepMargin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Lipschitz bound of a field at the small scale (blueprint-W `bpW:w5:pullback` step `p-dy`)

Off-frontier, source-faithful infrastructure (W5-STEP); the dependency graph is still being built.

`kamNorm_lipschitz_small`: for `Y` holomorphic on `D(S, 4ρ)` with `|Y|_ρ ≤ Y₀` there, and
`x, x' ∈ D(S-σ, 2ρ)`: `|Y x - Y x'|_ρ ≤ (2Y₀/σ) |x - x'|_ρ` (Cauchy in `StepPhase ρ`; balls of
radius `σ/2` in `|·|_{4ρ} ≤ |·|_ρ` stay in `D(S, 4ρ)`).
-/

@[expose] public noncomputable section

open Set Metric

namespace KAM.Wave

open KAM

theorem kamNorm_ball_mem {S σ ρ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hSσ : σ < S) (hρ : 0 < ρ) {x W : KamPhase}
    (hx : x ∈ kamDomain (S - σ) (2 * ρ)) (hW : kamNorm ρ W < σ / 2) :
    x + W ∈ kamDomain S (4 * ρ) := by
  have h4 : 0 < 4 * ρ := by positivity
  have hW4 : kamNorm (4 * ρ) W < σ / 2 := by
    refine lt_of_le_of_lt ?_ hW
    exact kamNorm_le_of_le_radius hρ (by linarith) W
  have hx' : x ∈ kamDomain ((S + σ) - 2 * σ) (4 * ρ / 2) := by
    have e1 : (S + σ) - 2 * σ = S - σ := by ring
    have e2 : 4 * ρ / 2 = 2 * ρ := by ring
    rw [e1, e2]; exact hx
  have := kamDomain_add_mem (s := S + σ) hσ hσ1 (by linarith) h4 hx' hW4
  have e3 : (S + σ) - σ = S := by ring
  rwa [e3] at this


theorem kamNorm_lipschitz_small {S σ ρ Y0 : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hSσ : σ < S)
    (hρ : 0 < ρ) {Y : KamPhase → KamPhase} (hY : DifferentiableOn ℂ Y (kamDomain S (4 * ρ)))
    (hb : ∀ z ∈ kamDomain S (4 * ρ), kamNorm ρ (Y z) ≤ Y0) (hY0 : 0 ≤ Y0) {x x' : KamPhase}
    (hx : x ∈ kamDomain (S - σ) (2 * ρ)) (hx' : x' ∈ kamDomain (S - σ) (2 * ρ)) :
    kamNorm ρ (Y x - Y x') ≤ Y0 / (σ / 2) * kamNorm ρ (x - x') := by
  haveI : Fact (0 < ρ) := ⟨hρ⟩
  set f : StepPhase ρ → StepPhase ρ := fun z => StepPhase.ofK (Y (StepPhase.toK z)) with hf
  have hV : IsOpen (stepDomain ρ S (4 * ρ)) := stepDomain_isOpen _ _ _
  have hfd : DifferentiableOn ℂ f (stepDomain ρ S (4 * ρ)) := fun z hz =>
    (((stepOfKCLM ρ).differentiableAt).comp z
      ((hY.differentiableAt ((kamDomain_isOpen S (4 * ρ)).mem_nhds hz)).comp z
        (stepToKCLM ρ).differentiableAt)).differentiableWithinAt
  have hfb : ∀ z ∈ stepDomain ρ S (4 * ρ), ‖f z‖ ≤ Y0 := fun z hz => hb _ hz
  have hconv : Convex ℝ (stepDomain ρ (S - σ) (2 * ρ)) := by
    have := (kamDomain_convex (S - σ) (2 * ρ)).linear_preimage
      (((stepToKCLM ρ).restrictScalars ℝ).toLinearMap)
    exact this
  have hmarg : ∀ z ∈ stepDomain ρ (S - σ) (2 * ρ), ball z (σ / 2) ⊆ stepDomain ρ S (4 * ρ) := by
    intro z hz y hy
    rw [mem_ball, dist_eq_norm, stepPhase_norm_eq] at hy
    have h : StepPhase.toK z + (StepPhase.toK y - StepPhase.toK z) ∈ kamDomain S (4 * ρ) :=
      kamNorm_ball_mem hσ hσ1 hSσ hρ hz (W := StepPhase.toK y - StepPhase.toK z) hy
    have e : StepPhase.toK z + (StepPhase.toK y - StepPhase.toK z) = StepPhase.toK y := by
      rw [add_sub_cancel]
    rw [e] at h
    exact h
  have := lipschitz_of_margin (by positivity : 0 < σ / 2) hY0 hV hfd hfb hconv hmarg
    (StepPhase.ofK (r := ρ) x) hx (StepPhase.ofK (r := ρ) x') hx'
  exact this

end KAM.Wave
