/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.KamStep.ParamIntegral
public import KAM.Wave.KamStep.PullbackNu
public import KAM.Wave.KamStep.StepFlowConcrete
public import KAM.Wave.KamStep.TaylorEst
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Scale norms of parameter integrals (blueprint-W `bpW:w5:new-ham` step `n-field`)

Off-frontier, source-faithful infrastructure (W5-STEP); the dependency graph is still being built.

`stepNu_integral_sub_le`: if `ν_ρ(f₁(t) - f₂(t)) ≤ K` for `t ∈ [0,1]` and `f₁, f₂` are Lipschitz in
`t` then `ν_ρ(∫₀¹ f₁ - ∫₀¹ f₂) ≤ K` (Riemann sums and the continuity of the norm `|·|_ρ`).
-/

@[expose] public noncomputable section

open Set Filter Topology MeasureTheory intervalIntegral

namespace KAM.Wave

open KAM

variable {r ρ : ℝ} [Fact (0 < r)]

/-- `|·|_ρ` on `StepPhase r` as the norm of a continuous linear map into `StepPhase ρ`. -/
def stepKappa (ρ : ℝ) [Fact (0 < ρ)] : StepPhase r →L[ℂ] StepPhase ρ :=
  (kamToStep ρ).comp (stepToKCLM r)

theorem norm_stepKappa (ρ : ℝ) [Fact (0 < ρ)] (y : StepPhase r) :
    ‖stepKappa ρ y‖ = stepNu ρ y := rfl

theorem stepNu_integral_sub_le (hρ : 0 < ρ) {f₁ f₂ : ℝ → StepPhase r} {L₁ L₂ K : ℝ}
    (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂)
    (hf₁ : ∀ t ∈ Icc (0 : ℝ) 1, ∀ t' ∈ Icc (0 : ℝ) 1, ‖f₁ t - f₁ t'‖ ≤ L₁ * |t - t'|)
    (hf₂ : ∀ t ∈ Icc (0 : ℝ) 1, ∀ t' ∈ Icc (0 : ℝ) 1, ‖f₂ t - f₂ t'‖ ≤ L₂ * |t - t'|)
    (hK : ∀ t ∈ Icc (0 : ℝ) 1, stepNu ρ (f₁ t - f₂ t) ≤ K) :
    stepNu ρ ((∫ t in (0 : ℝ)..1, f₁ t) - ∫ t in (0 : ℝ)..1, f₂ t) ≤ K := by
  haveI : Fact (0 < ρ) := ⟨hρ⟩
  have h1 := tendstoUniformlyOn_riemann (S := ({()} : Set Unit)) (f := fun t (_ : Unit) => f₁ t)
    hL₁ (fun _ _ t ht t' ht' => hf₁ t ht t' ht')
  have h2 := tendstoUniformlyOn_riemann (S := ({()} : Set Unit)) (f := fun t (_ : Unit) => f₂ t)
    hL₂ (fun _ _ t ht t' ht' => hf₂ t ht t' ht')
  have t1 := h1.tendsto_at (Set.mem_singleton ())
  have t2 := h2.tendsto_at (Set.mem_singleton ())
  have hcont : Continuous (fun y : StepPhase r => ‖stepKappa ρ y‖) :=
    (stepKappa ρ).continuous.norm
  have hlim := (hcont.tendsto _).comp (t1.sub t2)
  refine le_of_tendsto hlim (eventually_atTop.2 ⟨1, fun n hn => ?_⟩)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  simp only [Function.comp_apply, norm_stepKappa]
  rw [← norm_stepKappa]
  unfold riemannSum
  rw [← smul_sub, ← Finset.sum_sub_distrib, ContinuousLinearMap.map_smul_of_tower, norm_smul]
  have hs : ‖(1 : ℝ) / n‖ = 1 / n := by rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [hs]
  have hsum : ‖stepKappa ρ (∑ i ∈ Finset.range n, (f₁ ((i : ℝ) / n) - f₂ ((i : ℝ) / n)))‖ ≤
      n * K := by
    rw [map_sum]
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum fun i hi => ?_).trans
      (le_of_eq (by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]))
    have hi' := Finset.mem_range.mp hi
    have hin : (i : ℝ) / n ∈ Icc (0 : ℝ) 1 :=
      ⟨by positivity, by rw [div_le_one hn0]; exact_mod_cast hi'.le⟩
    have := hK _ hin
    rw [← norm_stepKappa] at this
    simpa using this
  calc 1 / (n : ℝ) * ‖stepKappa ρ (∑ i ∈ Finset.range n, (f₁ ((i : ℝ) / n) - f₂ ((i : ℝ) / n)))‖
      ≤ 1 / (n : ℝ) * (n * K) := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = K := by field_simp

end KAM.Wave
