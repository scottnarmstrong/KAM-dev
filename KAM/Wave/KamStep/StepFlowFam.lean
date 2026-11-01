/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.KamStep.FlowStepBounds
public import KAM.Wave.KamStep.StepBracket
public import KAM.Wave.KamStep.StepMargin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The transformation bounds (blueprint-W `bpW:w5:step` (v), `bpW:w5:flow` (i)--(ii))

Off-frontier, source-faithful infrastructure (W5-STEP); the dependency graph is still being built.

`stepFlow_bounds`: for two Taylor fields `F_1, F_2` with `|X_{F_i}|_r ≤ M₀`, `|X_{F_1} - X_{F_2}|_r
≤ N`,
`M₀ ≤ σ/1024`, on `w ∈ D(s-3σ, r/4)`: `Φ = φ¹` satisfies `|Φ_1 w - w| ≤ M₀`,
`|(Φ_1 - Φ_2) w| ≤ 2N`, `|DΦ_1(w) - I| ≤ 8M₀/σ`, `|DΦ_1(w) - DΦ_2(w)| ≤ 16N/σ`.
With `M₀ + λ M₁ ≤ M_F`, `N = M₁ d` these give the `λ`-bounds `2M_F` and `16M_F/σ`.
-/

@[expose] public noncomputable section

open Set Metric

namespace KAM.Wave

open KAM

variable {a p pb s r σ : ℝ} [Fact (0 < r)]

theorem stepFlow_bounds (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hσs : 3 * σ < s) {FT₁ FT₂ : HomTaylor_gen a p pb (s - σ)} {M₀ N : ℝ}
    (hF₁ : HomFieldBound_gen ha hp hpb r M₀ FT₁) (hF₂ : HomFieldBound_gen ha hp hpb r M₀ FT₂)
    (hΔF : HomFieldBound_gen ha hp hpb r N (FT₁.homSub FT₂)) (hM0 : 0 < M₀)
    (hM : M₀ ≤ σ / 1024) (hN : 0 ≤ N) {w : StepPhase r}
    (hw : w ∈ stepDomain r (s - 3 * σ) (r / 4)) :
    ‖holoFlow (smoothField (stepEmbedCLM a p pb hpb r) (stepFieldS ha hp hpb FT₁ r)) 1 w - w‖ ≤
        M₀ ∧
      ‖(holoFlow (smoothField (stepEmbedCLM a p pb hpb r) (stepFieldS ha hp hpb FT₁ r)) 1 w - w) -
        (holoFlow (smoothField (stepEmbedCLM a p pb hpb r) (stepFieldS ha hp hpb FT₂ r)) 1 w - w)‖
          ≤ 2 * N ∧
      ‖fderiv ℂ (holoFlow (smoothField (stepEmbedCLM a p pb hpb r) (stepFieldS ha hp hpb FT₁ r))
          1) w - ContinuousLinearMap.id ℂ _‖ ≤ 8 * M₀ / σ ∧
      ‖fderiv ℂ (holoFlow (smoothField (stepEmbedCLM a p pb hpb r) (stepFieldS ha hp hpb FT₁ r))
          1) w - fderiv ℂ (holoFlow (smoothField (stepEmbedCLM a p pb hpb r)
            (stepFieldS ha hp hpb FT₂ r)) 1) w‖ ≤ 16 * N / σ := by
  have hMδ : M₀ < σ / 4 := by linarith
  have hFl₁ := stepFlowHyp_concrete' (S := s) ha hp hpb FT₁ r hσ hσ1 (by linarith : 2 * σ < s)
    le_rfl hF₁ hM0 hMδ
  have hFl₂ := stepFlowHyp_concrete' (S := s) ha hp hpb FT₂ r hσ hσ1 (by linarith : 2 * σ < s)
    le_rfl hF₂ hM0 hMδ
  have hVθ : stepDomain r (s - σ) r ⊆
      {z : StepPhase r | (StepPhase.toK z).1 ∈ complexStrip 2 (s - σ)} := fun z hz =>
    stepDomain_theta_mem le_rfl hz
  have hZ₁ := (stepFieldS_differentiableOn_theta ha hp hpb FT₁).mono hVθ
  have hZ₂ := (stepFieldS_differentiableOn_theta ha hp hpb FT₂).mono hVθ
  have hb₁ : ∀ z ∈ stepDomain r (s - σ) r, ‖stepFieldS ha hp hpb FT₁ r z‖ ≤ M₀ := fun z hz =>
    stepFieldS_bound ha hp hpb FT₁ r hF₁ le_rfl hz
  have hb₂ : ∀ z ∈ stepDomain r (s - σ) r, ‖stepFieldS ha hp hpb FT₂ r z‖ ≤ M₀ := fun z hz =>
    stepFieldS_bound ha hp hpb FT₂ r hF₂ le_rfl hz
  have hZZ : ∀ z ∈ stepDomain r (s - σ) r,
      ‖stepFieldS ha hp hpb FT₁ r z - stepFieldS ha hp hpb FT₂ r z‖ ≤ N := fun z hz => by
    rw [← stepFieldS_sub ha hp hpb FT₁ FT₂ (stepDomain_theta_mem le_rfl hz)]
    exact stepFieldS_bound ha hp hpb _ r hΔF le_rfl hz
  have hL : M₀ / (σ / 4) ≤ 1 / 64 := by
    rw [div_le_iff₀ (by positivity)]; linarith
  have hU : w ∈ stepDomain r (s - 2 * σ) (r / 2) := stepDomain_mono' (by linarith)
    (by have := Fact.out (p := 0 < r); positivity)
    (by have := Fact.out (p := 0 < r); linarith) hw
  have hball := stepDomain_U_margin hσ hσ1 hσs hw
  have h1 : (1 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨by norm_num, le_rfl⟩
  have hι := norm_stepEmbedCLM_apply_le a p pb hpb r
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [holoFlow_smooth_eq hFl₁ hZ₁ hU h1, add_sub_cancel_left]
    exact (hι _).trans (flowII_disp hFl₁ hb₁ hU h1)
  · rw [holoFlow_smooth_eq hFl₁ hZ₁ hU h1, holoFlow_smooth_eq hFl₂ hZ₂ hU h1]
    have e : (w + stepEmbedCLM a p pb hpb r (smoothDisp (stepEmbedCLM a p pb hpb r)
        (stepFieldS ha hp hpb FT₁ r) 1 w) - w) - (w + stepEmbedCLM a p pb hpb r
        (smoothDisp (stepEmbedCLM a p pb hpb r) (stepFieldS ha hp hpb FT₂ r) 1 w) - w) =
        stepEmbedCLM a p pb hpb r (smoothDisp (stepEmbedCLM a p pb hpb r)
          (stepFieldS ha hp hpb FT₁ r) 1 w - smoothDisp (stepEmbedCLM a p pb hpb r)
          (stepFieldS ha hp hpb FT₂ r) 1 w) := by
      rw [map_sub]; abel
    rw [e]
    exact (hι _).trans (flowII_disp_sub hFl₁ hFl₂ hZ₁ hZ₂ hι hb₂ hL hN hZZ hU h1)
  · rw [fderiv_holoFlow_smooth hFl₁ hZ₁ hb₁ hU h1, add_sub_cancel_left]
    have := flowII_deriv hFl₁ hZ₁ hb₁ (by positivity : (0 : ℝ) < σ / 8) hball h1
    calc _ ≤ ‖stepEmbedCLM a p pb hpb r‖ * ‖fderiv ℂ (smoothDisp (stepEmbedCLM a p pb hpb r)
          (stepFieldS ha hp hpb FT₁ r) 1) w‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * (M₀ / (σ / 8)) := by
          refine mul_le_mul ?_ this (norm_nonneg _) zero_le_one
          exact ContinuousLinearMap.opNorm_le_bound _ zero_le_one
            (fun x => by rw [one_mul]; exact hι x)
      _ = 8 * M₀ / σ := by field_simp
  · rw [fderiv_holoFlow_smooth hFl₁ hZ₁ hb₁ hU h1, fderiv_holoFlow_smooth hFl₂ hZ₂ hb₂ hU h1,
      add_sub_add_left_eq_sub, ← ContinuousLinearMap.comp_sub]
    have := flowII_deriv_sub hFl₁ hFl₂ hZ₁ hb₁ hZ₂ hb₂ hι hL hN hZZ
      (by positivity : (0 : ℝ) < σ / 8) hball h1
    calc _ ≤ ‖stepEmbedCLM a p pb hpb r‖ * ‖fderiv ℂ (smoothDisp (stepEmbedCLM a p pb hpb r)
          (stepFieldS ha hp hpb FT₁ r) 1) w - fderiv ℂ (smoothDisp (stepEmbedCLM a p pb hpb r)
          (stepFieldS ha hp hpb FT₂ r) 1) w‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * (2 * N / (σ / 8)) := by
          refine mul_le_mul ?_ this (norm_nonneg _) zero_le_one
          exact ContinuousLinearMap.opNorm_le_bound _ zero_le_one
            (fun x => by rw [one_mul]; exact hι x)
      _ = 16 * N / σ := by field_simp; ring

end KAM.Wave
