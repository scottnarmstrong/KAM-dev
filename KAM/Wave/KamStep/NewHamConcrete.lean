/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.KamStep.NewHamFlow
public import KAM.Wave.KamStep.StepPlusAssemble
public import KAM.Wave.KamStep.StepNfun
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# `H ∘ Φ = N_+ + P_+ + â₀` on the concrete flow (blueprint-W `bpW:w5:new-ham` (i))

Off-frontier, source-faithful infrastructure (W5-STEP); the dependency graph is still being built.

`stepNewHam_concrete`: for the flow of `X = ι ∘ Z_F` on `StepPhase r`, `N = stepNfun`, `N̂ = stepFS
N̂`,
`R = stepFS T` and the homological equation `R + DN·ιX_F = N̂ + â₀` on `V = D(s-σ, r)`,
`N(Φ w) + P(Φ w) = N w + N̂ w + â₀ + P_+(w)` for `w ∈ D(s-5σ, ηr)`, with
`P_+ = stepPplusS` (the function of `bpW:w5:new-ham`).
-/

@[expose] public noncomputable section

open Set Metric

namespace KAM.Wave

open KAM

variable {a p pb s r σ η Mf : ℝ} [Fact (0 < r)]

/-- **`H ∘ Φ = N_+ + P_+ + â₀`** (`bpW:w5:new-ham` (i)), `N_+ = N + N̂` as functions. -/
theorem stepNewHam_concrete {γ K0 : ℝ} {Ω : ℕ+ → ℝ} (hG : HomGuard a p γ) (hK0 : 0 ≤ K0)
    (hΩ : ∀ j : ℕ+, |Ω j| ≤ K0 * ((j : ℝ) + 2)) (ω : Fin 2 → ℝ)
    (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) (hσ : 0 < σ)
    (hσ1 : σ ≤ 1) (hσs : 5 * σ < s) (hη0 : 0 < η) (hη : η ≤ 1 / 8)
    (P : KamPhase → ℂ) (T : HomTaylor_gen a p pb s) (FT : HomTaylor_gen a p pb (s - σ))
    (hF : HomFieldBound_gen ha hp hpb r Mf FT) (hMf0 : 0 < Mf) (hMf : Mf ≤ σ / 1024)
    (a0 : ℂ)
    (hP : DifferentiableOn ℂ (stepPS P r) (stepDomain r (s - σ) r))
    (heq : ∀ w : KamPhase, w.1 ∈ complexStrip 2 (s - σ) →
      waveStepFun ha (homPP hp hpb) T w +
        ((homDN hG hK0 hΩ ω (stepToHom w)).comp stepToHom)
          (kamHomEmbed a p pb hpb (stepField ha hp hpb FT w)) =
      waveStepFun ha (homPP hp hpb) (homNhatTaylor_gen T) w + a0)
    {w : StepPhase r} (hw : w ∈ stepDomain r (s - 5 * σ) (η * r)) :
    stepNfun hG hK0 hΩ ω (StepPhase.toK (holoFlow (smoothField (stepEmbedCLM a p pb hpb r)
        (stepFieldS ha hp hpb FT r)) 1 w)) +
      stepPS P r (holoFlow (smoothField (stepEmbedCLM a p pb hpb r)
        (stepFieldS ha hp hpb FT r)) 1 w) =
    stepNfun hG hK0 hΩ ω (StepPhase.toK w) + stepFS ha hp hpb (homNhatTaylor_gen T) r w + a0 +
      (stepPS P r (holoFlow (smoothField (stepEmbedCLM a p pb hpb r)
        (stepFieldS ha hp hpb FT r)) 1 w) - stepFS ha hp hpb T r (holoFlow (smoothField
        (stepEmbedCLM a p pb hpb r) (stepFieldS ha hp hpb FT r)) 1 w) +
        ∫ t in (0 : ℝ)..1, stepGfam ha hp hpb T FT t (holoFlow (smoothField
          (stepEmbedCLM a p pb hpb r) (stepFieldS ha hp hpb FT r)) t w)) := by
  have hMδ : Mf < σ / 4 := by linarith
  have hFlow := stepFlowHyp_concrete' (S := s) ha hp hpb FT r hσ hσ1 (by linarith : 2 * σ < s)
    le_rfl hF hMf0 hMδ
  have hU : w ∈ stepDomain r (s - 2 * σ) (r / 2) := by
    have h8 : η * r ≤ r / 2 := by nlinarith [Fact.out (p := 0 < r)]
    exact kamDomain_mono (by linarith) (mul_pos hη0 Fact.out) h8 hw
  have hVθ : ∀ z ∈ stepDomain r (s - σ) r, (StepPhase.toK z).1 ∈ complexStrip 2 s :=
    fun z hz => stepDomain_theta_mem (by linarith) hz
  have hFθ : ∀ z ∈ stepDomain r (s - σ) r, (StepPhase.toK z).1 ∈ complexStrip 2 (s - σ) :=
    fun z hz => stepDomain_theta_mem le_rfl hz
  set ι := stepEmbedCLM a p pb hpb r with hι
  set Z := stepFieldS ha hp hpb FT r with hZ
  have hcont : ∀ {G : HomTaylor_gen a p pb s},
      ContinuousOn (fun t : ℝ => stepBrG ha hp hpb G FT (holoFlow (smoothField ι Z) t w))
        (Icc 0 1) := by
    intro G
    have hVsub : stepDomain r (s - σ) r ⊆
        {z : StepPhase r | (StepPhase.toK z).1 ∈ complexStrip 2 (s - σ)} := fun z hz => hFθ z hz
    have hcG : ContinuousOn (stepFieldS ha hp hpb G r) (stepDomain r (s - σ) r) :=
      ((stepFieldS_differentiableOn_theta ha hp hpb G).mono
        (fun z hz => by exact hVθ z hz)).continuousOn
    have hcF : ContinuousOn Z (stepDomain r (s - σ) r) :=
      ((stepFieldS_differentiableOn_theta ha hp hpb FT).mono hVsub).continuousOn
    have hBr : ContinuousOn (stepBrG ha hp hpb G FT) (stepDomain r (s - σ) r) := by
      have h1 : ContinuousOn (fun z => stepSympCLM (q := p) (q' := p) ha (by linarith) r
          (ι (stepFieldS ha hp hpb G r z))) (stepDomain r (s - σ) r) :=
        (stepSympCLM (q := p) (q' := p) ha (by linarith) r).continuous.comp_continuousOn
          (ι.continuous.comp_continuousOn hcG)
      exact h1.clm_apply (ι.continuous.comp_continuousOn hcF)
    have hφ := continuousOn_holoFlow_time hFlow hU
    refine (hBr.comp hφ (fun t ht => hFlow.mem_V_of_ball hU (holoFlow_mem_ball hFlow hU ht))).mono
      (fun t ht => ⟨by linarith [ht.1], ht.2⟩)
  have key := stepNewHam_flow_H hFlow (N := fun z => stepNfun hG hK0 hΩ ω (StepPhase.toK z))
    (N' := stepFS ha hp hpb (homNhatTaylor_gen T) r) (R := stepFS ha hp hpb T r)
    (P := stepPS P r)
    (DN := fun z => ((homDN hG hK0 hΩ ω (stepToHom (StepPhase.toK z))).comp stepToHom).comp
      (stepToKCLM r))
    (DN' := fun z => stepSympCLM (q := p) (q' := p) ha (by linarith) r
      (ι (stepFieldS ha hp hpb (homNhatTaylor_gen T) r z)))
    (DR := fun z => stepSympCLM (q := p) (q' := p) ha (by linarith) r
      (ι (stepFieldS ha hp hpb T r z))) (a0 := a0)
    (fun z hz => (stepNfun_hasFDerivAt hG hK0 hΩ ω (StepPhase.toK z)).comp z
      (stepToKCLM r).hasFDerivAt)
    (fun z hz => stepFS_hasFDerivAt ha hp hpb _ r (hVθ z hz))
    (fun z hz => stepFS_hasFDerivAt ha hp hpb T r (hVθ z hz))
    (fun z hz => by
      have h := heq (StepPhase.toK z) (hFθ z hz)
      show ((homDN hG hK0 hΩ ω (stepToHom (StepPhase.toK z))).comp stepToHom)
          (kamHomEmbed a p pb hpb (stepField ha hp hpb FT (StepPhase.toK z))) =
        waveStepFun ha (homPP hp hpb) (homNhatTaylor_gen T) (StepPhase.toK z) + a0 -
          waveStepFun ha (homPP hp hpb) T (StepPhase.toK z)
      linear_combination h)
    hU (hcont (G := homNhatTaylor_gen T)) (hcont (G := T))
  have hint : (∫ τ in (0 : ℝ)..1, ((1 - τ) • stepSympCLM (q := p) (q' := p) ha (by linarith) r
        (ι (stepFieldS ha hp hpb (homNhatTaylor_gen T) r (holoFlow (smoothField ι Z) τ w)))
        (smoothField ι Z (holoFlow (smoothField ι Z) τ w)) +
      τ • stepSympCLM (q := p) (q' := p) ha (by linarith) r
        (ι (stepFieldS ha hp hpb T r (holoFlow (smoothField ι Z) τ w)))
        (smoothField ι Z (holoFlow (smoothField ι Z) τ w)))) =
      ∫ t in (0 : ℝ)..1, stepGfam ha hp hpb T FT t (holoFlow (smoothField ι Z) t w) := by
    refine intervalIntegral.integral_congr (E := ℂ) fun t _ => ?_
    simp only [stepGfam, stepBrG, smoothField, Complex.real_smul]
    push_cast
    rfl
  rw [hint] at key
  linear_combination key

end KAM.Wave
