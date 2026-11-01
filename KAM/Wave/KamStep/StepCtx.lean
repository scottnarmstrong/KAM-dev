/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.KamStep.StepBracket
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The flow context of a step (blueprint-W `bpW:w5:flow`)

Off-frontier, source-faithful infrastructure (W5-STEP); the dependency graph is still being built.

`StepCtx`: all the hypotheses of the abstract flow engine for `F = G = StepPhase r`,
`ι = stepEmbedCLM`, `Z = stepFieldS FT`, `B = stepSympCLM`, on `V = D(s-σ,r)`, `U = D(s-2σ,r/2)`.
-/

@[expose] public noncomputable section

open Set Metric

namespace KAM.Wave

open KAM

variable {a p pb s r σ M : ℝ} [Fact (0 < r)]

/-- The engine hypotheses for the field `Z = X_F`. -/
structure StepCtx (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) (σ s : ℝ)
    (FT : HomTaylor_gen a p pb (s - σ)) (M : ℝ) (r : ℝ) [Fact (0 < r)] : Prop where
  flow : FlowHyp (smoothField (stepEmbedCLM a p pb hpb r) (stepFieldS ha hp hpb FT r))
    (stepDomain r (s - σ) r) (stepDomain r (s - 2 * σ) (r / 2)) M (σ / 4)
  holo : DifferentiableOn ℂ (stepFieldS ha hp hpb FT r) (stepDomain r (s - σ) r)
  bound : ∀ z ∈ stepDomain r (s - σ) r, ‖stepFieldS ha hp hpb FT r z‖ ≤ M
  skew : ∀ z ∈ stepDomain r (s - σ) r, ∀ x y,
    stepSympCLM (q := p) (q' := p) ha (by linarith) r
        (fderiv ℂ (smoothField (stepEmbedCLM a p pb hpb r) (stepFieldS ha hp hpb FT r)) z x) y +
      stepSympCLM (q := p) (q' := p) ha (by linarith) r x
        (fderiv ℂ (smoothField (stepEmbedCLM a p pb hpb r) (stepFieldS ha hp hpb FT r)) z y) = 0

protected theorem StepCtx.mk' (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hσs : 2 * σ < s) {FT : HomTaylor_gen a p pb (s - σ)}
    (hF : HomFieldBound_gen ha hp hpb r M FT) (hM0 : 0 < M) (hMδ : M < σ / 4) :
    StepCtx ha hp hpb σ s FT M r := by
  have hVd : ∀ z ∈ stepDomain r (s - σ) r,
      z ∈ {z : StepPhase r | (StepPhase.toK z).1 ∈ complexStrip 2 (s - σ)} := fun z hz =>
    stepDomain_theta_mem le_rfl hz
  exact ⟨stepFlowHyp_concrete' (S := s) ha hp hpb FT r hσ hσ1 hσs le_rfl hF hM0 hMδ,
    (stepFieldS_differentiableOn_theta ha hp hpb FT).mono hVd,
    fun z hz => stepFieldS_bound ha hp hpb FT r hF le_rfl hz,
    fun z hz x y => stepFieldS_skew ha hp hpb FT r (stepDomain_theta_mem le_rfl hz) x y⟩

end KAM.Wave
