/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.KamStep.StepPlusFinal
public import KAM.Wave.KamStep.Class
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The pulled-back term `(P - R) ∘ Φ` (blueprint-W `bpW:w5:new-ham` (ii))

Off-frontier, source-faithful infrastructure (W5-STEP); the dependency graph is still being built.

`stepSympCLM_embed_apply`: `ϖ_{p,p}(ι g, W) = ϖ_{p_+,p}(g, W)`. The function `Q₀ = P - R` on
`StepPhase r` has derivative `B(ι(X_P - X_R), ·)` on `D(s,r)`; its pull-back by the flow is a
smoothing Hamiltonian with field `(1 + N_1)⁻¹ (X_P - X_R)(Φ w)`.
-/

@[expose] public noncomputable section

open Set Metric

namespace KAM.Wave

open KAM

variable {a p pb s r σ η Mf e₁ : ℝ} [Fact (0 < r)]

theorem stepSympCLM_embed_apply (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) (g W : StepPhase r) :
    stepSympCLM (q := p) (q' := p) ha (by linarith) r (stepEmbedCLM a p pb hpb r g) W =
      stepSymp (q := pb) (q' := p) ha (by linarith) (StepPhase.toK g) (StepPhase.toK W) := by
  rw [stepSympCLM_apply, stepEmbedCLM_apply, stepSymp_embed ha hpb (by linarith)
    (by linarith : 0 ≤ p + pb), stepSymp_comm_weights ha (by linarith) (by linarith)]

/-- `P` as a function on `StepPhase r`. -/
def stepPS (P : KamPhase → ℂ) (r : ℝ) : StepPhase r → ℂ := fun z => P (StepPhase.toK z)

/-- The field of `P` as a map into `StepPhase r`. -/
def stepXPS (X : KamPhase → KamPhase) (r : ℝ) : StepPhase r → StepPhase r :=
  fun z => StepPhase.ofK (X (StepPhase.toK z))

theorem stepPS_hasFDerivAt (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) {s : ℝ}
    {P : KamPhase → ℂ} {X : KamPhase → KamPhase}
    (hP : IsSmoothing (p := p) ha (by linarith : 0 ≤ pb + p) (kamDomain s r) P X)
    {z : StepPhase r} (hz : StepPhase.toK z ∈ kamDomain s r) :
    HasFDerivAt (stepPS P r)
      (stepSympCLM (q := p) (q' := p) ha (by linarith) r
        (stepEmbedCLM a p pb hpb r (stepXPS X r z))) z := by
  have hd : DifferentiableAt ℂ P (StepPhase.toK z) :=
    hP.holoP.differentiableAt ((kamDomain_isOpen s r).mem_nhds hz)
  have h : HasFDerivAt (stepPS P r) ((fderiv ℂ P (StepPhase.toK z)).comp (stepToKCLM r)) z :=
    hd.hasFDerivAt.comp z (stepToKCLM r).hasFDerivAt
  refine h.congr_fderiv (ContinuousLinearMap.ext fun W => ?_)
  rw [stepSympCLM_embed_apply ha hp hpb]
  simp only [ContinuousLinearMap.comp_apply, stepToKCLM_apply]
  rw [hP.deriv_eq _ hz]
  rfl

end KAM.Wave
