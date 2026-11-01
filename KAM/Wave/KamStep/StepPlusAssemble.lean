/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.KamStep.StepPlusA
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# `P_+` is a smoothing Hamiltonian (blueprint-W `bpW:w5:new-ham` (ii))

Off-frontier, source-faithful infrastructure (W5-STEP); the dependency graph is still being built.

`stepPplus P X FT T`: `P_+ = (P - R)∘Φ + ∫₀¹ {R(t),F}∘φ^t dt` as a function of `w ∈ KamPhase`
(through `ofK`), `stepXplus`: its field. `stepPlus_isSmoothing`: `(P_+, X_+) ∈ 𝒮_{p_+}(D(s-5σ, ηr))`.
-/

@[expose] public noncomputable section

open Set Metric

namespace KAM.Wave

open KAM

variable {a p pb s r σ η Mf e₁ : ℝ} [Fact (0 < r)]

/-- The new Hamiltonian `P_+` on `StepPhase r`. -/
def stepPplusS (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) (P : KamPhase → ℂ)
    (T : HomTaylor_gen a p pb s) (FT : HomTaylor_gen a p pb (s - σ))
    : StepPhase r → ℂ := fun w =>
  (stepPS P r (holoFlow (smoothField (stepEmbedCLM a p pb hpb r) (stepFieldS ha hp hpb FT r)) 1 w) -
      stepFS ha hp hpb T r (holoFlow (smoothField (stepEmbedCLM a p pb hpb r)
        (stepFieldS ha hp hpb FT r)) 1 w)) +
    ∫ t in (0 : ℝ)..1, stepGfam ha hp hpb T FT t (holoFlow (smoothField (stepEmbedCLM a p pb hpb r)
      (stepFieldS ha hp hpb FT r)) t w)

/-- The field of `P_+`. -/
def stepXplusS (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb)
    (X : KamPhase → KamPhase) (T : HomTaylor_gen a p pb s) (FT : HomTaylor_gen a p pb (s - σ))
    : StepPhase r → StepPhase r := fun w =>
  transSolve (transNop (stepEmbedCLM a p pb hpb r) (stepFieldS ha hp hpb FT r) 1 w)
      (stepXPS X r (holoFlow (smoothField (stepEmbedCLM a p pb hpb r)
        (stepFieldS ha hp hpb FT r)) 1 w) -
        stepFieldS ha hp hpb T r (holoFlow (smoothField (stepEmbedCLM a p pb hpb r)
        (stepFieldS ha hp hpb FT r)) 1 w)) +
    ∫ t in (0 : ℝ)..1, yfam (stepEmbedCLM a p pb hpb r) (stepFieldS ha hp hpb FT r)
      (stepZgfam ha hp hpb T FT) t w

/-- **`(P_+, X_+) ∈ 𝒮_{p_+}(D(s-5σ, ηr))`** (`bpW:w5:new-ham` (ii), class membership). -/
theorem stepPlus_isSmoothing (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) (hσ : 0 < σ)
    (hσ1 : σ ≤ 1) (hσs : 5 * σ < s) (hη0 : 0 < η) (hη : η ≤ 1 / 8)
    {P : KamPhase → ℂ} {X : KamPhase → KamPhase}
    (hP : IsSmoothing (p := p) ha (by linarith : 0 ≤ pb + p) (kamDomain s r) P X)
    (T : HomTaylor_gen a p pb s) (FT : HomTaylor_gen a p pb (s - σ)) (he₁ : 0 ≤ e₁)
    (hT : HomFieldBound_gen ha hp hpb r e₁ T)
    (hTn : HomFieldBound_gen ha hp hpb r (2 * e₁) (homNhatTaylor_gen T))
    (hF : HomFieldBound_gen ha hp hpb r Mf FT) (hMf0 : 0 < Mf) (hMf : Mf ≤ σ / 1024) :
    IsSmoothing (p := p) ha (by linarith : 0 ≤ pb + p) (kamDomain (s - 5 * σ) (η * r))
      (fun w : KamPhase => stepPplusS ha hp hpb P T FT (StepPhase.ofK (r := r) w))
      (fun w : KamPhase => StepPhase.toK (stepXplusS ha hp hpb X T FT (StepPhase.ofK (r := r) w))) := by
  have hA := stepPlusA_smoothing ha hp hpb hσ hσ1 hσs hη0 hη hP T FT hF hMf0 hMf
  have hB := stepPlus_integral_smoothing ha hp hpb hσ hσ1 hσs hη0 hη T FT he₁ hT hTn hF hMf0 hMf
  obtain ⟨hA1, hA2⟩ := hA
  obtain ⟨hB1, hB2, hB3⟩ := hB
  have hderiv : ∀ w ∈ stepDomain r (s - 5 * σ) (η * r),
      HasFDerivAt (stepPplusS ha hp hpb P T FT)
        (stepSympCLM (q := p) (q' := p) ha (by linarith) r
          (stepEmbedCLM a p pb hpb r (stepXplusS ha hp hpb X T FT w))) w := by
    intro w hw
    have h := (hA1 w hw).add (hB3 w hw)
    refine h.congr_fderiv ?_
    ext W
    simp [stepXplusS, map_add]
  have hPd : DifferentiableOn ℂ (stepPplusS ha hp hpb P T FT) (stepDomain r (s - 5 * σ) (η * r)) :=
    fun w hw => (hderiv w hw).differentiableAt.differentiableWithinAt
  have hXd : DifferentiableOn ℂ (stepXplusS ha hp hpb X T FT) (stepDomain r (s - 5 * σ) (η * r)) :=
    hA2.add hB2
  refine ⟨?_, ?_, ?_⟩
  · exact hPd.comp (stepOfKCLM r).differentiable.differentiableOn (fun w hw => hw)
  · exact (stepToKCLM r).differentiable.comp_differentiableOn
      (hXd.comp (stepOfKCLM r).differentiable.differentiableOn (fun w hw => hw))
  · intro w hw W
    have h1 := hderiv (StepPhase.ofK (r := r) w) hw
    have h2 : HasFDerivAt (fun w : KamPhase => stepPplusS ha hp hpb P T FT (StepPhase.ofK (r := r) w))
        ((stepSympCLM (q := p) (q' := p) ha (by linarith) r
          (stepEmbedCLM a p pb hpb r (stepXplusS ha hp hpb X T FT (StepPhase.ofK (r := r) w)))).comp
            (stepOfKCLM r)) w := h1.comp w (stepOfKCLM r).hasFDerivAt
    rw [h2.fderiv]
    simp only [ContinuousLinearMap.comp_apply, stepOfKCLM_apply]
    rw [stepSympCLM_embed_apply ha hp hpb]
    rfl

end KAM.Wave
