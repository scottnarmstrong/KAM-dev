/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.KamStep.StepCLM
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The Hamiltonian of a W4 Taylor polynomial on `KamPhase` (blueprint-W `bpW:w5:solve`, step
`s-class`)

Off-frontier, source-faithful infrastructure (W5-STEP); the dependency graph is still being built.

For `T : HomTaylor_gen a p pb s` (W4's class `𝒯_s`) we define the polynomial
`waveStepFun T : KamPhase → ℂ` in the coordinates `(θ, y, u, v)` of `bpW:w1:kam-space`, through
`z = (u + i v)/√2`, `z̄ = (u - i v)/√2` (`stepZ`, `stepZb`), and prove that it is Fréchet
differentiable on `θ ∈ T_s`.
-/

@[expose] public noncomputable section

namespace KAM.Wave

open KAM

/-- `z = (u + i v)/√2` as a continuous linear map on `KamPhase`. -/
def stepZ : KamPhase →L[ℂ] HomL2 :=
  homSqrt2⁻¹ • ((ContinuousLinearMap.fst ℂ HomL2 HomL2).comp
      ((ContinuousLinearMap.snd ℂ (Fin 2 → ℂ) (HomL2 × HomL2)).comp
        (ContinuousLinearMap.snd ℂ (Fin 2 → ℂ) ((Fin 2 → ℂ) × HomL2 × HomL2)))
    + Complex.I • (ContinuousLinearMap.snd ℂ HomL2 HomL2).comp
      ((ContinuousLinearMap.snd ℂ (Fin 2 → ℂ) (HomL2 × HomL2)).comp
        (ContinuousLinearMap.snd ℂ (Fin 2 → ℂ) ((Fin 2 → ℂ) × HomL2 × HomL2))))

/-- `z̄ = (u - i v)/√2`. -/
def stepZb : KamPhase →L[ℂ] HomL2 :=
  homSqrt2⁻¹ • ((ContinuousLinearMap.fst ℂ HomL2 HomL2).comp
      ((ContinuousLinearMap.snd ℂ (Fin 2 → ℂ) (HomL2 × HomL2)).comp
        (ContinuousLinearMap.snd ℂ (Fin 2 → ℂ) ((Fin 2 → ℂ) × HomL2 × HomL2)))
    - Complex.I • (ContinuousLinearMap.snd ℂ HomL2 HomL2).comp
      ((ContinuousLinearMap.snd ℂ (Fin 2 → ℂ) (HomL2 × HomL2)).comp
        (ContinuousLinearMap.snd ℂ (Fin 2 → ℂ) ((Fin 2 → ℂ) × HomL2 × HomL2))))

theorem stepZ_apply (θ y : Fin 2 → ℂ) (u v : HomL2) :
    stepZ (θ, y, u, v) = homSqrt2⁻¹ • (u + Complex.I • v) := by
  simp [stepZ]

theorem stepZb_apply (θ y : Fin 2 → ℂ) (u v : HomL2) :
    stepZb (θ, y, u, v) = homSqrt2⁻¹ • (u - Complex.I • v) := by
  simp [stepZb]

section Fun

variable {a p pb s : ℝ}

/-- The pairing of a `p_+`-representative with a `p`-representative. -/
abbrev stepPr (ha : 0 ≤ a) (hpp : 0 ≤ p + pb) : HomL2 →L[ℂ] HomL2 →L[ℂ] ℂ :=
  stepPairCLM (q := p) (q' := pb) ha hpp

/-- **The polynomial `F` of a W4 Taylor polynomial** (`𝒯_s`) on `KamPhase`:
`F = a₀ + ⟨b,y⟩ + ⟨c⁺,z⟩ + ⟨c⁻,z̄⟩ + ⟨Pz,z⟩ + ⟨Qz,z̄⟩ + ⟨P'z̄,z̄⟩`, `z = (u+iv)/√2`. -/
def waveStepFun (ha : 0 ≤ a) (hpp : 0 ≤ p + pb) (T : HomTaylor_gen a p pb s) (w : KamPhase) : ℂ :=
  T.a0 w.1 + ∑ k, T.b w.1 k * w.2.1 k
    + stepPr ha hpp (T.cp w.1) (stepZ w) + stepPr ha hpp (T.cm w.1) (stepZb w)
    + stepPr ha hpp (T.P w.1 (stepZ w)) (stepZ w) + stepPr ha hpp (T.Q w.1 (stepZ w)) (stepZb w)
    + stepPr ha hpp (T.P' w.1 (stepZb w)) (stepZb w)

/-- The first projection `KamPhase → ℂ²`. -/
abbrev stepPrTheta : KamPhase →L[ℂ] (Fin 2 → ℂ) := ContinuousLinearMap.fst ℂ _ _

theorem hasFDerivAt_pair_term (ha : 0 ≤ a) (hpp : 0 ≤ p + pb) {A B : KamPhase → HomL2}
    {A' B' : KamPhase →L[ℂ] HomL2} {w : KamPhase} (hA : HasFDerivAt A A' w)
    (hB : HasFDerivAt B B' w) :
    HasFDerivAt (fun x => stepPr ha hpp (A x) (B x))
      ((stepPr ha hpp (A w)).comp B' + ((stepPr ha hpp).comp A').flip (B w)) w :=
  ((stepPr ha hpp).hasFDerivAt.comp w hA).clm_apply hB

theorem hasFDerivAt_theta_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : (Fin 2 → ℂ) → E} {w : KamPhase} (hf : DifferentiableAt ℂ f w.1) :
    HasFDerivAt (fun x : KamPhase => f x.1) ((fderiv ℂ f w.1).comp stepPrTheta) w :=
  hf.hasFDerivAt.comp w (hasFDerivAt_fst)

theorem hasFDerivAt_op_apply {M : (Fin 2 → ℂ) → HomOp} {g : KamPhase → HomL2}
    {g' : KamPhase →L[ℂ] HomL2} {w : KamPhase} (hM : DifferentiableAt ℂ M w.1)
    (hg : HasFDerivAt g g' w) :
    HasFDerivAt (fun x : KamPhase => M x.1 (g x))
      ((M w.1).comp g' + ((fderiv ℂ M w.1).comp stepPrTheta).flip (g w)) w :=
  (hasFDerivAt_theta_comp hM).clm_apply hg

end Fun

end KAM.Wave
