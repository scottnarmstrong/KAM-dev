/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.KamStep.StepBracket
public import KAM.Wave.KamStep.NewHamIntegral
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The commutator integral of `P_+` is a smoothing Hamiltonian (blueprint-W `bpW:w5:new-ham` (ii))

Off-frontier, source-faithful infrastructure (W5-STEP); the dependency graph is still being built.

`stepGfam t = (1-t) {N̂,F} + t {R,F}` (the brackets `{R(t),F}` of `R(t) = (1-t)N̂ + tR`) with
`G`-valued fields `stepZgfam` (Zeros of `Cauchy`-bounded size `O(εM_F/σ)`), and the conclusion of
`newHam_integral_smoothing` on `D_+ = D(s-5σ, ηr)`.
-/

@[expose] public noncomputable section

open Set Metric

namespace KAM.Wave

open KAM

variable {a p pb s r σ η M e₁ : ℝ} [Fact (0 < r)]

section fam

variable (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) (T : HomTaylor_gen a p pb s)
  (FT : HomTaylor_gen a p pb (s - σ))

/-- `{R(t), F}` as a function. -/
def stepGfam (t : ℝ) : StepPhase r → ℂ := fun z =>
  (1 - (t : ℂ)) * stepBrG ha hp hpb (homNhatTaylor_gen T) FT z + (t : ℂ) * stepBrG ha hp hpb T FT z

/-- The `G`-valued field of `{R(t), F}`. -/
def stepZgfam (t : ℝ) : StepPhase r → StepPhase r := fun z =>
  (1 - (t : ℂ)) • stepBrZ ha hp hpb (homNhatTaylor_gen T) FT z + (t : ℂ) • stepBrZ ha hp hpb T FT z

variable {ha hp hpb T FT}

theorem stepGfam_hasFDerivAt (hσ : 0 < σ) (hσs : 2 * σ < s) (t : ℝ) {z : StepPhase r}
    (hz : z ∈ stepDomain r (s - 2 * σ) (r / 2)) :
    HasFDerivAt (stepGfam ha hp hpb T FT t)
      (stepSympCLM (q := p) (q' := p) ha (by linarith) r
        (stepEmbedCLM a p pb hpb r (stepZgfam ha hp hpb T FT t z))) z := by
  have h1 := (stepBrG_hasFDerivAt (ha := ha) (hp := hp) (hpb := hpb) (TG := homNhatTaylor_gen T)
    (FT := FT) hσ hσs hz).const_mul (1 - (t : ℂ))
  have h2 := (stepBrG_hasFDerivAt (ha := ha) (hp := hp) (hpb := hpb) (TG := T) (FT := FT) hσ hσs
    hz).const_mul (t : ℂ)
  have h : HasFDerivAt (stepGfam ha hp hpb T FT t) _ z := h1.add h2
  refine h.congr_fderiv ?_
  ext W
  simp [stepZgfam, map_add, map_smul]

end fam

end KAM.Wave
