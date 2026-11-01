/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Iteration.StepSmooth
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# W6: discharge of the W5 smoothing dependency (blueprint `bpW:w6:iter-lemma`, step `il-tr`)

Off the frontier: source-faithful infrastructure used by several nodes. The dependency graph is
still being built. Blueprint label `bpW:w6:iter-lemma` (step `il-tr`, the `p_+` bounds of one
step's transformation), used by `bpW:w6:convergence` (iii), (iv), `bpW:w6:invariance`,
`bpW:w6:prep-step` (iii), `bpW:w6:tori`.

W6-CONV stated the `p_+` bounds of W5's step transformation as the named dependencies
`W6StepSmooth` (unmodified step) and `W6StepSmoothMod` (modified step). W5 (`bpW:w5:step`, the
smoothing displacement `Ψ = StepCore.Psi`, W5-STEP-B-FIX) now provides them:

* `w6StepSmooth_holds : W6StepSmooth`, `w6StepSmoothMod_holds : W6StepSmoothMod`, with
  `Ψ = H.hyp.core.Psi ξ`: holomorphic on `D_+` (`StepCore.psi_differentiableOn`),
  `Φ = id + ι Ψ` (`StepCore.phi_eq_add_Psi`), the sharp sup bound `|Ψ|_{p_+,r} ≤ M_F`
  (`StepCore.psi_le_MF`), and `‖DΨ‖_{p → p_+} ≤ 8 M₀/σ ≤ 8 M_F/σ` (`StepCore.flow_pair_smooth`,
  `M₀ ≤ M₀ + λ M₁ ≤ M_F`).
-/

@[expose] public noncomputable section

namespace KAM.Wave

open KAM

/-- The derivative bound `‖DΨ‖ ≤ 8 M_F/σ` of a step core, from `‖DΨ‖ ≤ 8 M₀/σ` and `M₀ ≤ M_F`. -/
theorem StepCore.fderiv_psi_le_MF {a p pb s r σ η τ α lam ε ε₀ ε₁ γ M0 Mω MΩ M₀ M₁ cF tF : ℝ}
    {Par : Set (Fin 2 → ℝ)} {ω : (Fin 2 → ℝ) → Fin 2 → ℝ} {Ω : (Fin 2 → ℝ) → ℕ+ → ℝ}
    {P : (Fin 2 → ℝ) → KamPhase → ℂ} {X : (Fin 2 → ℝ) → KamPhase → KamPhase}
    {FT : (Fin 2 → ℝ) → HomTaylor_gen a p pb (s - σ)} [Fact (0 < r)]
    (H : StepCore a p pb s r σ η τ α lam ε ε₀ ε₁ γ M0 Mω MΩ M₀ M₁ cF tF Par ω Ω P X FT)
    {ξ : Fin 2 → ℝ} (hξ : ξ ∈ Par) {w : StepPhase r}
    (hw : w ∈ stepDomain r (s - 5 * σ) (η * r)) :
    ‖fderiv ℂ (H.Psi ξ) w‖ ≤ 8 * stepMF cF tF α σ ε / σ := by
  have h := (H.flow_pair_smooth hξ hξ hw).2.2.1
  have hM : M₀ ≤ stepMF cF tF α σ ε := by
    have := mul_nonneg H.hlam0 H.M₁_nonneg
    linarith [H.M_sum]
  exact h.trans (div_le_div_of_nonneg_right (by linarith) H.hσ.le)

/-- **The W5 smoothing dependency holds** (unmodified step, `bpW:w6:iter-lemma` step `il-tr`):
W5's `Ψ = H.hyp.core.Psi ξ` witnesses `W6StepSmooth`. -/
theorem w6StepSmooth_holds : W6StepSmooth := by
  intro a p pb s r σ η τ α lam ε ε₀ ε₁ γ M0 Mω MΩ Par ω Ω P X H _ ξ hξ
  exact ⟨H.hyp.core.Psi ξ, H.hyp.core.psi_differentiableOn hξ, fun w hw =>
    ⟨H.hyp.core.phi_eq_add_Psi hξ hw, H.hyp.core.psi_le_MF hξ hw,
      H.hyp.core.fderiv_psi_le_MF hξ hw⟩⟩

/-- **The W5 smoothing dependency holds** (modified step, constants `c^♮_F`, `t^♮`):
W5's `Ψ = H.hyp.core.Psi ξ` witnesses `W6StepSmoothMod`. -/
theorem w6StepSmoothMod_holds : W6StepSmoothMod := by
  intro a p pb s r σ η τ α β lam ε ε₀ ε₁ γ M0 Mω MΩ Par ω Ω P X H _ ξ hξ
  exact ⟨H.hyp.core.Psi ξ, H.hyp.core.psi_differentiableOn hξ, fun w hw =>
    ⟨H.hyp.core.phi_eq_add_Psi hξ hw, H.hyp.core.psi_le_MF hξ hw,
      H.hyp.core.fderiv_psi_le_MF hξ hw⟩⟩

end KAM.Wave
