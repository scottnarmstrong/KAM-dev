/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.KamStep.StepTheoremSrc
public import KAM.Wave.KamStep.StepFlowFam
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# W6: the smoothing of one step's transformation (blueprint `bpW:w6:iter-lemma`, step `il-tr`)

Off the frontier: source-faithful infrastructure used by several nodes. The dependency graph is
still being built. Blueprint label `bpW:w6:iter-lemma` (transformations), used by
`bpW:w6:convergence` (iii), (iv).

W5's `stepTheorem` (v) bounds `Φ - id` and `DΦ - I` in the norm `|·|_{p,r}` of `𝒫 = 𝒫^p`. The
blueprint's bounds `|Φ - id|_{p_+,r}` and `|DΦ - I|_{p → p_+, r}` are read off the construction
`Φ = φ¹` (the time-one map of the smoothing field `ι ∘ Z`, `StepCore.Phi`): on `D_+`,

* `Φ(w) = w + ι Ψ(w)` with `Ψ = StepCore.stepPsi` (`p_+`-representatives) and `|Ψ(w)|_r ≤ M₀`;
* `DΦ(w) = I + ι ∘ DΨ(w)` with `‖DΨ(w)‖ ≤ 8 M₀/σ`;
* `Φ` and `Ψ` are holomorphic on `D_+`.

Here `M₀` is the sup part of `M_F` (`M₀ + λ M₁ ≤ M_F`), so `|Φ - id|_{p_+,r} ≤ M_F`, which is the
sharper bound of step `f-flow` (`bpW:w5:flow`). The source-facing forms for `StepHypSrc` are
`StepHypSrc.phi_smooth` (objects of `H.hyp`, as in `stepTheorem`).
-/

@[expose] public noncomputable section

open Set Metric

namespace KAM.Wave

open KAM

variable {a p pb s r σ η τ α lam ε ε₀ ε₁ γ M0 Mω MΩ M₀ M₁ cF tF : ℝ}
  {Par : Set (Fin 2 → ℝ)}
  {ω : (Fin 2 → ℝ) → Fin 2 → ℝ} {Ω : (Fin 2 → ℝ) → ℕ+ → ℝ}
  {P : (Fin 2 → ℝ) → KamPhase → ℂ} {X : (Fin 2 → ℝ) → KamPhase → KamPhase}
  {FT : (Fin 2 → ℝ) → HomTaylor_gen a p pb (s - σ)}

theorem stepOne_mem_Icc : (1 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨by norm_num, le_rfl⟩

namespace StepCore

variable (H : StepCore a p pb s r σ η τ α lam ε ε₀ ε₁ γ M0 Mω MΩ M₀ M₁ cF tF Par ω Ω P X FT)
  [Fact (0 < r)]

/-- The smoothing displacement `Ψ` of the step (`p_+`-representatives): `Φ = id + ι ∘ Ψ` on
`D_+`. -/
def stepPsi (ξ : Fin 2 → ℝ) : StepPhase r → StepPhase r :=
  smoothDisp (stepEmbedCLM a p pb H.hpb r) (stepFieldS H.ha H.hp H.hpb (FT ξ) r) 1

include H

theorem flowHyp_core {ξ : Fin 2 → ℝ} (hξ : ξ ∈ Par) :
    FlowHyp (smoothField (stepEmbedCLM a p pb H.hpb r) (stepFieldS H.ha H.hp H.hpb (FT ξ) r))
      (stepDomain r (s - σ) r) (stepDomain r (s - 2 * σ) (r / 2)) M₀ (σ / 4) :=
  stepFlowHyp_concrete' (S := s) H.ha H.hp H.hpb (FT ξ) r H.hσ H.hσ1
    (by linarith [H.hσs, H.hσ]) le_rfl (H.F_field ξ hξ) H.M₀_pos H.mf_lt

theorem field_diff_core (ξ : Fin 2 → ℝ) :
    DifferentiableOn ℂ (stepFieldS H.ha H.hp H.hpb (FT ξ) r) (stepDomain r (s - σ) r) :=
  (stepFieldS_differentiableOn_theta H.ha H.hp H.hpb (FT ξ)).mono fun _ hz =>
    stepDomain_theta_mem le_rfl hz

theorem field_bound_core {ξ : Fin 2 → ℝ} (hξ : ξ ∈ Par) :
    ∀ z ∈ stepDomain r (s - σ) r, ‖stepFieldS H.ha H.hp H.hpb (FT ξ) r z‖ ≤ M₀ := fun _ hz =>
  stepFieldS_bound H.ha H.hp H.hpb (FT ξ) r (H.F_field ξ hξ) le_rfl hz

/-- `Φ(w) = w + ι Ψ(w)` on `D(s-2σ, r/2) ⊇ D_+`. -/
theorem phi_eq_add_psi {ξ : Fin 2 → ℝ} (hξ : ξ ∈ Par) {w : StepPhase r}
    (hw : w ∈ stepDomain r (s - 2 * σ) (r / 2)) :
    H.Phi ξ w = w + stepEmbedCLM a p pb H.hpb r (H.stepPsi ξ w) :=
  holoFlow_smooth_eq (H.flowHyp_core hξ) (H.field_diff_core ξ) hw stepOne_mem_Icc

/-- `|Ψ(w)|_{r} ≤ M₀` (the `p_+`-norm of `Φ(w) - w`). -/
theorem norm_psi_le {ξ : Fin 2 → ℝ} (hξ : ξ ∈ Par) {w : StepPhase r}
    (hw : w ∈ stepDomain r (s - 2 * σ) (r / 2)) : ‖H.stepPsi ξ w‖ ≤ M₀ :=
  flowII_disp (H.flowHyp_core hξ) (H.field_bound_core hξ) hw stepOne_mem_Icc

/-- `Ψ` is holomorphic on `D(s-2σ, r/2)`. -/
theorem psi_differentiableOn {ξ : Fin 2 → ℝ} (hξ : ξ ∈ Par) :
    DifferentiableOn ℂ (H.stepPsi ξ) (stepDomain r (s - 2 * σ) (r / 2)) :=
  differentiableOn_smoothDisp (H.flowHyp_core hξ) (H.field_diff_core ξ) (H.field_bound_core hξ)
    stepOne_mem_Icc

/-- `Φ` is holomorphic on `D(s-2σ, r/2)`. -/
theorem phi_differentiableOn {ξ : Fin 2 → ℝ} (hξ : ξ ∈ Par) :
    DifferentiableOn ℂ (H.Phi ξ) (stepDomain r (s - 2 * σ) (r / 2)) :=
  holomorphicOn_holoFlow (H.flowHyp_core hξ) stepOne_mem_Icc

/-- `DΦ(w) = I + ι ∘ DΨ(w)`. -/
theorem fderiv_phi_eq {ξ : Fin 2 → ℝ} (hξ : ξ ∈ Par) {w : StepPhase r}
    (hw : w ∈ stepDomain r (s - 2 * σ) (r / 2)) :
    fderiv ℂ (H.Phi ξ) w =
      ContinuousLinearMap.id ℂ _ + (stepEmbedCLM a p pb H.hpb r).comp (fderiv ℂ (H.stepPsi ξ) w) :=
  fderiv_holoFlow_smooth (H.flowHyp_core hξ) (H.field_diff_core ξ) (H.field_bound_core hξ) hw
    stepOne_mem_Icc

/-- `‖DΨ(w)‖ ≤ 8 M₀/σ` on `D_+` (the bound `|DΦ - I|_{p → p_+, r}`). -/
theorem norm_fderiv_psi_le {ξ : Fin 2 → ℝ} (hξ : ξ ∈ Par) {w : StepPhase r}
    (hw : w ∈ stepDomain r (s - 5 * σ) (η * r)) : ‖fderiv ℂ (H.stepPsi ξ) w‖ ≤ 8 * M₀ / σ := by
  have hball := stepDomain_U_margin H.hσ H.hσ1 (by linarith [H.hσs, H.hσ]) (H.Dplus_sub_small hw)
  have := flowII_deriv (H.flowHyp_core hξ) (H.field_diff_core ξ) (H.field_bound_core hξ)
    (by have := H.hσ; positivity : (0 : ℝ) < σ / 8) hball stepOne_mem_Icc
  calc _ ≤ M₀ / (σ / 8) := this
    _ = 8 * M₀ / σ := by field_simp

omit [Fact (0 < r)] in
theorem M₀_le_MF : M₀ ≤ stepMF cF tF α σ ε := by
  have := mul_nonneg H.hlam0 H.M₁_nonneg
  linarith [H.M_sum]

end StepCore

namespace StepHypSrc

variable (H : StepHypSrc a p pb s r σ η τ α lam ε ε₀ ε₁ γ M0 Mω MΩ Par ω Ω P X) [Fact (0 < r)]
include H

/-- **The smoothing of `Φ`** (`bpW:w5:step` (v) with the sharper sup bound of step `f-flow`; used by
`bpW:w6:iter-lemma`, step `il-tr`): on `D_+ = D(s-5σ, ηr)`, for `ξ ∈ Π`,
`Φ(w) = w + ι Ψ(w)`, `|Ψ(w)|_r ≤ M_F`, `DΦ(w) = I + ι ∘ DΨ(w)`, `‖DΨ(w)‖ ≤ 8 M_F/σ`, and `Φ`, `Ψ`
are holomorphic on an open neighbourhood `D(s - 2σ, r/2)` of `D_+`. -/
theorem phi_smooth {ξ : Fin 2 → ℝ} (hξ : ξ ∈ Par) :
    stepDomain r (s - 5 * σ) (η * r) ⊆ stepDomain r (s - 2 * σ) (r / 2) ∧
    DifferentiableOn ℂ (H.hyp.core.Phi ξ) (stepDomain r (s - 2 * σ) (r / 2)) ∧
    DifferentiableOn ℂ (H.hyp.core.stepPsi ξ) (stepDomain r (s - 2 * σ) (r / 2)) ∧
    ∀ w ∈ stepDomain r (s - 5 * σ) (η * r),
      H.hyp.core.Phi ξ w = w + stepEmbedCLM a p pb H.hpb r (H.hyp.core.stepPsi ξ w) ∧
      ‖H.hyp.core.stepPsi ξ w‖ ≤ stepMF (stepCF τ) (stepExpT τ) α σ ε ∧
      fderiv ℂ (H.hyp.core.Phi ξ) w = ContinuousLinearMap.id ℂ _ +
        (stepEmbedCLM a p pb H.hpb r).comp (fderiv ℂ (H.hyp.core.stepPsi ξ) w) ∧
      ‖fderiv ℂ (H.hyp.core.stepPsi ξ) w‖ ≤ 8 * stepMF (stepCF τ) (stepExpT τ) α σ ε / σ := by
  have hMF := H.hyp.core.M₀_le_MF
  refine ⟨H.hyp.core.Dplus_sub_U, H.hyp.core.phi_differentiableOn hξ, H.hyp.core.psi_differentiableOn hξ,
    fun w hw => ⟨H.hyp.core.phi_eq_add_psi hξ (H.hyp.core.Dplus_sub_U hw),
      (H.hyp.core.norm_psi_le hξ (H.hyp.core.Dplus_sub_U hw)).trans hMF, H.hyp.core.fderiv_phi_eq hξ (H.hyp.core.Dplus_sub_U hw),
      (H.hyp.core.norm_fderiv_psi_le hξ hw).trans ?_⟩⟩
  exact div_le_div_of_nonneg_right (by linarith) H.hyp.core.hσ.le

end StepHypSrc

namespace StepHypModSrc

variable {β : ℝ}
  (H : StepHypModSrc a p pb s r σ η τ α β lam ε ε₀ ε₁ γ M0 Mω MΩ Par ω Ω P X) [Fact (0 < r)]
include H

/-- **The smoothing of `Φ`, modified case** (`bpW:w5:step` (v) with the sharper sup bound of step
`f-flow`, used by `bpW:w6:prep-step` (iii)): on `D_+`, for `ξ ∈ Π`, `Φ(w) = w + ι Ψ(w)`,
`|Ψ(w)|_r ≤ M_F` (constants `c^♮_F`, `t^♮`), `DΦ(w) = I + ι ∘ DΨ(w)`, `‖DΨ(w)‖ ≤ 8 M_F/σ`, and `Φ`,
`Ψ` are holomorphic on `D(s - 2σ, r/2)`. -/
theorem phi_smooth {ξ : Fin 2 → ℝ} (hξ : ξ ∈ Par) :
    stepDomain r (s - 5 * σ) (η * r) ⊆ stepDomain r (s - 2 * σ) (r / 2) ∧
    DifferentiableOn ℂ (H.hyp.core.Phi ξ) (stepDomain r (s - 2 * σ) (r / 2)) ∧
    DifferentiableOn ℂ (H.hyp.core.stepPsi ξ) (stepDomain r (s - 2 * σ) (r / 2)) ∧
    ∀ w ∈ stepDomain r (s - 5 * σ) (η * r),
      H.hyp.core.Phi ξ w = w + stepEmbedCLM a p pb H.hpb r (H.hyp.core.stepPsi ξ w) ∧
      ‖H.hyp.core.stepPsi ξ w‖ ≤ stepMF (stepCFn τ) (stepTn τ) α σ ε ∧
      fderiv ℂ (H.hyp.core.Phi ξ) w = ContinuousLinearMap.id ℂ _ +
        (stepEmbedCLM a p pb H.hpb r).comp (fderiv ℂ (H.hyp.core.stepPsi ξ) w) ∧
      ‖fderiv ℂ (H.hyp.core.stepPsi ξ) w‖ ≤ 8 * stepMF (stepCFn τ) (stepTn τ) α σ ε / σ := by
  have hMF := H.hyp.core.M₀_le_MF
  refine ⟨H.hyp.core.Dplus_sub_U, H.hyp.core.phi_differentiableOn hξ,
    H.hyp.core.psi_differentiableOn hξ,
    fun w hw => ⟨H.hyp.core.phi_eq_add_psi hξ (H.hyp.core.Dplus_sub_U hw),
      (H.hyp.core.norm_psi_le hξ (H.hyp.core.Dplus_sub_U hw)).trans hMF,
      H.hyp.core.fderiv_phi_eq hξ (H.hyp.core.Dplus_sub_U hw),
      (H.hyp.core.norm_fderiv_psi_le hξ hw).trans ?_⟩⟩
  exact div_le_div_of_nonneg_right (by linarith) H.hyp.core.hσ.le

end StepHypModSrc

end KAM.Wave
