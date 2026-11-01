/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.KamStep.StepConj
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The flow clauses of the KAM step (blueprint-W `bpW:w5:step` (i), (v))

Off-frontier, source-faithful infrastructure (W5-STEP); the dependency graph is still being built.

For `w ∈ D_+ = D(s-5σ, ηr)` and `ξ ∈ Π`: `Φ w ∈ D(s-4σ, 2ηr)` (`StepHyp.phi_mem`), the weak
conjugacy (`StepHyp.weakConj`), symplecticity (`StepHyp.phi_symplectic`), translation
equivariance (`StepHyp.phi_translate`) and the `λ`-bounds of the transformation
(`StepHyp.phi_bounds`).
-/

@[expose] public noncomputable section

open Set

namespace KAM.Wave

open KAM

variable {a p pb s r σ η τ α lam ε ε₀ ε₁ γ M0 Mω MΩ : ℝ} {Par : Set (Fin 2 → ℝ)}
  {ω : (Fin 2 → ℝ) → Fin 2 → ℝ} {Ω : (Fin 2 → ℝ) → ℕ+ → ℝ}
  {P : (Fin 2 → ℝ) → KamPhase → ℂ} {X : (Fin 2 → ℝ) → KamPhase → KamPhase}

namespace StepHyp

variable (H : StepHyp a p pb s r σ η τ α lam ε ε₀ ε₁ γ M0 Mω MΩ Par ω Ω P X) [Fact (0 < r)]

include H

theorem mf_lt : stepM₀ τ σ α ε₀ < σ / 4 := by
  have := H.mf_le_sigma
  linarith [H.hσ]

theorem Dplus_sub_small : stepDomain r (s - 5 * σ) (η * r) ⊆ stepDomain r (s - 3 * σ) (r / 4) :=
  stepDomain_mono' (by linarith [H.hσ]) (by have := H.hr; have := H.hη0; positivity)
    (by have := H.hr; nlinarith [H.hη])

theorem Dplus_sub_U : stepDomain r (s - 5 * σ) (η * r) ⊆ stepDomain r (s - 2 * σ) (r / 2) :=
  H.Dplus_sub_small.trans (stepDomain_mono' (by linarith [H.hσ]) (by have := H.hr; positivity)
    (by have := H.hr; linarith))

/-- The four bounds of the transformation (`stepFlow_bounds` for the pair `ξ, ζ`). -/
theorem flow_pair {ξ ζ : Fin 2 → ℝ} (hξ : ξ ∈ Par) (hζ : ζ ∈ Par) {w : StepPhase r}
    (hw : w ∈ stepDomain r (s - 5 * σ) (η * r)) :
    ‖H.Phi ξ w - w‖ ≤ stepM₀ τ σ α ε₀ ∧
      ‖(H.Phi ξ w - w) - (H.Phi ζ w - w)‖ ≤ 2 * (stepM₁ τ σ α ε₀ ε₁ Mω MΩ * ‖ξ - ζ‖) ∧
      ‖fderiv ℂ (H.Phi ξ) w - ContinuousLinearMap.id ℂ _‖ ≤ 8 * stepM₀ τ σ α ε₀ / σ ∧
      ‖fderiv ℂ (H.Phi ξ) w - fderiv ℂ (H.Phi ζ) w‖ ≤
        16 * (stepM₁ τ σ α ε₀ ε₁ Mω MΩ * ‖ξ - ζ‖) / σ := by
  have hN : 0 ≤ stepM₁ τ σ α ε₀ ε₁ Mω MΩ * ‖ξ - ζ‖ := mul_nonneg H.M₁_nonneg (norm_nonneg _)
  exact stepFlow_bounds H.ha H.hp H.hpb H.hσ H.hσ1 (by linarith [H.hσs, H.hσ])
    (H.F_field ξ hξ) (H.F_field ζ hζ) (H.F_sub ξ hξ ζ hζ) H.M₀_pos H.mf_le_sigma hN
    (H.Dplus_sub_small hw)

/-- `Φ(D_+) ⊆ D(s-4σ, 2ηr)`. -/
theorem phi_mem {ξ : Fin 2 → ℝ} (hξ : ξ ∈ Par) {w : StepPhase r}
    (hw : w ∈ stepDomain r (s - 5 * σ) (η * r)) :
    StepPhase.toK (H.Phi ξ w) ∈ kamDomain (s - 4 * σ) (2 * η * r) := by
  have h := (H.flow_pair hξ hξ hw).1
  have hmf : stepM₀ τ σ α ε₀ ≤ σ * η ^ 2 / 16 := by
    have := H.mf_small
    have h2 := H.M_sum
    have := mul_nonneg H.hlam0 H.M₁_nonneg
    linarith
  have := stepImage_mem (s := s) H.hr H.hσ H.hσ1 H.hη0 H.hη hmf (w := StepPhase.toK w)
    (W := StepPhase.toK (H.Phi ξ w - w)) hw (by rw [← stepPhase_norm_eq]; exact h)
  convert this using 1
  simp [StepPhase.toK]
  exact (add_sub_cancel w (H.Phi ξ w)).symm

theorem two_p : 0 ≤ p + p := by linarith [H.hp]

/-- **Weak conjugacy** (`bpW:w5:new-ham` (iii)), derivative form. -/
theorem weakConj {ξ : Fin 2 → ℝ} (hξ : ξ ∈ Par) {w : StepPhase r}
    (hw : w ∈ stepDomain r (s - 5 * σ) (η * r)) (W : StepPhase r) :
    ((homDN H.hG H.hK0 (homOmega_le H.freq hξ) (ω ξ) (stepToHom (StepPhase.toK (H.Phi ξ w)))).comp
        stepToHom).comp (stepToKCLM r) (fderiv ℂ (H.Phi ξ) w W) +
      stepSympCLM (q := p) (q' := p) H.ha H.two_p r
        (stepEmbedCLM a p pb H.hpb r (stepXPS (X ξ) r (H.Phi ξ w))) (fderiv ℂ (H.Phi ξ) w W) =
    ((homDN H.hG H.hK0 (homOmega_le H.freq hξ) (ω ξ) (stepToHom (StepPhase.toK w))).comp
        stepToHom).comp (stepToKCLM r) W +
      stepSympCLM (q := p) (q' := p) H.ha H.two_p r
        (stepEmbedCLM a p pb H.hpb r
          (stepFieldS H.ha H.hp H.hpb (homNhatTaylor_gen (H.R ξ)) r w)) W +
      stepSympCLM (q := p) (q' := p) H.ha H.two_p r
        (stepEmbedCLM a p pb H.hpb r (H.Xplus ξ w)) W := by
  have he := stepWeakConj (r := r) (σ := σ) (η := η) H.hG H.hK0 (homOmega_le H.freq hξ) (ω ξ)
    H.ha H.hp H.hpb H.hσ H.hσ1 H.hσs H.hη0 H.hη (H.hP ξ hξ) (H.R ξ) (H.FT ξ)
    (e₁ := 3 * ε₀) (by linarith [H.hε₀]) (H.R_field ξ hξ)
    (homNhat_fieldBound_gen H.ha H.hp H.hpb H.hr H.hs (H.R ξ) (H.R_field ξ hξ))
    (H.F_field ξ hξ) H.M₀_pos H.mf_le_sigma (H.a0 ξ) (fun w hw => H.equation hξ hw) hw W
  exact he

/-- **Symplecticity of `Φ`**. -/
theorem phi_symplectic {ξ : Fin 2 → ℝ} (hξ : ξ ∈ Par) {w : StepPhase r}
    (hw : w ∈ stepDomain r (s - 5 * σ) (η * r)) (W W' : StepPhase r) :
    stepSympCLM (q := p) (q' := p) H.ha H.two_p r (fderiv ℂ (H.Phi ξ) w W)
        (fderiv ℂ (H.Phi ξ) w W') =
      stepSympCLM (q := p) (q' := p) H.ha H.two_p r W W' :=
  stepFlow_symplectic H.ha H.hp H.hpb H.hσ H.hσ1 (by linarith [H.hσs, H.hσ]) (H.FT ξ)
    (H.F_field ξ hξ) H.M₀_pos H.mf_lt (H.Dplus_sub_U hw) ⟨by norm_num, le_rfl⟩ W W'

/-- **Translation equivariance of `Φ`**. -/
theorem phi_translate {ξ : Fin 2 → ℝ} (hξ : ξ ∈ Par) {w : StepPhase r}
    (hw : w ∈ stepDomain r (s - 5 * σ) (η * r)) (k : Fin 2) :
    H.Phi ξ (w + stepTauS r k) = H.Phi ξ w + stepTauS r k :=
  stepFlow_translate H.ha H.hp H.hpb H.hσ H.hσ1 (by linarith [H.hσs, H.hσ]) (H.FT ξ)
    (H.F_field ξ hξ) H.M₀_pos H.mf_lt (H.Dplus_sub_U hw) k ⟨by norm_num, le_rfl⟩

end StepHyp

end KAM.Wave
