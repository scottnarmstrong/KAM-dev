/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.KamStep.StepTheorem
public import KAM.Wave.KamStep.StepHypMod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# One KAM step, modified case (blueprint-W `bpW:w5:step`)

Off-frontier, source-faithful infrastructure (W5-STEP, item 6); the dependency graph is still being
built.

`stepTheoremMod_of_eps0_pos`: the clauses of `stepTheorem` for `StepHypMod` (modified divisors,
`P ∈ 𝒮_{p+1}`, `2β ≤ p+1-p₊`, `c♮_F`, `t♮`, `C♮₂`), through `StepHypMod.core`.
-/

@[expose] public noncomputable section

open Set

namespace KAM.Wave

open KAM

variable {a p pb s r σ η τ α β lam ε ε₀ ε₁ γ M0 Mω MΩ : ℝ} {Par : Set (Fin 2 → ℝ)}
  {ω : (Fin 2 → ℝ) → Fin 2 → ℝ} {Ω : (Fin 2 → ℝ) → ℕ+ → ℝ}
  {P : (Fin 2 → ℝ) → KamPhase → ℂ} {X : (Fin 2 → ℝ) → KamPhase → KamPhase}

/-- **One KAM step, modified case** (`bpW:w5:step`), conditional helper (assumes `0 < ε₀`). The solve
uses modified divisors; the new objects are those of `H.core` for the pair `(P, D_ρ ∘ X)`. The
hypothesis `hH` is that of clause (iv) (the blueprint's "whenever the same holds with `α`"). -/
theorem stepTheoremMod_of_eps0_pos
    (H : StepHypMod a p pb s r σ η τ α β lam ε ε₀ ε₁ γ M0 Mω MΩ Par ω Ω P X)
    (hH : HomMelnikov τ α Par ω Ω) [Fact (0 < r)] :
    -- (i)
    (∀ ξ ∈ Par, ∀ w ∈ stepDomain r (s - 5 * σ) (η * r),
      StepPhase.toK (H.core.Phi ξ w) ∈ kamDomain (s - 4 * σ) (2 * η * r)) ∧
    (∀ ξ (hξ : ξ ∈ Par), ∀ w ∈ stepDomain r (s - 5 * σ) (η * r),
      stepNfun H.hG H.core.hK0 (homOmega_le H.freq hξ) (ω ξ) (StepPhase.toK (H.core.Phi ξ w)) +
          P ξ (StepPhase.toK (H.core.Phi ξ w)) =
        stepNfun H.hG H.core.hKp (Ω := H.core.OmegaPlus ξ) (H.core.omegaPlus_bound hξ) (H.core.omegaPlus ξ)
          (StepPhase.toK w) + H.core.Pplus ξ w + H.core.a0 ξ) ∧
    (∀ ξ (hξ : ξ ∈ Par), ∀ w ∈ stepDomain r (s - 5 * σ) (η * r), ∀ W : StepPhase r,
      ((homDN H.hG H.core.hK0 (homOmega_le H.freq hξ) (ω ξ)
          (stepToHom (StepPhase.toK (H.core.Phi ξ w)))).comp stepToHom).comp (stepToKCLM r)
          (fderiv ℂ (H.core.Phi ξ) w W) +
        stepSympCLM (q := p) (q' := p) H.ha H.core.two_p r
          (stepEmbedCLM a p pb H.hpb r (stepXPS (H.X' ξ) r (H.core.Phi ξ w))) (fderiv ℂ (H.core.Phi ξ) w W) =
      ((homDN H.hG H.core.hK0 (homOmega_le H.freq hξ) (ω ξ)
          (stepToHom (StepPhase.toK w))).comp stepToHom).comp (stepToKCLM r) W +
        stepSympCLM (q := p) (q' := p) H.ha H.core.two_p r
          (stepEmbedCLM a p pb H.hpb r
            (stepFieldS H.ha H.hp H.hpb (homNhatTaylor_gen (H.core.R ξ)) r w)) W +
        stepSympCLM (q := p) (q' := p) H.ha H.core.two_p r
          (stepEmbedCLM a p pb H.hpb r (H.core.Xplus ξ w)) W) ∧
    (∀ ξ ∈ Par, ∀ w ∈ stepDomain r (s - 5 * σ) (η * r), ∀ W W' : StepPhase r,
      stepSympCLM (q := p) (q' := p) H.ha H.core.two_p r (fderiv ℂ (H.core.Phi ξ) w W)
          (fderiv ℂ (H.core.Phi ξ) w W') =
        stepSympCLM (q := p) (q' := p) H.ha H.core.two_p r W W') ∧
    (∀ ξ ∈ Par, ∀ w ∈ stepDomain r (s - 5 * σ) (η * r), ∀ k : Fin 2,
      H.core.Phi ξ (w + stepTauS r k) = H.core.Phi ξ w + stepTauS r k) ∧
    -- (ii)
    (∀ ξ ∈ Par, IsSmoothing (p := p) H.ha H.core.pb_pos (kamDomain (s - 5 * σ) (η * r))
      (fun w : KamPhase => H.core.Pplus ξ (StepPhase.ofK (r := r) w))
      (fun w : KamPhase => StepPhase.toK (H.core.Xplus ξ (StepPhase.ofK (r := r) w)))) ∧
    (∀ ξ ∈ Par, ∀ i : Fin 2, ∀ w ∈ kamDomain (s - 5 * σ) (η * r),
      H.core.Pplus ξ (StepPhase.ofK (r := r) (w + stepTau i)) = H.core.Pplus ξ (StepPhase.ofK (r := r) w)) ∧
    FamBound Par (kamDomain (s - 5 * σ) (η * r)) (η * r) lam
      (stepC2n τ * (ε ^ 2 / (α * σ ^ stepTn τ * η ^ 2) + η * ε))
      (fun ξ w => StepPhase.toK (H.core.Xplus ξ (StepPhase.ofK (r := r) w))) ∧
    -- (iii)
    (∀ ξ ∈ Par, ‖H.core.omegaPlus ξ - ω ξ‖ ≤ 6 * Real.pi * ε₀ ∧
      ∀ j : ℕ+, ((j : ℝ) + 2) ^ (pb - p) * |H.core.OmegaPlus ξ j - Ω ξ j| ≤ 3 * ε₀) ∧
    (∀ ξ ∈ Par, ∀ ζ ∈ Par,
      ‖(H.core.omegaPlus ξ - ω ξ) - (H.core.omegaPlus ζ - ω ζ)‖ ≤ 6 * Real.pi * ε₁ * ‖ξ - ζ‖ ∧
      ∀ j : ℕ+, ((j : ℝ) + 2) ^ (pb - p) *
        |(H.core.OmegaPlus ξ j - Ω ξ j) - (H.core.OmegaPlus ζ j - Ω ζ j)| ≤ 3 * ε₁ * ‖ξ - ζ‖) ∧
    (0 < lam → HomFreqHyp Par H.core.omegaPlus H.core.OmegaPlus (M0 + 3 * ε) (Mω + 6 * Real.pi * ε / lam)
      (MΩ + 3 * ε / lam)) ∧
    -- (iv)
    (∀ K α' : ℝ, 1 ≤ K → 6 * Real.pi * (1 + K) * (1 + K ^ τ) * ε ≤ α - α' →
      ∀ ξ ∈ Par, ∀ (k : Fin 2 → ℤ) (l : ℕ+ →₀ ℤ), (k, l) ∈ homZ → Fourier.modeSize k ≤ K →
        α' * (homJap l : ℝ) / waveA τ k ≤
          |homPairZ k (H.core.omegaPlus ξ) + homPairL l (H.core.OmegaPlus ξ)|) ∧
    -- (v)
    (stepM₀ τ σ α ε₀ + lam * stepM₁n τ σ α ε₀ ε₁ Mω MΩ ≤ stepMF (stepCFn τ) (stepTn τ) α σ ε) ∧
    (∀ ξ ∈ Par, ∀ ζ ∈ Par, ∀ w ∈ stepDomain r (s - 5 * σ) (η * r),
      ‖H.core.Phi ξ w - w‖ ≤ stepM₀ τ σ α ε₀ ∧
      ‖(H.core.Phi ξ w - w) - (H.core.Phi ζ w - w)‖ ≤ 2 * (stepM₁n τ σ α ε₀ ε₁ Mω MΩ * ‖ξ - ζ‖) ∧
      ‖fderiv ℂ (H.core.Phi ξ) w - ContinuousLinearMap.id ℂ _‖ ≤ 8 * stepM₀ τ σ α ε₀ / σ ∧
      ‖fderiv ℂ (H.core.Phi ξ) w - fderiv ℂ (H.core.Phi ζ) w‖ ≤
        16 * (stepM₁n τ σ α ε₀ ε₁ Mω MΩ * ‖ξ - ζ‖) / σ) :=
  stepTheoremCore H.core hH

end KAM.Wave
