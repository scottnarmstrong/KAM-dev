/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.KamStep.StepClauses
public import KAM.Wave.KamStep.StepHyp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# One KAM step, non-modified case (blueprint-W `bpW:w5:step`)

Off-frontier, source-faithful infrastructure (W5-STEP); the dependency graph is still being built.

`stepTheorem`: under `StepHyp` (step data and the smallness condition) there are the objects
`Φ = StepHyp.Phi`, `P_+ = StepHyp.Pplus`, `X_+ = StepHyp.Xplus`, `ω_+ = StepHyp.omegaPlus`,
`Ω_+ = StepHyp.OmegaPlus`, `â₀ = StepHyp.a0` with the clauses

* (i) `Φ(D_+) ⊆ D(s-4σ, 2ηr)`, `H∘Φ = N_+ + P_+ + â₀`, the weak conjugacy in derivative form,
  symplecticity of `Φ`, `Φ(w + τ_k) = Φ(w) + τ_k`;
* (ii) `P_+ ∈ 𝒮_{p_+}(D_+)`, periodic, `|X_{P_+}|^λ ≤ C₂(ε²/(α σ^t η²) + η ε)`;
* (iii) the frequency corrections (`λ`-norms read as conjunctions of the sup and the Lipschitz
bound,
  with `ε₀ + λ ε₁ ≤ ε`), and `(ω_+, Ω_+)` satisfies the frequency hypothesis when `λ > 0`;
* (iv) the divisor bounds;
* (v) `|Φ - id|`, `|DΦ - I|` (sup and Lipschitz parts, `M₀ + λ M₁ ≤ M_F`).

Not included (open, recorded in the handoff): the reality clauses (`Φ` real on real points, `P_+`
real) and `DΦ(w)(𝒫^{p_+}) = 𝒫^{p_+}`; the Riesz representation of `DN` by the unbounded field `X_N`.
-/

@[expose] public noncomputable section

open Set

namespace KAM.Wave

open KAM

variable {a p pb s r σ η τ α lam ε ε₀ ε₁ γ M0 Mω MΩ M₀ M₁ cF tF : ℝ} {Par : Set (Fin 2 → ℝ)}
  {ω : (Fin 2 → ℝ) → Fin 2 → ℝ} {Ω : (Fin 2 → ℝ) → ℕ+ → ℝ}
  {P : (Fin 2 → ℝ) → KamPhase → ℂ} {X : (Fin 2 → ℝ) → KamPhase → KamPhase}
  {FT : (Fin 2 → ℝ) → HomTaylor_gen a p pb (s - σ)}

/-- **One KAM step** (`bpW:w5:step`) for an abstract `StepCore`. -/
theorem stepTheoremCore (H : StepCore a p pb s r σ η τ α lam ε ε₀ ε₁ γ M0 Mω MΩ M₀ M₁ cF tF Par ω Ω
  P X FT)
    [Fact (0 < r)] :
    -- (i)
    (∀ ξ ∈ Par, ∀ w ∈ stepDomain r (s - 5 * σ) (η * r),
      StepPhase.toK (H.Phi ξ w) ∈ kamDomain (s - 4 * σ) (2 * η * r)) ∧
    (∀ ξ (hξ : ξ ∈ Par), ∀ w ∈ stepDomain r (s - 5 * σ) (η * r),
      stepNfun H.hG H.hK0 (homOmega_le H.freq hξ) (ω ξ) (StepPhase.toK (H.Phi ξ w)) +
          P ξ (StepPhase.toK (H.Phi ξ w)) =
        stepNfun H.hG H.hKp (Ω := H.OmegaPlus ξ) (H.omegaPlus_bound hξ) (H.omegaPlus ξ)
          (StepPhase.toK w) + H.Pplus ξ w + H.a0 ξ) ∧
    (∀ ξ (hξ : ξ ∈ Par), ∀ w ∈ stepDomain r (s - 5 * σ) (η * r), ∀ W : StepPhase r,
      ((homDN H.hG H.hK0 (homOmega_le H.freq hξ) (ω ξ)
          (stepToHom (StepPhase.toK (H.Phi ξ w)))).comp stepToHom).comp (stepToKCLM r)
          (fderiv ℂ (H.Phi ξ) w W) +
        stepSympCLM (q := p) (q' := p) H.ha H.two_p r
          (stepEmbedCLM a p pb H.hpb r (stepXPS (X ξ) r (H.Phi ξ w))) (fderiv ℂ (H.Phi ξ) w W) =
      ((homDN H.hG H.hK0 (homOmega_le H.freq hξ) (ω ξ)
          (stepToHom (StepPhase.toK w))).comp stepToHom).comp (stepToKCLM r) W +
        stepSympCLM (q := p) (q' := p) H.ha H.two_p r
          (stepEmbedCLM a p pb H.hpb r
            (stepFieldS H.ha H.hp H.hpb (homNhatTaylor_gen (H.R ξ)) r w)) W +
        stepSympCLM (q := p) (q' := p) H.ha H.two_p r
          (stepEmbedCLM a p pb H.hpb r (H.Xplus ξ w)) W) ∧
    (∀ ξ ∈ Par, ∀ w ∈ stepDomain r (s - 5 * σ) (η * r), ∀ W W' : StepPhase r,
      stepSympCLM (q := p) (q' := p) H.ha H.two_p r (fderiv ℂ (H.Phi ξ) w W)
          (fderiv ℂ (H.Phi ξ) w W') =
        stepSympCLM (q := p) (q' := p) H.ha H.two_p r W W') ∧
    (∀ ξ ∈ Par, ∀ w ∈ stepDomain r (s - 5 * σ) (η * r), ∀ k : Fin 2,
      H.Phi ξ (w + stepTauS r k) = H.Phi ξ w + stepTauS r k) ∧
    -- (ii)
    (∀ ξ ∈ Par, IsSmoothing (p := p) H.ha H.pb_pos (kamDomain (s - 5 * σ) (η * r))
      (fun w : KamPhase => H.Pplus ξ (StepPhase.ofK (r := r) w))
      (fun w : KamPhase => StepPhase.toK (H.Xplus ξ (StepPhase.ofK (r := r) w)))) ∧
    (∀ ξ ∈ Par, ∀ i : Fin 2, ∀ w ∈ kamDomain (s - 5 * σ) (η * r),
      H.Pplus ξ (StepPhase.ofK (r := r) (w + stepTau i)) = H.Pplus ξ (StepPhase.ofK (r := r) w)) ∧
    FamBound Par (kamDomain (s - 5 * σ) (η * r)) (η * r) lam
      ((896 + 168 * cF) * (ε ^ 2 / (α * σ ^ tF * η ^ 2) + η * ε))
      (fun ξ w => StepPhase.toK (H.Xplus ξ (StepPhase.ofK (r := r) w))) ∧
    -- (iii)
    (∀ ξ ∈ Par, ‖H.omegaPlus ξ - ω ξ‖ ≤ 6 * Real.pi * ε₀ ∧
      ∀ j : ℕ+, ((j : ℝ) + 2) ^ (pb - p) * |H.OmegaPlus ξ j - Ω ξ j| ≤ 3 * ε₀) ∧
    (∀ ξ ∈ Par, ∀ ζ ∈ Par,
      ‖(H.omegaPlus ξ - ω ξ) - (H.omegaPlus ζ - ω ζ)‖ ≤ 6 * Real.pi * ε₁ * ‖ξ - ζ‖ ∧
      ∀ j : ℕ+, ((j : ℝ) + 2) ^ (pb - p) *
        |(H.OmegaPlus ξ j - Ω ξ j) - (H.OmegaPlus ζ j - Ω ζ j)| ≤ 3 * ε₁ * ‖ξ - ζ‖) ∧
    (0 < lam → HomFreqHyp Par H.omegaPlus H.OmegaPlus (M0 + 3 * ε) (Mω + 6 * Real.pi * ε / lam)
      (MΩ + 3 * ε / lam)) ∧
    -- (iv)
    (HomMelnikov τ α Par ω Ω → ∀ K α' : ℝ, 1 ≤ K → 6 * Real.pi * (1 + K) * (1 + K ^ τ) * ε ≤ α - α'
      →
      ∀ ξ ∈ Par, ∀ (k : Fin 2 → ℤ) (l : ℕ+ →₀ ℤ), (k, l) ∈ homZ → Fourier.modeSize k ≤ K →
        α' * (homJap l : ℝ) / waveA τ k ≤
          |homPairZ k (H.omegaPlus ξ) + homPairL l (H.OmegaPlus ξ)|) ∧
    -- (v)
    (M₀ + lam * M₁ ≤ stepMF (cF) (tF) α σ ε) ∧
    (∀ ξ ∈ Par, ∀ ζ ∈ Par, ∀ w ∈ stepDomain r (s - 5 * σ) (η * r),
      ‖H.Phi ξ w - w‖ ≤ M₀ ∧
      ‖(H.Phi ξ w - w) - (H.Phi ζ w - w)‖ ≤ 2 * (M₁ * ‖ξ - ζ‖) ∧
      ‖fderiv ℂ (H.Phi ξ) w - ContinuousLinearMap.id ℂ _‖ ≤ 8 * M₀ / σ ∧
      ‖fderiv ℂ (H.Phi ξ) w - fderiv ℂ (H.Phi ζ) w‖ ≤
        16 * (M₁ * ‖ξ - ζ‖) / σ) :=
  ⟨fun ξ hξ w hw => H.phi_mem hξ hw, fun ξ hξ w hw => H.conj_eq hξ hw,
    fun ξ hξ w hw W => H.weakConj hξ hw W, fun ξ hξ w hw W W' => H.phi_symplectic hξ hw W W',
    fun ξ hξ w hw k => H.phi_translate hξ hw k, fun ξ hξ => H.Pplus_smoothing hξ,
    fun ξ hξ i w hw => H.Pplus_periodic hξ i hw, H.Xplus_fam,
    fun ξ hξ => ⟨H.freq_sup hξ, H.tail_sup hξ⟩,
    fun ξ hξ ζ hζ => ⟨H.freq_lip hξ hζ, H.tail_lip hξ hζ⟩, fun hl => H.freq_hyp hl,
    fun hH K α' hK hα' ξ hξ k l hkl hkK => H.divisors hH hK hα' hξ hkl hkK, H.M_sum,
    fun ξ hξ ζ hζ w hw => H.flow_pair hξ hζ hw⟩


namespace StepHyp

/-- The clauses of **one KAM step** (`bpW:w5:step`), non-modified case, conditional helper: it
  assumes `0 < ε₀`, which is not
a premise of the blueprint (see `stepTheorem`). -/
def Conclusion (H : StepHyp a p pb s r σ η τ α lam ε ε₀ ε₁ γ M0 Mω MΩ Par ω Ω P X)
    [Fact (0 < r)] : Prop :=    -- (i)
    (∀ ξ ∈ Par, ∀ w ∈ stepDomain r (s - 5 * σ) (η * r),
      StepPhase.toK (H.core.Phi ξ w) ∈ kamDomain (s - 4 * σ) (2 * η * r)) ∧
    (∀ ξ (hξ : ξ ∈ Par), ∀ w ∈ stepDomain r (s - 5 * σ) (η * r),
      stepNfun H.hG H.core.hK0 (homOmega_le H.freq hξ) (ω ξ) (StepPhase.toK (H.core.Phi ξ w)) +
          P ξ (StepPhase.toK (H.core.Phi ξ w)) =
        stepNfun H.hG H.core.hKp (Ω := H.core.OmegaPlus ξ) (H.core.omegaPlus_bound hξ)
          (H.core.omegaPlus ξ)
          (StepPhase.toK w) + H.core.Pplus ξ w + H.core.a0 ξ) ∧
    (∀ ξ (hξ : ξ ∈ Par), ∀ w ∈ stepDomain r (s - 5 * σ) (η * r), ∀ W : StepPhase r,
      ((homDN H.hG H.core.hK0 (homOmega_le H.freq hξ) (ω ξ)
          (stepToHom (StepPhase.toK (H.core.Phi ξ w)))).comp stepToHom).comp (stepToKCLM r)
          (fderiv ℂ (H.core.Phi ξ) w W) +
        stepSympCLM (q := p) (q' := p) H.ha H.core.two_p r
          (stepEmbedCLM a p pb H.hpb r (stepXPS (X ξ) r (H.core.Phi ξ w))) (fderiv ℂ (H.core.Phi ξ)
            w W) =
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
      H.core.Pplus ξ (StepPhase.ofK (r := r) (w + stepTau i)) = H.core.Pplus ξ (StepPhase.ofK (r :=
        r) w)) ∧
    FamBound Par (kamDomain (s - 5 * σ) (η * r)) (η * r) lam
      (stepC2 τ * (ε ^ 2 / (α * σ ^ stepExpT τ * η ^ 2) + η * ε))
      (fun ξ w => StepPhase.toK (H.core.Xplus ξ (StepPhase.ofK (r := r) w))) ∧
    -- (iii)
    (∀ ξ ∈ Par, ‖H.core.omegaPlus ξ - ω ξ‖ ≤ 6 * Real.pi * ε₀ ∧
      ∀ j : ℕ+, ((j : ℝ) + 2) ^ (pb - p) * |H.core.OmegaPlus ξ j - Ω ξ j| ≤ 3 * ε₀) ∧
    (∀ ξ ∈ Par, ∀ ζ ∈ Par,
      ‖(H.core.omegaPlus ξ - ω ξ) - (H.core.omegaPlus ζ - ω ζ)‖ ≤ 6 * Real.pi * ε₁ * ‖ξ - ζ‖ ∧
      ∀ j : ℕ+, ((j : ℝ) + 2) ^ (pb - p) *
        |(H.core.OmegaPlus ξ j - Ω ξ j) - (H.core.OmegaPlus ζ j - Ω ζ j)| ≤ 3 * ε₁ * ‖ξ - ζ‖) ∧
    (0 < lam → HomFreqHyp Par H.core.omegaPlus H.core.OmegaPlus (M0 + 3 * ε) (Mω + 6 * Real.pi * ε
      / lam)
      (MΩ + 3 * ε / lam)) ∧
    -- (iv)
    (HomMelnikov τ α Par ω Ω → ∀ K α' : ℝ, 1 ≤ K → 6 * Real.pi * (1 + K) * (1 + K ^ τ) * ε ≤ α - α'
      →
      ∀ ξ ∈ Par, ∀ (k : Fin 2 → ℤ) (l : ℕ+ →₀ ℤ), (k, l) ∈ homZ → Fourier.modeSize k ≤ K →
        α' * (homJap l : ℝ) / waveA τ k ≤
          |homPairZ k (H.core.omegaPlus ξ) + homPairL l (H.core.OmegaPlus ξ)|) ∧
    -- (v)
    (stepM₀ τ σ α ε₀ + lam * stepM₁ τ σ α ε₀ ε₁ Mω MΩ ≤ stepMF (stepCF τ) (stepExpT τ) α σ ε) ∧
    (∀ ξ ∈ Par, ∀ ζ ∈ Par, ∀ w ∈ stepDomain r (s - 5 * σ) (η * r),
      ‖H.core.Phi ξ w - w‖ ≤ stepM₀ τ σ α ε₀ ∧
      ‖(H.core.Phi ξ w - w) - (H.core.Phi ζ w - w)‖ ≤ 2 * (stepM₁ τ σ α ε₀ ε₁ Mω MΩ * ‖ξ - ζ‖) ∧
      ‖fderiv ℂ (H.core.Phi ξ) w - ContinuousLinearMap.id ℂ _‖ ≤ 8 * stepM₀ τ σ α ε₀ / σ ∧
      ‖fderiv ℂ (H.core.Phi ξ) w - fderiv ℂ (H.core.Phi ζ) w‖ ≤
        16 * (stepM₁ τ σ α ε₀ ε₁ Mω MΩ * ‖ξ - ζ‖) / σ)

end StepHyp

/-- Conditional helper (`0 < ε₀`). -/
theorem stepTheorem_of_eps0_pos (H : StepHyp a p pb s r σ η τ α lam ε ε₀ ε₁ γ M0 Mω MΩ Par ω Ω P X)
    [Fact (0 < r)] : H.Conclusion :=
  stepTheoremCore H.core

end KAM.Wave
