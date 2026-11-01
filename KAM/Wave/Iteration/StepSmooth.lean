/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.KamStep.StepTheoremSrc
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# W6: the smoothing of one step's transformation — W5 dependency (blueprint `bpW:w6:iter-lemma`)

Off the frontier: source-faithful infrastructure used by several nodes. The dependency graph is
still being built. Blueprint label `bpW:w6:iter-lemma` (step `il-tr`), used by
`bpW:w6:convergence` (iii), (iv), `bpW:w6:invariance`, `bpW:w6:prep-step` (iii), `bpW:w6:tori`.

W5's `stepTheorem` (v) bounds `Φ - id` and `DΦ - I` only in the ambient norm `|·|_{p,r}`. The
blueprint's bounds `|Φ - id|_{p_+,r} ≤ M_F` (sharp sup bound of step `f-flow`) and
`|DΦ - I|_{p → p_+, r} ≤ 8 M_F/σ` are being added to W5 (branch `inp-w5aa`, the smoothing
displacement `Ψ`, `Φ = id + ι Ψ`). Per the orchestrator's ruling, W6 does not reprove them: they are
the **named W5 dependencies** `W6StepSmooth` (unmodified step) and `W6StepSmoothMod` (modified
step),
and every W6 result that uses them is a conditional helper (suffix `_of_stepSmooth`), to be
discharged by one line once `inp-w5aa` lands.

* `W6StepSmooth`, `W6StepSmoothMod`: on `D_+ = D(s-5σ, ηr)`, for `ξ ∈ Π`, there is `Ψ` holomorphic
  on `D_+` with `Φ(w) = w + ι Ψ(w)`, `|Ψ(w)|_{p_+,r} ≤ M_F`, `‖DΨ(w)‖_{p → p_+} ≤ 8 M_F/σ`;
* `StepHypSrc.w6Psi`, `StepHypModSrc.w6Psi`: a choice of `Ψ`;
* `StepHypSrc.phi_smooth_of`, `StepHypModSrc.phi_smooth_of`: consequences used by W6 (`Φ`
  holomorphic on `D_+` and `DΦ = I + ι ∘ DΨ`, by plain calculus from `Φ = id + ι ∘ Ψ` on the open
  `D_+`).
-/

@[expose] public noncomputable section

open Set Metric Filter Topology

namespace KAM.Wave

open KAM

/-- **W5 dependency** (unmodified step; being added to W5 on `inp-w5aa`): the smoothing
displacement of `Φ = H.hyp.core.Phi ξ` with the blueprint's `p_+` bounds. -/
def W6StepSmooth : Prop :=
  ∀ (a p pb s r σ η τ α lam ε ε₀ ε₁ γ M0 Mω MΩ : ℝ) (Par : Set (Fin 2 → ℝ))
    (ω : (Fin 2 → ℝ) → Fin 2 → ℝ) (Ω : (Fin 2 → ℝ) → ℕ+ → ℝ)
    (P : (Fin 2 → ℝ) → KamPhase → ℂ) (X : (Fin 2 → ℝ) → KamPhase → KamPhase)
    (H : StepHypSrc a p pb s r σ η τ α lam ε ε₀ ε₁ γ M0 Mω MΩ Par ω Ω P X) (_ : Fact (0 < r))
    (ξ : Fin 2 → ℝ), ξ ∈ Par → ∃ Ψ : StepPhase r → StepPhase r,
      DifferentiableOn ℂ Ψ (stepDomain r (s - 5 * σ) (η * r)) ∧
      ∀ w ∈ stepDomain r (s - 5 * σ) (η * r),
        H.hyp.core.Phi ξ w = w + stepEmbedCLM a p pb H.hpb r (Ψ w) ∧
        ‖Ψ w‖ ≤ stepMF (stepCF τ) (stepExpT τ) α σ ε ∧
        ‖fderiv ℂ Ψ w‖ ≤ 8 * stepMF (stepCF τ) (stepExpT τ) α σ ε / σ

/-- **W5 dependency** (modified step; being added to W5 on `inp-w5aa`): the smoothing
displacement of `Φ = H.hyp.core.Phi ξ` with the blueprint's `p_+` bounds (constants `c^♮_F`,
`t^♮`). -/
def W6StepSmoothMod : Prop :=
  ∀ (a p pb s r σ η τ α β lam ε ε₀ ε₁ γ M0 Mω MΩ : ℝ) (Par : Set (Fin 2 → ℝ))
    (ω : (Fin 2 → ℝ) → Fin 2 → ℝ) (Ω : (Fin 2 → ℝ) → ℕ+ → ℝ)
    (P : (Fin 2 → ℝ) → KamPhase → ℂ) (X : (Fin 2 → ℝ) → KamPhase → KamPhase)
    (H : StepHypModSrc a p pb s r σ η τ α β lam ε ε₀ ε₁ γ M0 Mω MΩ Par ω Ω P X)
    (_ : Fact (0 < r)) (ξ : Fin 2 → ℝ), ξ ∈ Par → ∃ Ψ : StepPhase r → StepPhase r,
      DifferentiableOn ℂ Ψ (stepDomain r (s - 5 * σ) (η * r)) ∧
      ∀ w ∈ stepDomain r (s - 5 * σ) (η * r),
        H.hyp.core.Phi ξ w = w + stepEmbedCLM a p pb H.hpb r (Ψ w) ∧
        ‖Ψ w‖ ≤ stepMF (stepCFn τ) (stepTn τ) α σ ε ∧
        ‖fderiv ℂ Ψ w‖ ≤ 8 * stepMF (stepCFn τ) (stepTn τ) α σ ε / σ

/-- Calculus: if `Φ = id + ι ∘ Ψ` on an open set `U` and `Ψ` is holomorphic there, then `Φ` is
holomorphic on `U` and `DΦ = I + ι ∘ DΨ`. -/
theorem w6_phi_of_psi {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [NormedAddCommGroup G] [NormedSpace ℂ G] {ι : G →L[ℂ] F} {Φ : F → F} {Ψ : F → G} {U : Set F}
    (hU : IsOpen U) (hΨ : DifferentiableOn ℂ Ψ U) (he : ∀ w ∈ U, Φ w = w + ι (Ψ w)) :
    DifferentiableOn ℂ Φ U ∧
      ∀ w ∈ U, fderiv ℂ Φ w = ContinuousLinearMap.id ℂ F + ι.comp (fderiv ℂ Ψ w) := by
  have key : ∀ w ∈ U, HasFDerivAt Φ (ContinuousLinearMap.id ℂ F + ι.comp (fderiv ℂ Ψ w)) w := by
    intro w hw
    have hev : (fun x => x + ι (Ψ x)) =ᶠ[𝓝 w] Φ :=
      Filter.eventually_of_mem (hU.mem_nhds hw) fun x hx => (he x hx).symm
    have hd := (hΨ.differentiableAt (hU.mem_nhds hw)).hasFDerivAt
    exact ((hasFDerivAt_id w).add (ι.hasFDerivAt.comp w hd)).congr_of_eventuallyEq hev.symm
  exact ⟨fun w hw => (key w hw).differentiableAt.differentiableWithinAt,
    fun w hw => (key w hw).fderiv⟩

variable {a p pb s r σ η τ α lam ε ε₀ ε₁ γ M0 Mω MΩ : ℝ}
  {Par : Set (Fin 2 → ℝ)}
  {ω : (Fin 2 → ℝ) → Fin 2 → ℝ} {Ω : (Fin 2 → ℝ) → ℕ+ → ℝ}
  {P : (Fin 2 → ℝ) → KamPhase → ℂ} {X : (Fin 2 → ℝ) → KamPhase → KamPhase}

namespace StepHypSrc

/-- A choice of the smoothing displacement `Ψ` (from the dependency `W6StepSmooth`, `0` if it
is not available). -/
def w6Psi (H : StepHypSrc a p pb s r σ η τ α lam ε ε₀ ε₁ γ M0 Mω MΩ Par ω Ω P X)
    [Fact (0 < r)] (ξ : Fin 2 → ℝ) : StepPhase r → StepPhase r :=
  open Classical in
  if h : W6StepSmooth ∧ ξ ∈ Par then
    (h.1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H inferInstance ξ h.2).choose
  else fun _ => 0

/-- **The smoothing of `Φ`** (conditional on the W5 dependency `W6StepSmooth`): on `D_+`, for
`ξ ∈ Π`, `Φ` and `Ψ` are holomorphic, `Φ(w) = w + ι Ψ(w)`, `|Ψ(w)|_r ≤ M_F`,
`DΦ(w) = I + ι ∘ DΨ(w)`, `‖DΨ(w)‖ ≤ 8 M_F/σ`. -/
theorem phi_smooth_of (hS : W6StepSmooth)
    (H : StepHypSrc a p pb s r σ η τ α lam ε ε₀ ε₁ γ M0 Mω MΩ Par ω Ω P X) [Fact (0 < r)]
    {ξ : Fin 2 → ℝ} (hξ : ξ ∈ Par) :
    DifferentiableOn ℂ (H.hyp.core.Phi ξ) (stepDomain r (s - 5 * σ) (η * r)) ∧
    DifferentiableOn ℂ (H.w6Psi ξ) (stepDomain r (s - 5 * σ) (η * r)) ∧
    ∀ w ∈ stepDomain r (s - 5 * σ) (η * r),
      H.hyp.core.Phi ξ w = w + stepEmbedCLM a p pb H.hpb r (H.w6Psi ξ w) ∧
      ‖H.w6Psi ξ w‖ ≤ stepMF (stepCF τ) (stepExpT τ) α σ ε ∧
      fderiv ℂ (H.hyp.core.Phi ξ) w = ContinuousLinearMap.id ℂ _ +
        (stepEmbedCLM a p pb H.hpb r).comp (fderiv ℂ (H.w6Psi ξ) w) ∧
      ‖fderiv ℂ (H.w6Psi ξ) w‖ ≤ 8 * stepMF (stepCF τ) (stepExpT τ) α σ ε / σ := by
  have e : H.w6Psi ξ =
      (hS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H inferInstance ξ hξ).choose := by
    unfold w6Psi; rw [dite_eq_left ⟨hS, hξ⟩]
  obtain ⟨hd, hall⟩ :=
    (hS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H inferInstance ξ hξ).choose_spec
  rw [e]
  obtain ⟨hΦ, hDΦ⟩ := w6_phi_of_psi (stepDomain_isOpen _ _ _) hd fun w hw => (hall w hw).1
  exact ⟨hΦ, hd, fun w hw => ⟨(hall w hw).1, (hall w hw).2.1, hDΦ w hw, (hall w hw).2.2⟩⟩

end StepHypSrc

namespace StepHypModSrc

variable {β : ℝ}

/-- A choice of the smoothing displacement `Ψ` (from the dependency `W6StepSmoothMod`, `0` if
it is not available). -/
def w6Psi (H : StepHypModSrc a p pb s r σ η τ α β lam ε ε₀ ε₁ γ M0 Mω MΩ Par ω Ω P X)
    [Fact (0 < r)] (ξ : Fin 2 → ℝ) : StepPhase r → StepPhase r :=
  open Classical in
  if h : W6StepSmoothMod ∧ ξ ∈ Par then
    (h.1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H inferInstance ξ h.2).choose
  else fun _ => 0

/-- **The smoothing of `Φ`, modified case** (conditional on the W5 dependency `W6StepSmoothMod`). -/
theorem phi_smooth_of (hS : W6StepSmoothMod)
    (H : StepHypModSrc a p pb s r σ η τ α β lam ε ε₀ ε₁ γ M0 Mω MΩ Par ω Ω P X) [Fact (0 < r)]
    {ξ : Fin 2 → ℝ} (hξ : ξ ∈ Par) :
    DifferentiableOn ℂ (H.hyp.core.Phi ξ) (stepDomain r (s - 5 * σ) (η * r)) ∧
    DifferentiableOn ℂ (H.w6Psi ξ) (stepDomain r (s - 5 * σ) (η * r)) ∧
    ∀ w ∈ stepDomain r (s - 5 * σ) (η * r),
      H.hyp.core.Phi ξ w = w + stepEmbedCLM a p pb H.hpb r (H.w6Psi ξ w) ∧
      ‖H.w6Psi ξ w‖ ≤ stepMF (stepCFn τ) (stepTn τ) α σ ε ∧
      fderiv ℂ (H.hyp.core.Phi ξ) w = ContinuousLinearMap.id ℂ _ +
        (stepEmbedCLM a p pb H.hpb r).comp (fderiv ℂ (H.w6Psi ξ) w) ∧
      ‖fderiv ℂ (H.w6Psi ξ) w‖ ≤ 8 * stepMF (stepCFn τ) (stepTn τ) α σ ε / σ := by
  have e : H.w6Psi ξ =
      (hS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H inferInstance ξ hξ).choose := by
    unfold w6Psi; rw [dite_eq_left ⟨hS, hξ⟩]
  obtain ⟨hd, hall⟩ :=
    (hS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H inferInstance ξ hξ).choose_spec
  rw [e]
  obtain ⟨hΦ, hDΦ⟩ := w6_phi_of_psi (stepDomain_isOpen _ _ _) hd fun w hw => (hall w hw).1
  exact ⟨hΦ, hd, fun w hw => ⟨(hall w hw).1, (hall w hw).2.1, hDΦ w hw, (hall w hw).2.2⟩⟩

end StepHypModSrc

end KAM.Wave
