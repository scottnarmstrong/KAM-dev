/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.KamStep.RealNField
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Weak conjugacy in field form (blueprint-W `bpW:w5:new-ham` (iii), `bpW:w5:step` (i))

Off-frontier, source-faithful infrastructure (W5-REAL, item 3); the dependency graph is still being
built.

For `w ∈ D_+` and `W ∈ 𝒫^{p_+}`:
`ϖ(X_H(Φ w), DΦ(w) W) = ϖ(X_{N_+}(w) + X_{P_+}(w), W)`, with `X_H = X_N + X_P`, `X_N` the unbounded
field of `N` (`stepXN`, values in `𝒫^{p-1}`) and `ϖ = ϖ_{p-1,p_+}` on `𝒫^{p-1} × 𝒫^{p_+}`. In the
representative model `W = ι W'` and `DΦ(w)(ι W') = ι W''` (`W', W''` in the `p_+`-representatives;
`W''` exists by `StepCore.dPhi_smooth_mapsTo` and is unique by `stepEmbedCLM_injective`); the
bounded fields `X_P`, `X_{P_+}` (`p_+`-representatives) enter through `ι_{p_+→p-1}`.

* `StepCore.dNplus_eq`: `DN_+(w) = DN(w) + DN̂(w)` with `DN̂(w) V = ϖ_{p,p}(ι X_{N̂}(w), V)`.
* `StepCore.weakConj_field`: the identity, from the derivative form `StepCore.weakConj`, the Riesz
  representation `stepDN_eq_symp_XN` (for `N` and `N_+`) and the invariance `stepSymp_embed_eq`.
* `stepTheorem_weakConj_field` (`WaveStepHyp`), `stepTheoremMod_weakConj_field` (`StepHypMod`).
-/

@[expose] public noncomputable section

namespace KAM.Wave

open KAM

variable {a p pb s r σ η τ α lam ε ε₀ ε₁ γ M0 Mω MΩ M₀ M₁ cF tF : ℝ} {Par : Set (Fin 2 → ℝ)}
  {ω : (Fin 2 → ℝ) → Fin 2 → ℝ} {Ω : (Fin 2 → ℝ) → ℕ+ → ℝ}
  {P : (Fin 2 → ℝ) → KamPhase → ℂ} {X : (Fin 2 → ℝ) → KamPhase → KamPhase}
  {FT : (Fin 2 → ℝ) → HomTaylor_gen a p pb (s - σ)}

namespace StepCore

variable (H : StepCore a p pb s r σ η τ α lam ε ε₀ ε₁ γ M0 Mω MΩ M₀ M₁ cF tF Par ω Ω P X FT)
include H

theorem hqq1 : 0 ≤ (p - 1) + pb := by linarith [H.hp1]

theorem hpm : p - 1 ≤ pb := by linarith [H.hpb]

variable [Fact (0 < r)]

/-- `DN_+(w) = DN(w) + DN̂(w)`, `DN̂(w) V = ϖ_{p,p}(ι X_{N̂}(w), V)` (`N_+ = N + N̂`). -/
theorem dNplus_eq {ξ : Fin 2 → ℝ} (hξ : ξ ∈ Par) {w : StepPhase r}
    (hw : (StepPhase.toK w).1 ∈ complexStrip 2 s) (V : StepPhase r) :
    ((homDN H.hG H.hKp (H.omegaPlus_bound hξ) (H.omegaPlus ξ)
        (stepToHom (StepPhase.toK w))).comp stepToHom).comp (stepToKCLM r) V =
      ((homDN H.hG H.hK0 (homOmega_le H.freq hξ) (ω ξ)
          (stepToHom (StepPhase.toK w))).comp stepToHom).comp (stepToKCLM r) V +
        stepSympCLM (q := p) (q' := p) H.ha H.two_p r
          (stepEmbedCLM a p pb H.hpb r
            (stepFieldS H.ha H.hp H.hpb (homNhatTaylor_gen (H.R ξ)) r w)) V := by
  have h1 := (stepNfun_hasFDerivAt H.hG H.hKp (H.omegaPlus_bound hξ) (H.omegaPlus ξ)
    (StepPhase.toK w)).comp w (stepToKCLM r).hasFDerivAt
  have h2 := ((stepNfun_hasFDerivAt H.hG H.hK0 (homOmega_le H.freq hξ) (ω ξ)
    (StepPhase.toK w)).comp w (stepToKCLM r).hasFDerivAt).add
    (stepFS_hasFDerivAt H.ha H.hp H.hpb (homNhatTaylor_gen (H.R ξ)) r hw)
  have hfun : (stepNfun H.hG H.hK0 (homOmega_le H.freq hξ) (ω ξ) ∘ StepPhase.toK +
      stepFS H.ha H.hp H.hpb (homNhatTaylor_gen (H.R ξ)) r) =
      (stepNfun H.hG H.hKp (H.omegaPlus_bound hξ) (H.omegaPlus ξ)) ∘ StepPhase.toK :=
    funext fun z => H.nplus_eq hξ (StepPhase.toK z)
  rw [hfun] at h2
  have := congrArg (fun L : StepPhase r →L[ℂ] ℂ => L V) (h1.unique h2)
  exact this

/-- **Weak conjugacy in field form** (`bpW:w5:new-ham` (iii)): for `ξ ∈ Π`, `w ∈ D_+`, and
`W', W''` (`p_+`-representatives) with `DΦ(w)(ι W') = ι W''`:
`ϖ_{p-1,p_+}(X_N(Φ w) + ι X_P(Φ w), W'') = ϖ_{p-1,p_+}(X_{N_+}(w) + ι X_{P_+}(w), W')`. -/
theorem weakConj_field {ξ : Fin 2 → ℝ} (hξ : ξ ∈ Par) {w : StepPhase r}
    (hw : w ∈ stepDomain r (s - 5 * σ) (η * r)) (W' W'' : StepPhase r)
    (hW : fderiv ℂ (H.Phi ξ) w (stepEmbedCLM a p pb H.hpb r W') =
      stepEmbedCLM a p pb H.hpb r W'') :
    stepSymp (q := p - 1) (q' := pb) H.ha H.hqq1
        (stepXN (a := a) (p := p) (homOmega_le H.freq hξ) (ω ξ) (StepPhase.toK (H.Phi ξ w)) +
          kamHomEmbed a (p - 1) pb H.hpm (X ξ (StepPhase.toK (H.Phi ξ w))))
        (StepPhase.toK W'') =
      stepSymp (q := p - 1) (q' := pb) H.ha H.hqq1
        (stepXN (a := a) (p := p) (H.omegaPlus_bound hξ) (H.omegaPlus ξ) (StepPhase.toK w) +
          kamHomEmbed a (p - 1) pb H.hpm (StepPhase.toK (H.Xplus ξ w)))
        (StepPhase.toK W') := by
  have wc := H.weakConj hξ hw (stepEmbedCLM a p pb H.hpb r W')
  rw [hW, ← H.dNplus_eq hξ (stepDomain_theta_mem (by linarith [H.hσ]) hw)] at wc
  have e1 : ((homDN H.hG H.hK0 (homOmega_le H.freq hξ) (ω ξ)
      (stepToHom (StepPhase.toK (H.Phi ξ w)))).comp stepToHom).comp (stepToKCLM r)
        (stepEmbedCLM a p pb H.hpb r W'') =
      stepSymp (q := p - 1) (q' := pb) H.ha H.hqq1
        (stepXN (a := a) (p := p) (homOmega_le H.freq hξ) (ω ξ) (StepPhase.toK (H.Phi ξ w)))
        (StepPhase.toK W'') := by
    have h := stepDN_eq_symp_XN H.ha H.hpb H.hqq1 H.hG H.hK0 (homOmega_le H.freq hξ) (ω ξ)
      (StepPhase.toK (H.Phi ξ w)) (StepPhase.toK W'')
    rw [ContinuousLinearMap.comp_apply, stepToKCLM_apply, stepEmbedCLM_apply]
    exact h
  have e2 : stepSympCLM (q := p) (q' := p) H.ha H.two_p r
      (stepEmbedCLM a p pb H.hpb r (stepXPS (X ξ) r (H.Phi ξ w)))
        (stepEmbedCLM a p pb H.hpb r W'') =
      stepSymp (q := p - 1) (q' := pb) H.ha H.hqq1
        (kamHomEmbed a (p - 1) pb H.hpm (X ξ (StepPhase.toK (H.Phi ξ w)))) (StepPhase.toK W'') := by
    rw [stepSympCLM_apply, stepEmbedCLM_apply, stepEmbedCLM_apply]
    exact stepSymp_embed_eq H.ha H.hpb H.two_p H.hqq1 H.hpm _ _
  have e3 : ((homDN H.hG H.hKp (H.omegaPlus_bound hξ) (H.omegaPlus ξ)
      (stepToHom (StepPhase.toK w))).comp stepToHom).comp (stepToKCLM r)
        (stepEmbedCLM a p pb H.hpb r W') =
      stepSymp (q := p - 1) (q' := pb) H.ha H.hqq1
        (stepXN (a := a) (p := p) (H.omegaPlus_bound hξ) (H.omegaPlus ξ) (StepPhase.toK w))
        (StepPhase.toK W') := by
    have h := stepDN_eq_symp_XN H.ha H.hpb H.hqq1 H.hG H.hKp (H.omegaPlus_bound hξ)
      (H.omegaPlus ξ) (StepPhase.toK w) (StepPhase.toK W')
    rw [ContinuousLinearMap.comp_apply, stepToKCLM_apply, stepEmbedCLM_apply]
    exact h
  have e4 : stepSympCLM (q := p) (q' := p) H.ha H.two_p r
      (stepEmbedCLM a p pb H.hpb r (H.Xplus ξ w)) (stepEmbedCLM a p pb H.hpb r W') =
      stepSymp (q := p - 1) (q' := pb) H.ha H.hqq1
        (kamHomEmbed a (p - 1) pb H.hpm (StepPhase.toK (H.Xplus ξ w))) (StepPhase.toK W') := by
    rw [stepSympCLM_apply, stepEmbedCLM_apply, stepEmbedCLM_apply]
    exact stepSymp_embed_eq H.ha H.hpb H.two_p H.hqq1 H.hpm _ _
  rw [e1, e2, e3, e4] at wc
  rw [stepSymp_add_left, stepSymp_add_left]
  exact wc

end StepCore

/-- **Weak conjugacy in field form** (blueprint `bpW:w5:new-ham` (iii), `bpW:w5:step` (i)),
non-modified case. For `ξ ∈ Π` and `w ∈ D_+`, with `Φ = H.core.Phi ξ`, `X_{P_+} = H.core.Xplus ξ`,
`X_N` = `stepXN` for `(ω, Ω)` and `X_{N_+}` = `stepXN` for `(ω_+, Ω_+)`, and `ι` the inclusions:
every `W = ι W' ∈ 𝒫^{p_+}` has `DΦ(w) W = ι W''` for some `W''`, and for every such pair
`ϖ_{p-1,p_+}(X_H(Φ w), W'') = ϖ_{p-1,p_+}(X_{N_+}(w) + X_{P_+}(w), W')`, `X_H = X_N + X_P`. -/
theorem stepTheorem_weakConj_field
    (H : WaveStepHyp a p pb s r σ η τ α lam ε ε₀ ε₁ γ M0 Mω MΩ Par ω Ω P X) [Fact (0 < r)]
    {ξ : Fin 2 → ℝ} (hξ : ξ ∈ Par) {w : StepPhase r}
    (hw : w ∈ stepDomain r (s - 5 * σ) (η * r)) :
    (∀ W' : StepPhase r, ∃ W'' : StepPhase r,
      fderiv ℂ (H.core.Phi ξ) w (stepEmbedCLM a p pb H.hpb r W') =
        stepEmbedCLM a p pb H.hpb r W'') ∧
    (∀ W' W'' : StepPhase r, fderiv ℂ (H.core.Phi ξ) w (stepEmbedCLM a p pb H.hpb r W') =
        stepEmbedCLM a p pb H.hpb r W'' →
      stepSymp (q := p - 1) (q' := pb) H.ha H.core.hqq1
          (stepXN (a := a) (p := p) (homOmega_le H.freq hξ) (ω ξ)
              (StepPhase.toK (H.core.Phi ξ w)) +
            kamHomEmbed a (p - 1) pb H.core.hpm (X ξ (StepPhase.toK (H.core.Phi ξ w))))
          (StepPhase.toK W'') =
        stepSymp (q := p - 1) (q' := pb) H.ha H.core.hqq1
          (stepXN (a := a) (p := p) (H.core.omegaPlus_bound hξ) (H.core.omegaPlus ξ)
              (StepPhase.toK w) +
            kamHomEmbed a (p - 1) pb H.core.hpm (StepPhase.toK (H.core.Xplus ξ w)))
          (StepPhase.toK W')) :=
  ⟨H.core.dPhi_smooth_mapsTo hξ hw, fun W' W'' hW => H.core.weakConj_field hξ hw W' W'' hW⟩

/-- **Weak conjugacy in field form**, modified case (blueprint `bpW:w5:new-ham` (iii) for
`StepHypMod`; the field of `P` enters as `D_ρ ∘ X = H.X'` in the `p_+`-representatives). -/
theorem stepTheoremMod_weakConj_field {β : ℝ}
    (H : StepHypMod a p pb s r σ η τ α β lam ε ε₀ ε₁ γ M0 Mω MΩ Par ω Ω P X) [Fact (0 < r)]
    {ξ : Fin 2 → ℝ} (hξ : ξ ∈ Par) {w : StepPhase r}
    (hw : w ∈ stepDomain r (s - 5 * σ) (η * r)) :
    (∀ W' : StepPhase r, ∃ W'' : StepPhase r,
      fderiv ℂ (H.core.Phi ξ) w (stepEmbedCLM a p pb H.hpb r W') =
        stepEmbedCLM a p pb H.hpb r W'') ∧
    (∀ W' W'' : StepPhase r, fderiv ℂ (H.core.Phi ξ) w (stepEmbedCLM a p pb H.hpb r W') =
        stepEmbedCLM a p pb H.hpb r W'' →
      stepSymp (q := p - 1) (q' := pb) H.ha H.core.hqq1
          (stepXN (a := a) (p := p) (homOmega_le H.freq hξ) (ω ξ)
              (StepPhase.toK (H.core.Phi ξ w)) +
            kamHomEmbed a (p - 1) pb H.core.hpm (H.X' ξ (StepPhase.toK (H.core.Phi ξ w))))
          (StepPhase.toK W'') =
        stepSymp (q := p - 1) (q' := pb) H.ha H.core.hqq1
          (stepXN (a := a) (p := p) (H.core.omegaPlus_bound hξ) (H.core.omegaPlus ξ)
              (StepPhase.toK w) +
            kamHomEmbed a (p - 1) pb H.core.hpm (StepPhase.toK (H.core.Xplus ξ w)))
          (StepPhase.toK W')) :=
  ⟨H.core.dPhi_smooth_mapsTo hξ hw, fun W' W'' hW => H.core.weakConj_field hξ hw W' W'' hW⟩

end KAM.Wave
