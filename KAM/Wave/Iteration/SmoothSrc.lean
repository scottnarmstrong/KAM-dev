/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Iteration.ToriPrep
public import KAM.Wave.Iteration.StepSmoothW5
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# W6: the source-facing theorems after the W5 smoothing discharge

Off the frontier: source-faithful infrastructure used by several nodes. The dependency graph is
still being built. Blueprint labels `bpW:w6:convergence` (iii), (iv), `bpW:w6:invariance`,
`bpW:w6:prep-step` (iii) (sharp form), and the W6 part of `bpW:w6:tori` (KAM coordinates).

W6-CONV stated these as conditional helpers on the named W5 dependencies `W6StepSmooth`,
`W6StepSmoothMod`; both are now theorems (`w6StepSmooth_holds`, `w6StepSmoothMod_holds`,
module `StepSmoothW5`). The unconditional source-facing theorems (same statements, the dependency
argument removed); the helpers keep their names:

| helper (kept) | unconditional |
|---|---|
| `w6IterHyp_of_conv` | `w6IterHyp_src` |
| `w6ConvTorus_of_stepSmooth` | `w6ConvTorus` |
| `w6ConvOpsSrc_of_stepSmooth` | `w6ConvOpsSrc` |
| `w6Invariance_of_stepSmooth` | `w6Invariance` |
| `W6PrepHyp.phiP_sharp_of_stepSmoothMod` | `W6PrepHyp.phiP_sharp` |
| `W6PrepHyp.prepK_clauses` | `W6PrepHyp.prepK_props` |
| `W6PrepHyp.w6ToriKam_of_stepSmooth` | `W6PrepHyp.w6ToriKam` |
-/

@[expose] public noncomputable section

open Set Metric Real Filter Topology

namespace KAM.Wave

open KAM

section src

variable {d : W6SeqData} {Pm : Set (Fin 2 → ℝ)} {ω0 : (Fin 2 → ℝ) → Fin 2 → ℝ}
  {Ω0 : (Fin 2 → ℝ) → ℕ+ → ℝ} {P0 : (Fin 2 → ℝ) → KamPhase → ℂ}
  {X0 : (Fin 2 → ℝ) → KamPhase → KamPhase} {β₀ : ℝ}

/-- The iteration of Proposition `bpW:w6:convergence` has the hypotheses of every stage (step
`c-ind`), including the `p_+` bounds of each step (W5, `w6StepSmooth_holds`). -/
theorem w6IterHyp_src (hC : W6ConvHyp d Pm ω0 Ω0 P0 X0 β₀) :
    W6IterHyp d (w6Start d Pm ω0 Ω0 P0 X0) :=
  w6IterHyp_of_conv w6StepSmooth_holds hC

/-- **Transformations on the torus** (blueprint `bpW:w6:convergence` (iii)) for the data of the
proposition (`W6ConvHyp`, `Π_{-1} = Pm`, the iteration `w6Seq` started at `w6Start`). -/
theorem w6ConvTorus (hC : W6ConvHyp d Pm ω0 Ω0 P0 X0 β₀) :
    W6ConvTorusClause d (w6Start d Pm ω0 Ω0 P0 X0) :=
  w6ConvTorus_of_stepSmooth w6StepSmooth_holds hC

/-- **Operator bounds** (blueprint `bpW:w6:convergence` (iv)) for the data of the proposition:
`Φ^ν` is holomorphic on `D_ν`, `|DΦ^ν(w) W|_{p,r_0} ≤ 2|W|_{p,r_ν}`, `DΦ^ν(w)` maps `𝒫^{p_+}` into
itself with the same bound, is symplectic and onto `𝒫^{p_+}`. -/
theorem w6ConvOpsSrc (hC : W6ConvHyp d Pm ω0 Ω0 P0 X0 β₀)
    (ν : ℕ) (ξ : Fin 2 → ℝ)
    (hξ : ∀ μ < ν, ξ ∈ (w6Seq d (w6Start d Pm ω0 Ω0 P0 X0) μ).Pi) :
    DifferentiableOn ℂ (w6PhiC d (w6Start d Pm ω0 Ω0 P0 X0) ν ξ) (d.domNu ν) ∧
    ∀ w ∈ d.domNu ν,
      (∀ W, kamNorm (d.rNu 0) (fderiv ℂ (w6PhiC d (w6Start d Pm ω0 Ω0 P0 X0) ν ξ) w W) ≤
        2 * kamNorm (d.rNu ν) W) ∧
      (∀ W', ∃ W'', fderiv ℂ (w6PhiC d (w6Start d Pm ω0 Ω0 P0 X0) ν ξ) w (w6Iota W') =
        w6Iota W'' ∧ kamNorm (d.rNu 0) W'' ≤ 2 * kamNorm (d.rNu ν) W') ∧
      (∀ W W', w6Symp (fderiv ℂ (w6PhiC d (w6Start d Pm ω0 Ω0 P0 X0) ν ξ) w W)
        (fderiv ℂ (w6PhiC d (w6Start d Pm ω0 Ω0 P0 X0) ν ξ) w W') = w6Symp W W') ∧
      (∀ W'', ∃ W', fderiv ℂ (w6PhiC d (w6Start d Pm ω0 Ω0 P0 X0) ν ξ) w (w6Iota W') =
        w6Iota W'') :=
  w6ConvOpsSrc_of_stepSmooth w6StepSmooth_holds hC ν ξ hξ

/-- **Invariant tori in KAM coordinates** (blueprint `bpW:w6:invariance`). In the setting of
Proposition `bpW:w6:convergence` (`W6ConvHyp`), with `X_{H_0} = X_{N_0} + ι X_{P_0}` (any bound
`K0` for `Ω_0(ξ)`), `ν_* = ω_*/(2π)`: for `ξ ∈ Π_*` and `θ ∈ T_{s_0/2}`,
`X_{H_0}(Φ_*(θ)) = ι_{p→p-1}(∂_θΦ_*(θ) ν_*)` in `𝒫^{p-1}`. -/
theorem w6Invariance (hC : W6ConvHyp d Pm ω0 Ω0 P0 X0 β₀) {ξ : Fin 2 → ℝ}
    (hξ : ξ ∈ w6PiStarIt d (w6Start d Pm ω0 Ω0 P0 X0))
    {K0 : ℝ} (hΩ0 : ∀ j : ℕ+, |Ω0 ξ j| ≤ K0 * ((j : ℝ) + 2))
    {θ : Fin 2 → ℂ} (hθ : θ ∈ complexStrip 2 (d.s0 / 2)) :
    w6Field hΩ0 (ω0 ξ) (X0 ξ) (w6PhiStar d (w6Start d Pm ω0 Ω0 P0 X0) θ ξ) =
      w6IotaPred (fderiv ℂ (fun θ' => w6PhiStar d (w6Start d Pm ω0 Ω0 P0 X0) θ' ξ) θ
        (w6NuVec (w6OmStar d (w6Start d Pm ω0 Ω0 P0 X0) ξ))) :=
  w6Invariance_of_stepSmooth w6StepSmooth_holds hC hξ hΩ0 hθ

end src

namespace W6PrepHyp

variable {m : ℝ} {hm : 0 < m} {Pi : Set (Fin 2 → ℝ)} {α r ε : ℝ}
  {P : (Fin 2 → ℝ) → KamPhase → ℂ} {X : (Fin 2 → ℝ) → KamPhase → KamPhase} {ε₀ : ℝ}

/-- **Preparatory step, transformation, sharp form** (`bpW:w6:prep-step` (iii)): for
`ξ ∈ Π ∖ Ξ` and `w ∈ D_0 = D(s_0, η_P r)`: `Φ_P(w) = w + ι Ψ_P(w)` with
`|Ψ_P(w)|_{p_+,r} ≤ M_{F,P} = c^♮_F ε/(α̂ σ_P^{t^♮-1})`, and `Φ_P(w) - w` is Lipschitz in `ξ` in
`|·|_{p,r}`. -/
theorem phiP_sharp (H : W6PrepHyp m hm Pi α r ε P X) :
    (∀ ξ ∈ Pi \ prepSet m hm Pi α, ∀ w ∈ kamDomain w6S0 (w6EtaP α ε * r),
      H.w6PhiPK ξ w = w + w6Iota (H.w6PsiPK ξ w) ∧ kamNorm r (H.w6PsiPK ξ w) ≤ w6MFP α ε) ∧
    ∃ A₁ : ℝ, 0 ≤ A₁ ∧ ∀ ξ ∈ Pi \ prepSet m hm Pi α, ∀ ζ ∈ Pi \ prepSet m hm Pi α,
      ∀ w ∈ kamDomain w6S0 (w6EtaP α ε * r),
        kamNorm r (H.w6PhiPK ξ w - H.w6PhiPK ζ w) ≤ A₁ * ‖ξ - ζ‖ :=
  H.phiP_sharp_of_stepSmoothMod w6StepSmoothMod_holds

/-- The clauses of `Φ_P` on `KamPhase` (`bpW:w5:step` (i), modified case), unconditional form of
`prepK_clauses`: for `ξ ∈ Π ∖ Ξ`, `Φ_P` is differentiable on `D_0`, and on `D_0`:
`Φ_P(w) ∈ D(s-4σ_P, 2η_P r)`, real on real points, `Φ_P(w + τ_i) = Φ_P(w) + τ_i`, `DΦ_P(w)`
symplectic and onto `𝒫^{p_+}`, and the weak conjugacy in field form. -/
theorem prepK_props (H : W6PrepHyp m hm Pi α r ε P X) {ξ : Fin 2 → ℝ}
    (hξ : ξ ∈ Pi \ prepSet m hm Pi α) :
    (∀ w ∈ kamDomain w6S0 (w6EtaP α ε * r), DifferentiableAt ℂ (H.w6PhiPK ξ) w) ∧
    ∀ w ∈ kamDomain w6S0 (w6EtaP α ε * r),
      H.w6PhiPK ξ w ∈ kamDomain (w6S - 4 * w6SigmaP) (2 * w6EtaP α ε * r) ∧
      (StepReal w → StepReal (H.w6PhiPK ξ w)) ∧
      (∀ i : Fin 2, H.w6PhiPK ξ (w + stepTau i) = H.w6PhiPK ξ w + stepTau i) ∧
      (∀ W W', w6Symp (fderiv ℂ (H.w6PhiPK ξ) w W) (fderiv ℂ (H.w6PhiPK ξ) w W') =
        w6Symp W W') ∧
      (∀ W'', ∃ W', fderiv ℂ (H.w6PhiPK ξ) w (w6Iota W') = w6Iota W'') ∧
      ∀ {K0 K1 : ℝ} (hΩ0 : ∀ j : ℕ+, |waveFreqNor m hm ξ j| ≤ K0 * ((j : ℝ) + 2))
        (hΩ1 : ∀ j : ℕ+, |H.Om0 ξ j| ≤ K1 * ((j : ℝ) + 2)) (W' W'' : KamPhase),
        fderiv ℂ (H.w6PhiPK ξ) w (w6Iota W') = w6Iota W'' →
        w6SympPred (w6Field hΩ0 (waveFreqTan m hm ξ) (H.prepStepHyp.hyp.X' ξ)
            (H.w6PhiPK ξ w)) W'' =
          w6SympPred (w6Field hΩ1 (H.om0 ξ) (H.X0 ξ) w) W' :=
  H.prepK_clauses w6StepSmoothMod_holds hξ

/-- **The tori in KAM coordinates** (W6 part of `bpW:w6:tori`, steps `t-hol`, `t-cont`, `t-prep`,
`t-close`; before W5's action-angle map). For the wave iteration with starting size
`ε₀ ∈ [ε^♭_0, γ₁ α̌]`, `Π_* = wavePiStar`, `T = T_{s_∞}`, and `Ψ(θ) = Φ_P(Φ_*(θ))`:
* for `ξ ∈ Π_*`, `Ψ` is holomorphic on `T`, periodic, and real on real `θ`;
* `(θ, ξ) ↦ Ψ(θ)` is continuous on `T × Π_*`;
* `Ψ(θ) ∈ D(s - 4σ_P, 2η_P r)` and `Ψ(θ) - ιθ = ι V` with `|V|_{p_+,r} ≤ e_tor = M_{F,P} + e_Φ`;
* invariance, for `θ ∈ T_{s_0/2}`: `X_{H_in}(Ψ(θ)) = ι_{p→p-1}(∂_θΨ(θ) ν_*)` in `𝒫^{p-1}`,
  `ν_* = ω_*/2π`, with `X_{H_in} = X_N + ι X'` for the unperturbed frequencies (any bound `K0` of
  `Ω⁰`) and W5's reweighted input field `X'`. -/
theorem w6ToriKam (H : W6PrepHyp m hm Pi α r ε P X) (hlo : w6EpsFlat α ε ≤ ε₀)
    (hhi : ε₀ ≤ w6Gamma1 m hm * alphaCheck α) :
    (∀ ξ ∈ H.wavePiStar ε₀,
      DifferentiableOn ℂ (fun θ => H.w6TorusKam ε₀ θ ξ)
        (complexStrip 2 (w6WaveSeq m hm α r ε ε₀).sInfty) ∧
      (∀ θ ∈ complexStrip 2 (w6WaveSeq m hm α r ε ε₀).sInfty, ∀ i : Fin 2,
        H.w6TorusKam ε₀ (θ + _root_.Pi.single i 1) ξ = H.w6TorusKam ε₀ θ ξ + stepTau i) ∧
      ∀ x : Fin 2 → ℝ, StepReal (H.w6TorusKam ε₀ (fun i => (x i : ℂ)) ξ)) ∧
    ContinuousOn (fun q : (Fin 2 → ℂ) × (Fin 2 → ℝ) => H.w6TorusKam ε₀ q.1 q.2)
      (complexStrip 2 (w6WaveSeq m hm α r ε ε₀).sInfty ×ˢ H.wavePiStar ε₀) ∧
    (∀ θ ∈ complexStrip 2 (w6WaveSeq m hm α r ε ε₀).sInfty, ∀ ξ ∈ H.wavePiStar ε₀,
      H.w6TorusKam ε₀ θ ξ ∈ kamDomain (w6S - 4 * w6SigmaP) (2 * w6EtaP α ε * r) ∧
      ∃ V : KamPhase, H.w6TorusKam ε₀ θ ξ - w6TorusPt θ = w6Iota V ∧
        kamNorm r V ≤ w6Etor m hm α r ε ε₀) ∧
    ∀ ξ ∈ H.wavePiStar ε₀, ∀ θ ∈ complexStrip 2 (w6S0 / 2), ∀ {K0 : ℝ}
      (hΩ0 : ∀ j : ℕ+, |waveFreqNor m hm ξ j| ≤ K0 * ((j : ℝ) + 2)),
      w6Field hΩ0 (waveFreqTan m hm ξ) (H.prepStepHyp.hyp.X' ξ) (H.w6TorusKam ε₀ θ ξ) =
        w6IotaPred (fderiv ℂ (fun θ' => H.w6TorusKam ε₀ θ' ξ) θ
          (w6NuVec (w6OmStar (w6WaveSeq m hm α r ε ε₀) (w6Start (w6WaveSeq m hm α r ε ε₀)
            (Pi \ prepSet m hm Pi α) H.om0 H.Om0 H.w6P0 H.X0) ξ))) :=
  H.w6ToriKam_of_stepSmooth w6StepSmooth_holds w6StepSmoothMod_holds hlo hhi

end W6PrepHyp

end KAM.Wave
