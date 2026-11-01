/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Iteration.Invariance
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# W6: the tori in KAM coordinates after the preparatory step (interface for `bpW:w6:tori`)

Off the frontier: source-faithful infrastructure used by several nodes. The dependency graph is
still being built. Blueprint labels `bpW:w6:prep-step` (iii) (sharp bound) and the W6 part of
`bpW:w6:tori` (steps `t-hol`, `t-cont`, `t-prep`, `t-close`), before W5's action-angle map
`𝒜_ξ` (`bpW:w5:action-angle`, not formalized here).

For the wave iteration (Definition `bpW:w6:wave-iteration`, starting size
`ε₀ ∈ [ε^♭_0, γ₁ α̌]`), `w6TorusKam H ε₀ θ ξ = Φ_P(Φ_*(θ))`:

* `W6PrepHyp.phiP_sharp` (`bpW:w6:prep-step` (iii), sharp form): `Φ_P = id + ι Ψ_P` on `D_0` with
  `|Ψ_P|_{p_+,r} ≤ M_{F,P}` (the sharper bound of step `f-flow`; W6-ITER's `phiP_bounds` has
  `2M_{F,P}`, deviation D3, which this removes);
* `W6PrepHyp.w6ToriKam`: for `ξ ∈ Π_*`, `θ ∈ T_{s_0/2}`: `θ ↦ Φ_P(Φ_*(θ))` is holomorphic,
  periodic, real, jointly continuous in `(θ, ξ)`, with values in `D(s - 4σ_P, 2η_P r) ⊆ D(s, r)`,
  `Φ_P(Φ_*(θ)) - ιθ = ι V` with `|V|_{p_+,r} ≤ e_tor = M_{F,P} + e_Φ`, and the invariance
  `X_{H_in}(Φ_P Φ_* θ) = ι_{p→p-1}(∂_θ(Φ_P ∘ Φ_*)(θ) ν_*)` (steps `t-prep`: `bpW:w6:invariance`,
  the weak conjugacy of the preparatory step, `bpW:w6:strong` and the chain rule). Here
  `X_{H_in} = X_N + ι X_P` for the unperturbed frequencies `(ω⁰, Ω⁰)` and W5's reweighted field
  `X' = D_ρ ∘ X_P` of the input perturbation (the same vector of `𝒫^{p-1}` as `X_P`).

What `bpW:w6:tori` still needs: W5's `bpW:w5:action-angle` (the map `𝒜_ξ` and the identity
`X_{H'} ∘ 𝒜_ξ = D𝒜_ξ X_{H_in}`, clause (v)) and `bpW:w5:initial`, and W3/W1 for (v).
-/

@[expose] public noncomputable section

open Set Metric Real Filter Topology

namespace KAM.Wave

open KAM

/-- Joint continuity of a family of maps that are continuous in `w` and Lipschitz in the parameter
uniformly in `w`. -/
theorem continuousOn_param_lip {f : (Fin 2 → ℝ) → KamPhase → KamPhase} {D : Set KamPhase}
    {Pa : Set (Fin 2 → ℝ)} {A : ℝ} (hA : 0 ≤ A) (hc : ∀ ξ ∈ Pa, ∀ w ∈ D, ContinuousAt (f ξ) w)
    (hl : ∀ ξ ∈ Pa, ∀ ζ ∈ Pa, ∀ w ∈ D, ‖f ξ w - f ζ w‖ ≤ A * ‖ξ - ζ‖) :
    ContinuousOn (fun q : KamPhase × (Fin 2 → ℝ) => f q.2 q.1) (D ×ˢ Pa) := by
  rintro ⟨w0, ξ0⟩ ⟨hw0, hξ0⟩
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  obtain ⟨δ1, hδ1, h1⟩ := Metric.continuousAt_iff.1 (hc ξ0 hξ0 w0 hw0) (ε / 2) (by positivity)
  refine ⟨min δ1 (ε / (2 * (A + 1))), by positivity, ?_⟩
  rintro ⟨w, ξ⟩ ⟨hw, hξ⟩ hdist
  have hdw : dist w w0 < δ1 := (le_max_left _ _).trans_lt (hdist.trans_le (min_le_left _ _))
  have hdξ : dist ξ ξ0 < ε / (2 * (A + 1)) :=
    (le_max_right _ _).trans_lt (hdist.trans_le (min_le_right _ _))
  have e1 : ‖f ξ w - f ξ0 w‖ ≤ A * dist ξ ξ0 := by rw [dist_eq_norm]; exact hl ξ hξ ξ0 hξ0 w hw
  have e2 : dist (f ξ0 w) (f ξ0 w0) < ε / 2 := h1 hdw
  have e3 : A * dist ξ ξ0 < ε / 2 := by
    calc A * dist ξ ξ0 ≤ (A + 1) * dist ξ ξ0 := mul_le_mul_of_nonneg_right (by linarith) dist_nonneg
      _ < (A + 1) * (ε / (2 * (A + 1))) := mul_lt_mul_of_pos_left hdξ (by positivity)
      _ = ε / 2 := by field_simp
  simp only
  rw [dist_eq_norm] at e2 ⊢
  calc ‖f ξ w - f ξ0 w0‖ ≤ ‖f ξ w - f ξ0 w‖ + ‖f ξ0 w - f ξ0 w0‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ < ε / 2 + ε / 2 := by linarith
    _ = ε := by ring

namespace W6PrepHyp

variable {m : ℝ} {hm : 0 < m} {Pi : Set (Fin 2 → ℝ)} {α r ε : ℝ}
  {P : (Fin 2 → ℝ) → KamPhase → ℂ} {X : (Fin 2 → ℝ) → KamPhase → KamPhase} {ε₀ : ℝ}

/-- `Φ_P` on `KamPhase`. -/
def w6PhiPK (H : W6PrepHyp m hm Pi α r ε P X) (ξ : Fin 2 → ℝ) (w : KamPhase) : KamPhase :=
  StepPhase.toK (H.PhiP ξ (StepPhase.ofK w))

/-- `Ψ_P` on `KamPhase` (`p_+`-representatives): `Φ_P = id + ι Ψ_P` on `D_0`. -/
def w6PsiPK (H : W6PrepHyp m hm Pi α r ε P X) (ξ : Fin 2 → ℝ) (w : KamPhase) : KamPhase :=
  haveI := H.factR
  StepPhase.toK (H.prepStepHyp.hyp.core.stepPsi ξ (StepPhase.ofK w))

/-- **Preparatory step, transformation, sharp form** (`bpW:w6:prep-step` (iii), step `p-lipp`):
for `ξ ∈ Π ∖ Ξ` and `w ∈ D_0 = D(s_0, η_P r)`: `Φ_P(w) = w + ι Ψ_P(w)` with
`|Ψ_P(w)|_{p_+,r} ≤ M_{F,P} = c^♮_F ε/(α̂ σ_P^{t^♮-1})`, and `Φ_P(w) - w` is Lipschitz in `ξ` in
`|·|_{p,r}`. -/
theorem phiP_sharp (H : W6PrepHyp m hm Pi α r ε P X) :
    (∀ ξ ∈ Pi \ prepSet m hm Pi α, ∀ w ∈ kamDomain w6S0 (w6EtaP α ε * r),
      H.w6PhiPK ξ w = w + w6Iota (H.w6PsiPK ξ w) ∧ kamNorm r (H.w6PsiPK ξ w) ≤ w6MFP α ε) ∧
    ∃ A₁ : ℝ, 0 ≤ A₁ ∧ ∀ ξ ∈ Pi \ prepSet m hm Pi α, ∀ ζ ∈ Pi \ prepSet m hm Pi α,
      ∀ w ∈ kamDomain w6S0 (w6EtaP α ε * r),
        kamNorm r (H.w6PhiPK ξ w - H.w6PhiPK ζ w) ≤ A₁ * ‖ξ - ζ‖ := by
  have := H.factR
  obtain ⟨A₀, A₁, -, a1, -, hb⟩ := H.phiP_bounds
  refine ⟨fun ξ hξ w hw => ?_, A₁, a1, fun ξ hξ ζ hζ w hw => ?_⟩
  · obtain ⟨-, -, -, hall⟩ := H.prepStepHyp.phi_smooth hξ
    obtain ⟨e1, e2, -, -⟩ := hall (StepPhase.ofK w) hw
    refine ⟨?_, e2⟩
    unfold w6PhiPK w6PsiPK PhiP
    rw [e1]
    rfl
  · have h := (hb ξ hξ ζ hζ (StepPhase.ofK w) hw).2
    have e : H.PhiP ξ (StepPhase.ofK w) - StepPhase.ofK w - (H.PhiP ζ (StepPhase.ofK w) -
        StepPhase.ofK w) = H.PhiP ξ (StepPhase.ofK w) - H.PhiP ζ (StepPhase.ofK w) := by abel
    rw [e] at h
    exact h

/-- The clauses of `Φ_P` on `KamPhase` (`bpW:w5:step` (i), modified case): for `ξ ∈ Π ∖ Ξ`,
`Φ_P` is differentiable on `D(s - 2σ_P, r/2) ⊇ D_0`, and on `D_0`: `Φ_P(w) ∈ D(s-4σ_P, 2η_P r)`,
real on real points, `Φ_P(w + τ_i) = Φ_P(w) + τ_i`, `DΦ_P(w)` symplectic and onto `𝒫^{p_+}`, and
the weak conjugacy in field form. -/
theorem prepK_clauses (H : W6PrepHyp m hm Pi α r ε P X) {ξ : Fin 2 → ℝ}
    (hξ : ξ ∈ Pi \ prepSet m hm Pi α) :
    (∀ w ∈ kamDomain (w6S - 2 * w6SigmaP) (r / 2), DifferentiableAt ℂ (H.w6PhiPK ξ) w) ∧
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
          w6SympPred (w6Field hΩ1 (H.om0 ξ) (H.X0 ξ) w) W' := by
  have := H.factR
  set G := H.prepStepHyp
  obtain ⟨hsub, hdΦ, -, -⟩ := G.phi_smooth hξ
  obtain ⟨c1, -, -, c4, c5, c6, c7, c8, -⟩ := stepTheoremMod G
  have hΦ : ∀ w ∈ kamDomain (w6S - 2 * w6SigmaP) (r / 2), HasFDerivAt (H.w6PhiPK ξ)
      ((stepToKCLM r).comp ((fderiv ℂ (G.hyp.core.Phi ξ) (StepPhase.ofK w)).comp
        (stepOfKCLM r))) w := fun w hw =>
    hasFDerivAt_stepK ((hdΦ _ hw).differentiableAt ((stepDomain_isOpen _ _ _).mem_nhds hw))
  have hfd : ∀ w ∈ kamDomain (w6S - 2 * w6SigmaP) (r / 2), ∀ W,
      fderiv ℂ (H.w6PhiPK ξ) w W =
        StepPhase.toK (fderiv ℂ (G.hyp.core.Phi ξ) (StepPhase.ofK w) (StepPhase.ofK W)) :=
    fun w hw W => by rw [(hΦ w hw).fderiv]; rfl
  refine ⟨fun w hw => (hΦ w hw).differentiableAt, fun w hw => ⟨c1 ξ hξ (StepPhase.ofK w) hw,
    fun hr => c6 ξ hξ (StepPhase.ofK w) hw hr, fun i => c5 ξ hξ (StepPhase.ofK w) hw i,
    fun W W' => ?_, fun W'' => ?_, fun hΩ0 hΩ1 W' W'' hW => ?_⟩⟩
  · rw [hfd w (hsub hw), hfd w (hsub hw)]
    exact c4 ξ hξ (StepPhase.ofK w) hw (StepPhase.ofK W) (StepPhase.ofK W')
  · obtain ⟨W', h⟩ := (c7 ξ hξ (StepPhase.ofK w) hw).2 (StepPhase.ofK W'')
    refine ⟨StepPhase.toK W', ?_⟩
    rw [hfd w (hsub hw)]
    exact congrArg StepPhase.toK h
  · rw [hfd w (hsub hw)] at hW
    exact c8 ξ hξ (StepPhase.ofK w) hw (StepPhase.ofK W') (StepPhase.ofK W'') hW

/-- The torus in KAM coordinates of `bpW:w6:tori`: `θ ↦ Φ_P(Φ_*(θ))` for the wave iteration with
starting size `ε₀`. -/
def w6TorusKam (H : W6PrepHyp m hm Pi α r ε P X) (ε₀ : ℝ) (θ : Fin 2 → ℂ) (ξ : Fin 2 → ℝ) :
    KamPhase :=
  H.w6PhiPK ξ (w6PhiStar (w6WaveSeq m hm α r ε ε₀)
    (w6Start (w6WaveSeq m hm α r ε ε₀) (Pi \ prepSet m hm Pi α) H.om0 H.Om0 H.w6P0 H.X0) θ ξ)

/-- **The tori in KAM coordinates** (W6 part of `bpW:w6:tori`, steps `t-hol`, `t-cont`, `t-prep`,
`t-close`; before W5's action-angle map). For the wave iteration with starting size
`ε₀ ∈ [ε^♭_0, γ₁ α̌]`, `Π_* = wavePiStar`, `T = T_{s_∞}`, and `Ψ(θ) = Φ_P(Φ_*(θ))`:
* (i) for `ξ ∈ Π_*`, `Ψ` is holomorphic on `T`, periodic, and real on real `θ`;
* (ii) `(θ, ξ) ↦ Ψ(θ)` is continuous on `T × Π_*`;
* (iv) `Ψ(θ) ∈ D(s - 4σ_P, 2η_P r)` and `Ψ(θ) - ιθ = ι V` with `|V|_{p_+,r} ≤ e_tor = M_{F,P} + e_Φ`
  (so the normal part of `Ψ(θ)` lies in `𝒫^{p_+}`);
* (iii) invariance, for `θ ∈ T_{s_0/2}`: `X_{H_in}(Ψ(θ)) = ι_{p→p-1}(∂_θΨ(θ) ν_*)` in `𝒫^{p-1}`,
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
            (Pi \ prepSet m hm Pi α) H.om0 H.Om0 H.w6P0 H.X0) ξ))) := by
  have := H.factR
  have hr := H.hr
  set d := w6WaveSeq m hm α r ε ε₀ with hddef
  set S0 := w6Start d (Pi \ prepSet m hm Pi α) H.om0 H.Om0 H.w6P0 H.X0 with hS0
  have hC := H.w6Applicable hlo hhi
  have hI := w6IterHyp_of_conv hC
  have hr0 := W6SeqData.w6r_pos hI.std.1 0
  obtain ⟨-, -, -, hlim, hcont, himg, hcl, hbd, -⟩ := w6ConvTorus hC
  set T := complexStrip 2 d.sInfty
  have hTo : IsOpen T := isOpen_complexStrip 2 _
  have hPS : ∀ ξ ∈ H.wavePiStar ε₀, ξ ∈ Pi \ prepSet m hm Pi α := fun ξ hξ =>
    w6Pi0_subset (mem_iInter.1 hξ 0)
  have hD0 : ∀ θ ∈ T, ∀ ξ ∈ H.wavePiStar ε₀,
      w6PhiStar d S0 θ ξ ∈ kamDomain w6S0 (w6EtaP α ε * r) := fun θ hθ ξ hξ =>
    hcl (himg θ hθ ξ hξ)
  have hη := H.prepStepHyp.hη
  have hη0 := H.prepStepHyp.hη0
  have hσP := H.prepStepHyp.hσ
  have hsubU : kamDomain w6S0 (w6EtaP α ε * r) ⊆ kamDomain (w6S - 2 * w6SigmaP) (r / 2) :=
    kamDomain_mono (by unfold w6S0; linarith) (by positivity) (by nlinarith)
  -- `Φ_P` at `Φ_*(θ)`
  have hdP : ∀ θ ∈ T, ∀ ξ ∈ H.wavePiStar ε₀,
      DifferentiableAt ℂ (H.w6PhiPK ξ) (w6PhiStar d S0 θ ξ) := fun θ hθ ξ hξ =>
    (H.prepK_clauses (hPS ξ hξ)).1 _ (hsubU (hD0 θ hθ ξ hξ))
  have hdS : ∀ θ ∈ T, ∀ ξ ∈ H.wavePiStar ε₀,
      DifferentiableAt ℂ (fun θ' => w6PhiStar d S0 θ' ξ) θ := fun θ hθ ξ hξ =>
    ((hlim ξ hξ).1).differentiableAt (hTo.mem_nhds hθ)
  refine ⟨fun ξ hξ => ⟨fun θ hθ => ((hdP θ hθ ξ hξ).comp θ (hdS θ hθ ξ hξ)).differentiableWithinAt,
      fun θ hθ i => ?_, fun x => ?_⟩, ?_, fun θ hθ ξ hξ => ?_, fun ξ hξ θ hθ K0 hΩ0 => ?_⟩
  · -- periodicity
    have hcl' := (H.prepK_clauses (hPS ξ hξ)).2 _ (hD0 θ hθ ξ hξ)
    unfold w6TorusKam
    rw [((hlim ξ hξ).2.1 θ hθ i)]
    exact hcl'.2.2.1 i
  · -- reality
    have hx := w6_real_mem_strip hI.std x
    exact ((H.prepK_clauses (hPS ξ hξ)).2 _ (hD0 _ hx ξ hξ)).2.1 ((hlim ξ hξ).2.2 x)
  · -- joint continuity
    obtain ⟨-, A₁, hA₁, hlip⟩ := H.phiP_sharp
    set C := max 1 (max (r ^ 2) r)
    have hC : 0 < C := lt_of_lt_of_le one_pos (le_max_left _ _)
    have hg : ContinuousOn (fun q : KamPhase × (Fin 2 → ℝ) => H.w6PhiPK q.2 q.1)
        (kamDomain w6S0 (w6EtaP α ε * r) ×ˢ (Pi \ prepSet m hm Pi α)) :=
      continuousOn_param_lip (A := C * A₁) (by positivity)
        (fun ξ hξ w hw => ((H.prepK_clauses hξ).1 w (hsubU hw)).continuousAt)
        fun ξ hξ ζ hζ w hw => by
          calc _ ≤ C * kamNorm r (H.w6PhiPK ξ w - H.w6PhiPK ζ w) := norm_kamPhase_le_kamNorm hr _
            _ ≤ C * (A₁ * ‖ξ - ζ‖) := mul_le_mul_of_nonneg_left (hlip ξ hξ ζ hζ w hw) hC.le
            _ = C * A₁ * ‖ξ - ζ‖ := by ring
    have hh : ContinuousOn (fun q : (Fin 2 → ℂ) × (Fin 2 → ℝ) => (w6PhiStar d S0 q.1 q.2, q.2))
        (T ×ˢ w6PiStarS d S0) := hcont.prodMk continuous_snd.continuousOn
    have hmap : MapsTo (fun q : (Fin 2 → ℂ) × (Fin 2 → ℝ) => (w6PhiStar d S0 q.1 q.2, q.2))
        (T ×ˢ w6PiStarS d S0) (kamDomain w6S0 (w6EtaP α ε * r) ×ˢ (Pi \ prepSet m hm Pi α)) :=
      fun q hq => ⟨hD0 q.1 hq.1 q.2 hq.2, hPS q.2 hq.2⟩
    have hfin := hg.comp hh hmap
    exact hfin
  · -- values and closeness
    have hw := hD0 θ hθ ξ hξ
    refine ⟨((H.prepK_clauses (hPS ξ hξ)).2 _ hw).1, ?_⟩
    obtain ⟨V, hV, hVb⟩ := hbd θ hθ ξ hξ
    obtain ⟨e1, e2⟩ := H.phiP_sharp.1 ξ (hPS ξ hξ) _ hw
    refine ⟨V + H.w6PsiPK ξ (w6PhiStar d S0 θ ξ), ?_, ?_⟩
    · unfold w6TorusKam
      rw [e1, map_add, ← hV]
      abel
    · have h1 := kamNorm_add_le hr V (H.w6PsiPK ξ (w6PhiStar d S0 θ ξ))
      have h2 : kamNorm r V ≤ kamNorm (d.rNu 0) V :=
        kamNorm_anti hr0 (by show w6EtaP α ε * r ≤ r; nlinarith) V
      unfold w6Etor
      linarith
  · -- invariance through the preparatory step
    have hθT : θ ∈ T := w6_ball_subset_strip (d := d) hθ
      (mem_ball_self (by have := hI.std.1.s0_pos; positivity))
    have hw := hD0 θ hθT ξ hξ
    have hξ' := hPS ξ hξ
    have hΩ1 := H.prepStepHyp.hyp.core.omegaPlus_bound hξ'
    have hinv := w6Invariance hC hξ hΩ1 hθ
    obtain ⟨-, -, -, hs, hon, hweak⟩ := (H.prepK_clauses hξ').2 _ hw
    have key := w6StrongConjK _ hs hon _ _ (hweak hΩ0 hΩ1) _ hinv
    have hc : HasFDerivAt (fun θ' => H.w6TorusKam ε₀ θ' ξ)
        ((fderiv ℂ (H.w6PhiPK ξ) (w6PhiStar d S0 θ ξ)).comp
          (fderiv ℂ (fun θ' => w6PhiStar d S0 θ' ξ) θ)) θ :=
      (hdP θ hθT ξ hξ).hasFDerivAt.comp θ (hdS θ hθT ξ hξ).hasFDerivAt
    rw [hc.fderiv]
    exact key

end W6PrepHyp

end KAM.Wave
