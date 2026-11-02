/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.KamStep.ExportFlowCore
public import KAM.Wave.KamStep.StepTheoremSrc

/-!
# The flow of the KAM step at every time `|t| ≤ 1` (blueprint `bpW:w5:flow`, steps `f-flow`,
`f-par`, `f-der`)

Source-facing exports for the step data alone (`StepHypSrc`, non-modified case; `StepHypModSrc`,
modified case, where `M_F` is read with `c^♮_F`, `t^♮`). The objects are those of the step theorem
(`H.hyp.core`): `φ^t_ξ = H.hyp.core.phiT ξ t` is the time-`t` map of the flow of
`X_{F(ξ)} = ι ∘ Z_ξ`, `Z_ξ = stepFieldS (H.hyp.FT ξ)` the field of the solution `F(ξ)` of the
homological equation with values in the `p_+`-representatives, `ι = stepEmbedCLM : 𝒫^{p_+} → 𝒫`,
`Ψ^t_ξ = H.hyp.core.PsiT ξ t = ∫₀ᵗ Z_ξ(φ^τ_ξ ·) dτ`, so `φ^t = id + ι ∘ Ψ^t`, and
`φ¹ = H.hyp.core.Phi` is the transformation `Φ` of `stepTheorem` (`StepCore.phiT_one`).
`V = D(s-σ, r)`, `U = D(s-2σ, r/2)`, `δ = σ/4`, `M = M_F`, and the norms are those of the step
theorem: `|Ψ^t w|_{p_+,r} = ‖Ψ^t w‖`, `|Dφ^t - I|_{p→p_+,r} = ‖DΨ^t‖`; the `λ`-norms are a sup bound
plus `λ` times a `ξ`-Lipschitz bound.

* `stepFlowLemma`, `stepFlowLemmaMod` (Lemma `bpW:w5:flow`): the hypotheses of the W1 flow lemma
  hold (`M_F ≤ σ/256 < δ`, `L = M/δ ≤ 1/64`), and for `|t| ≤ 1`: (i) `φ^t(U) ⊆ V`,
  `φ^t - id = ι Ψ^t` with `Ψ^t` holomorphic on `U`, `|φ^t - id|^λ_{p_+,r,U} ≤ 2M_F`; (ii) on
  `D(s-3σ, r/4)`: `Dφ^t - I = ι DΨ^t`, `|DΨ^t| ≤ 8M_F/σ`, `|DΨ^t|^λ ≤ 16M_F/σ ≤ η²`; (iii)
  `φ^t(D(s-5σ, ηr)) ⊆ D(s-4σ, 2ηr) ⊆ D(s-3σ, r/4)`; (iv) `φ^t` real on real points of `U`, and
  `φ^t(w + τ_k) = φ^t(w) + τ_k` for `w ∈ U`, `k ∈ ℤ²` (`U + τ_k = U`).
* `stepFlow_fFlow`, `stepFlowMod_fFlow` (step `stepW:w5:f-flow`): `φ^t(U) ⊆ V`, the identity
  `φ^t(w) - w = ∫₀ᵗ X_F(φ^τ w) dτ`, `φ^t - id = ι Ψ^t ∈ 𝒫^{p_+}` holomorphic on `U` with
  `|Ψ^t|_{p_+,r} ≤ |t| M_F`.
* `stepFlow_fPar`, `stepFlowMod_fPar` (step `stepW:w5:f-par`): `|φ^t - id|^λ_{p_+,r,U} ≤ 2M_F`.
* `stepFlow_fDer`, `stepFlowMod_fDer` (step `stepW:w5:f-der`): clause (ii) and `16M_F/σ ≤ η²`.

The reality clause uses `WaveStepHyp.FT_isRealTaylor`, `StepHypMod.FT_isRealTaylor`
(`RealStep.lean`) to discharge the reality of `F`.
-/

@[expose] public noncomputable section

open Set

namespace KAM.Wave

open KAM

variable {a p pb s r σ η τ α β lam ε ε₀ ε₁ γ M0 Mω MΩ : ℝ} {Par : Set (Fin 2 → ℝ)}
  {ω : (Fin 2 → ℝ) → Fin 2 → ℝ} {Ω : (Fin 2 → ℝ) → ℕ+ → ℝ}
  {P : (Fin 2 → ℝ) → KamPhase → ℂ} {X : (Fin 2 → ℝ) → KamPhase → KamPhase}

/-- **The flow with explicit margins** (blueprint Lemma `bpW:w5:flow`, non-modified case).
Under the step data `H` (which include the smallness condition), apply the W1 flow lemma to
`X = X_{F(ξ)}` with `V = D(s-σ, r)`, `U = D(s-2σ, r/2)`, `δ = σ/4`, `M = M_F`: the hypotheses
hold, `M_F ≤ σ/256`,
`L = M/δ ≤ 1/64`, and for `|t| ≤ 1`, `ξ, ζ ∈ Π`: (i) `φ^t` maps `U` into `V`,
`φ^t - id = ι Ψ^t` with `Ψ^t` holomorphic `U → 𝒫^{p_+}`, and `|φ^t - id|^λ_{p_+,r,U} ≤ 2M_F`;
(ii) on `D(s-3σ, r/4)`: `|Dφ^t - I|_{p→p_+,r} ≤ 8M_F/σ` and `|Dφ^t - I|^λ ≤ 16M_F/σ ≤ η²`;
(iii) `φ^t(D(s-5σ, ηr)) ⊆ D(s-4σ, 2ηr) ⊆ D(s-3σ, r/4)`; (iv) `φ^t` is real on real points and
commutes with the integer angle translations `τ_k`, `k ∈ ℤ²` (`U + τ_k = U`). -/
theorem stepFlowLemma
    (H : StepHypSrc a p pb s r σ η τ α lam ε ε₀ ε₁ γ M0 Mω MΩ Par ω Ω P X)
    [Fact (0 < r)] :
    -- the hypotheses of the W1 flow lemma
    (∀ ξ ∈ Par, FlowHyp (smoothField (stepEmbedCLM a p pb H.hpb r)
        (stepFieldS H.ha H.hp H.hpb (H.hyp.FT ξ) r))
      (stepDomain r (s - σ) r) (stepDomain r (s - 2 * σ) (r / 2))
      (stepMF (stepCF τ) (stepExpT τ) α σ ε) (σ / 4)) ∧
    (stepMF (stepCF τ) (stepExpT τ) α σ ε) ≤ σ / 256 ∧
    (stepMF (stepCF τ) (stepExpT τ) α σ ε) / (σ / 4) ≤ 1 / 64 ∧
    ∀ t ∈ Icc (-1 : ℝ) 1,
      -- (i)
      (∀ ξ ∈ Par, ∀ w ∈ stepDomain r (s - 2 * σ) (r / 2),
        H.hyp.core.phiT ξ t w ∈ stepDomain r (s - σ) r ∧
        H.hyp.core.phiT ξ t w = w + stepEmbedCLM a p pb H.hpb r (H.hyp.core.PsiT ξ t w)) ∧
      (∀ ξ ∈ Par, DifferentiableOn ℂ (H.hyp.core.PsiT ξ t) (stepDomain r (s - 2 * σ) (r / 2))) ∧
      (∃ A₀ A₁ : ℝ, 0 ≤ A₀ ∧ 0 ≤ A₁ ∧
        A₀ + lam * A₁ ≤ 2 * (stepMF (stepCF τ) (stepExpT τ) α σ ε) ∧
        ∀ ξ ∈ Par, ∀ ζ ∈ Par, ∀ w ∈ stepDomain r (s - 2 * σ) (r / 2),
          ‖H.hyp.core.PsiT ξ t w‖ ≤ A₀ ∧
          ‖H.hyp.core.PsiT ξ t w - H.hyp.core.PsiT ζ t w‖ ≤ A₁ * ‖ξ - ζ‖) ∧
      -- (ii)
      (∀ ξ ∈ Par, ∀ w ∈ stepDomain r (s - 3 * σ) (r / 4),
        fderiv ℂ (H.hyp.core.phiT ξ t) w = ContinuousLinearMap.id ℂ _ +
          (stepEmbedCLM a p pb H.hpb r).comp (fderiv ℂ (H.hyp.core.PsiT ξ t) w) ∧
        ‖fderiv ℂ (H.hyp.core.PsiT ξ t) w‖ ≤
          8 * (stepMF (stepCF τ) (stepExpT τ) α σ ε) / σ) ∧
      ((∃ B₀ B₁ : ℝ, 0 ≤ B₀ ∧ 0 ≤ B₁ ∧
        B₀ + lam * B₁ ≤ 16 * (stepMF (stepCF τ) (stepExpT τ) α σ ε) / σ ∧
        ∀ ξ ∈ Par, ∀ ζ ∈ Par, ∀ w ∈ stepDomain r (s - 3 * σ) (r / 4),
          ‖fderiv ℂ (H.hyp.core.PsiT ξ t) w‖ ≤ B₀ ∧
          ‖fderiv ℂ (H.hyp.core.PsiT ξ t) w - fderiv ℂ (H.hyp.core.PsiT ζ t) w‖ ≤
            B₁ * ‖ξ - ζ‖) ∧
        16 * (stepMF (stepCF τ) (stepExpT τ) α σ ε) / σ ≤
          η ^ 2) ∧
      -- (iii)
      (∀ ξ ∈ Par, ∀ w ∈ stepDomain r (s - 5 * σ) (η * r),
        H.hyp.core.phiT ξ t w ∈ stepDomain r (s - 4 * σ) (2 * η * r)) ∧
      stepDomain r (s - 4 * σ) (2 * η * r) ⊆ stepDomain r (s - 3 * σ) (r / 4) ∧
      -- (iv)
      (∀ ξ ∈ Par, ∀ w ∈ stepDomain r (s - 2 * σ) (r / 2), StepReal (StepPhase.toK w) →
        StepReal (StepPhase.toK (H.hyp.core.phiT ξ t w))) ∧
      (∀ ξ ∈ Par, ∀ w ∈ stepDomain r (s - 2 * σ) (r / 2), ∀ k : Fin 2 → ℤ,
        w + (k 0 • stepTauS r 0 + k 1 • stepTauS r 1) ∈ stepDomain r (s - 2 * σ) (r / 2) ∧
        H.hyp.core.phiT ξ t (w + (k 0 • stepTauS r 0 + k 1 • stepTauS r 1)) =
          H.hyp.core.phiT ξ t w + (k 0 • stepTauS r 0 + k 1 • stepTauS r 1)) := by
  refine ⟨fun ξ hξ => (H.hyp.core.flowT_hyp hξ).1, H.hyp.core.MF_flow_margins.1,
    H.hyp.core.MF_flow_margins.2, fun t ht => ⟨fun ξ hξ w hw =>
      ⟨H.hyp.core.phiT_mem_V hξ ht hw, H.hyp.core.phiT_eq_add_PsiT hξ ht hw⟩,
    fun ξ hξ => H.hyp.core.PsiT_differentiableOn hξ ht, H.hyp.core.PsiT_lam_bound ht,
    fun ξ hξ w hw => ⟨H.hyp.core.fderiv_phiT_eq hξ ht (H.hyp.core.small_sub_U hw),
      H.hyp.core.PsiT_deriv_le hξ ht hw⟩, H.hyp.core.PsiT_deriv_lam_bound ht,
    fun ξ hξ w hw => H.hyp.core.phiT_image hξ ht hw, H.hyp.core.image_sub_small,
    fun ξ hξ w hw hwr =>
      H.hyp.core.phiT_real_of_FT_real (WaveStepHyp.FT_isRealTaylor H.hyp) hξ ht hw hwr,
    fun ξ hξ w hw k => ⟨stepDomain_U_add_int hw k, H.hyp.core.phiT_translate_int hξ ht hw k⟩⟩⟩

/-- **Step `stepW:w5:f-flow`** of `bpW:w5:flow` (non-modified case): for `|t| ≤ 1` and `ξ ∈ Π`,
`φ^t` maps `U` into `V`, `φ^t(w) - w = ∫₀ᵗ X_F(φ^τ w) dτ`, and `φ^t - id = ι Ψ^t` with `Ψ^t`
holomorphic `U → 𝒫^{p_+}` and `|Ψ^t|_{p_+,r} ≤ |t| M_F`. -/
theorem stepFlow_fFlow
    (H : StepHypSrc a p pb s r σ η τ α lam ε ε₀ ε₁ γ M0 Mω MΩ Par ω Ω P X)
    [Fact (0 < r)] :
    ∀ t ∈ Icc (-1 : ℝ) 1, ∀ ξ ∈ Par,
      DifferentiableOn ℂ (H.hyp.core.PsiT ξ t) (stepDomain r (s - 2 * σ) (r / 2)) ∧
      ∀ w ∈ stepDomain r (s - 2 * σ) (r / 2),
        H.hyp.core.phiT ξ t w ∈ stepDomain r (s - σ) r ∧
        H.hyp.core.phiT ξ t w - w = ∫ τ in (0 : ℝ)..t,
          smoothField (stepEmbedCLM a p pb H.hpb r) (stepFieldS H.ha H.hp H.hpb (H.hyp.FT ξ) r)
            (H.hyp.core.phiT ξ τ w) ∧
        H.hyp.core.phiT ξ t w = w + stepEmbedCLM a p pb H.hpb r (H.hyp.core.PsiT ξ t w) ∧
        ‖H.hyp.core.PsiT ξ t w‖ ≤
          |t| * (stepMF (stepCF τ) (stepExpT τ) α σ ε) := fun t ht ξ hξ =>
  ⟨H.hyp.core.PsiT_differentiableOn hξ ht, fun w hw =>
    ⟨H.hyp.core.phiT_mem_V hξ ht hw,
      by rw [H.hyp.core.phiT_eq_integral hξ ht hw, add_sub_cancel_left],
      H.hyp.core.phiT_eq_add_PsiT hξ ht hw, H.hyp.core.PsiT_norm_le hξ ht hw⟩⟩

/-- **Step `stepW:w5:f-par`** of `bpW:w5:flow` (non-modified case): for `|t| ≤ 1`,
`|φ^t - id|^λ_{p_+,r,U} ≤ 2M_F` (a sup bound `A₀` and a `ξ`-Lipschitz bound `A₁`,
`A₀ + λ A₁ ≤ 2M_F`). -/
theorem stepFlow_fPar
    (H : StepHypSrc a p pb s r σ η τ α lam ε ε₀ ε₁ γ M0 Mω MΩ Par ω Ω P X)
    [Fact (0 < r)] :
    ∀ t ∈ Icc (-1 : ℝ) 1, ∃ A₀ A₁ : ℝ, 0 ≤ A₀ ∧ 0 ≤ A₁ ∧
      A₀ + lam * A₁ ≤ 2 * (stepMF (stepCF τ) (stepExpT τ) α σ ε) ∧
      ∀ ξ ∈ Par, ∀ ζ ∈ Par, ∀ w ∈ stepDomain r (s - 2 * σ) (r / 2),
        ‖H.hyp.core.PsiT ξ t w‖ ≤ A₀ ∧
        ‖H.hyp.core.PsiT ξ t w - H.hyp.core.PsiT ζ t w‖ ≤ A₁ * ‖ξ - ζ‖ :=
  fun _ ht => H.hyp.core.PsiT_lam_bound ht

/-- **Step `stepW:w5:f-der`** of `bpW:w5:flow` (non-modified case): for `|t| ≤ 1`, on
`D(s-3σ, r/4)`: `Dφ^t - I = ι DΨ^t`, `|DΨ^t|_{p→p_+,r} ≤ 8M_F/σ`, `|DΨ^t|^λ ≤ 16M_F/σ`, and
`16M_F/σ ≤ η²`. -/
theorem stepFlow_fDer
    (H : StepHypSrc a p pb s r σ η τ α lam ε ε₀ ε₁ γ M0 Mω MΩ Par ω Ω P X)
    [Fact (0 < r)] :
    ∀ t ∈ Icc (-1 : ℝ) 1,
      (∀ ξ ∈ Par, ∀ w ∈ stepDomain r (s - 3 * σ) (r / 4),
        fderiv ℂ (H.hyp.core.phiT ξ t) w = ContinuousLinearMap.id ℂ _ +
          (stepEmbedCLM a p pb H.hpb r).comp (fderiv ℂ (H.hyp.core.PsiT ξ t) w) ∧
        ‖fderiv ℂ (H.hyp.core.PsiT ξ t) w‖ ≤
          8 * (stepMF (stepCF τ) (stepExpT τ) α σ ε) / σ) ∧
      (∃ B₀ B₁ : ℝ, 0 ≤ B₀ ∧ 0 ≤ B₁ ∧
        B₀ + lam * B₁ ≤ 16 * (stepMF (stepCF τ) (stepExpT τ) α σ ε) / σ ∧
        ∀ ξ ∈ Par, ∀ ζ ∈ Par, ∀ w ∈ stepDomain r (s - 3 * σ) (r / 4),
          ‖fderiv ℂ (H.hyp.core.PsiT ξ t) w‖ ≤ B₀ ∧
          ‖fderiv ℂ (H.hyp.core.PsiT ξ t) w - fderiv ℂ (H.hyp.core.PsiT ζ t) w‖ ≤
            B₁ * ‖ξ - ζ‖) ∧
      16 * (stepMF (stepCF τ) (stepExpT τ) α σ ε) / σ ≤
        η ^ 2 := fun _ ht =>
  ⟨fun _ hξ _ hw => ⟨H.hyp.core.fderiv_phiT_eq hξ ht (H.hyp.core.small_sub_U hw),
    H.hyp.core.PsiT_deriv_le hξ ht hw⟩, H.hyp.core.PsiT_deriv_lam_bound ht⟩

/-- **The flow with explicit margins** (blueprint Lemma `bpW:w5:flow`, modified case).
Under the step data `H` (which include the smallness condition), apply the W1 flow lemma to
`X = X_{F(ξ)}` with `V = D(s-σ, r)`, `U = D(s-2σ, r/2)`, `δ = σ/4`, `M = M_F`: the hypotheses
hold, `M_F ≤ σ/256`,
`L = M/δ ≤ 1/64`, and for `|t| ≤ 1`, `ξ, ζ ∈ Π`: (i) `φ^t` maps `U` into `V`,
`φ^t - id = ι Ψ^t` with `Ψ^t` holomorphic `U → 𝒫^{p_+}`, and `|φ^t - id|^λ_{p_+,r,U} ≤ 2M_F`;
(ii) on `D(s-3σ, r/4)`: `|Dφ^t - I|_{p→p_+,r} ≤ 8M_F/σ` and `|Dφ^t - I|^λ ≤ 16M_F/σ ≤ η²`;
(iii) `φ^t(D(s-5σ, ηr)) ⊆ D(s-4σ, 2ηr) ⊆ D(s-3σ, r/4)`; (iv) `φ^t` is real on real points and
commutes with the integer angle translations `τ_k`, `k ∈ ℤ²` (`U + τ_k = U`). -/
theorem stepFlowLemmaMod
    (H : StepHypModSrc a p pb s r σ η τ α β lam ε ε₀ ε₁ γ M0 Mω MΩ Par ω Ω P X)
    [Fact (0 < r)] :
    -- the hypotheses of the W1 flow lemma
    (∀ ξ ∈ Par, FlowHyp (smoothField (stepEmbedCLM a p pb H.hpb r)
        (stepFieldS H.ha H.hp H.hpb (H.hyp.FT ξ) r))
      (stepDomain r (s - σ) r) (stepDomain r (s - 2 * σ) (r / 2))
      (stepMF (stepCFn τ) (stepTn τ) α σ ε) (σ / 4)) ∧
    (stepMF (stepCFn τ) (stepTn τ) α σ ε) ≤ σ / 256 ∧
    (stepMF (stepCFn τ) (stepTn τ) α σ ε) / (σ / 4) ≤ 1 / 64 ∧
    ∀ t ∈ Icc (-1 : ℝ) 1,
      -- (i)
      (∀ ξ ∈ Par, ∀ w ∈ stepDomain r (s - 2 * σ) (r / 2),
        H.hyp.core.phiT ξ t w ∈ stepDomain r (s - σ) r ∧
        H.hyp.core.phiT ξ t w = w + stepEmbedCLM a p pb H.hpb r (H.hyp.core.PsiT ξ t w)) ∧
      (∀ ξ ∈ Par, DifferentiableOn ℂ (H.hyp.core.PsiT ξ t) (stepDomain r (s - 2 * σ) (r / 2))) ∧
      (∃ A₀ A₁ : ℝ, 0 ≤ A₀ ∧ 0 ≤ A₁ ∧
        A₀ + lam * A₁ ≤ 2 * (stepMF (stepCFn τ) (stepTn τ) α σ ε) ∧
        ∀ ξ ∈ Par, ∀ ζ ∈ Par, ∀ w ∈ stepDomain r (s - 2 * σ) (r / 2),
          ‖H.hyp.core.PsiT ξ t w‖ ≤ A₀ ∧
          ‖H.hyp.core.PsiT ξ t w - H.hyp.core.PsiT ζ t w‖ ≤ A₁ * ‖ξ - ζ‖) ∧
      -- (ii)
      (∀ ξ ∈ Par, ∀ w ∈ stepDomain r (s - 3 * σ) (r / 4),
        fderiv ℂ (H.hyp.core.phiT ξ t) w = ContinuousLinearMap.id ℂ _ +
          (stepEmbedCLM a p pb H.hpb r).comp (fderiv ℂ (H.hyp.core.PsiT ξ t) w) ∧
        ‖fderiv ℂ (H.hyp.core.PsiT ξ t) w‖ ≤
          8 * (stepMF (stepCFn τ) (stepTn τ) α σ ε) / σ) ∧
      ((∃ B₀ B₁ : ℝ, 0 ≤ B₀ ∧ 0 ≤ B₁ ∧
        B₀ + lam * B₁ ≤ 16 * (stepMF (stepCFn τ) (stepTn τ) α σ ε) / σ ∧
        ∀ ξ ∈ Par, ∀ ζ ∈ Par, ∀ w ∈ stepDomain r (s - 3 * σ) (r / 4),
          ‖fderiv ℂ (H.hyp.core.PsiT ξ t) w‖ ≤ B₀ ∧
          ‖fderiv ℂ (H.hyp.core.PsiT ξ t) w - fderiv ℂ (H.hyp.core.PsiT ζ t) w‖ ≤
            B₁ * ‖ξ - ζ‖) ∧
        16 * (stepMF (stepCFn τ) (stepTn τ) α σ ε) / σ ≤
          η ^ 2) ∧
      -- (iii)
      (∀ ξ ∈ Par, ∀ w ∈ stepDomain r (s - 5 * σ) (η * r),
        H.hyp.core.phiT ξ t w ∈ stepDomain r (s - 4 * σ) (2 * η * r)) ∧
      stepDomain r (s - 4 * σ) (2 * η * r) ⊆ stepDomain r (s - 3 * σ) (r / 4) ∧
      -- (iv)
      (∀ ξ ∈ Par, ∀ w ∈ stepDomain r (s - 2 * σ) (r / 2), StepReal (StepPhase.toK w) →
        StepReal (StepPhase.toK (H.hyp.core.phiT ξ t w))) ∧
      (∀ ξ ∈ Par, ∀ w ∈ stepDomain r (s - 2 * σ) (r / 2), ∀ k : Fin 2 → ℤ,
        w + (k 0 • stepTauS r 0 + k 1 • stepTauS r 1) ∈ stepDomain r (s - 2 * σ) (r / 2) ∧
        H.hyp.core.phiT ξ t (w + (k 0 • stepTauS r 0 + k 1 • stepTauS r 1)) =
          H.hyp.core.phiT ξ t w + (k 0 • stepTauS r 0 + k 1 • stepTauS r 1)) := by
  refine ⟨fun ξ hξ => (H.hyp.core.flowT_hyp hξ).1, H.hyp.core.MF_flow_margins.1,
    H.hyp.core.MF_flow_margins.2, fun t ht => ⟨fun ξ hξ w hw =>
      ⟨H.hyp.core.phiT_mem_V hξ ht hw, H.hyp.core.phiT_eq_add_PsiT hξ ht hw⟩,
    fun ξ hξ => H.hyp.core.PsiT_differentiableOn hξ ht, H.hyp.core.PsiT_lam_bound ht,
    fun ξ hξ w hw => ⟨H.hyp.core.fderiv_phiT_eq hξ ht (H.hyp.core.small_sub_U hw),
      H.hyp.core.PsiT_deriv_le hξ ht hw⟩, H.hyp.core.PsiT_deriv_lam_bound ht,
    fun ξ hξ w hw => H.hyp.core.phiT_image hξ ht hw, H.hyp.core.image_sub_small,
    fun ξ hξ w hw hwr =>
      H.hyp.core.phiT_real_of_FT_real (StepHypMod.FT_isRealTaylor H.hyp) hξ ht hw hwr,
    fun ξ hξ w hw k => ⟨stepDomain_U_add_int hw k, H.hyp.core.phiT_translate_int hξ ht hw k⟩⟩⟩

/-- **Step `stepW:w5:f-flow`** of `bpW:w5:flow` (modified case): for `|t| ≤ 1` and `ξ ∈ Π`,
`φ^t` maps `U` into `V`, `φ^t(w) - w = ∫₀ᵗ X_F(φ^τ w) dτ`, and `φ^t - id = ι Ψ^t` with `Ψ^t`
holomorphic `U → 𝒫^{p_+}` and `|Ψ^t|_{p_+,r} ≤ |t| M_F`. -/
theorem stepFlowMod_fFlow
    (H : StepHypModSrc a p pb s r σ η τ α β lam ε ε₀ ε₁ γ M0 Mω MΩ Par ω Ω P X)
    [Fact (0 < r)] :
    ∀ t ∈ Icc (-1 : ℝ) 1, ∀ ξ ∈ Par,
      DifferentiableOn ℂ (H.hyp.core.PsiT ξ t) (stepDomain r (s - 2 * σ) (r / 2)) ∧
      ∀ w ∈ stepDomain r (s - 2 * σ) (r / 2),
        H.hyp.core.phiT ξ t w ∈ stepDomain r (s - σ) r ∧
        H.hyp.core.phiT ξ t w - w = ∫ τ in (0 : ℝ)..t,
          smoothField (stepEmbedCLM a p pb H.hpb r) (stepFieldS H.ha H.hp H.hpb (H.hyp.FT ξ) r)
            (H.hyp.core.phiT ξ τ w) ∧
        H.hyp.core.phiT ξ t w = w + stepEmbedCLM a p pb H.hpb r (H.hyp.core.PsiT ξ t w) ∧
        ‖H.hyp.core.PsiT ξ t w‖ ≤
          |t| * (stepMF (stepCFn τ) (stepTn τ) α σ ε) := fun t ht ξ hξ =>
  ⟨H.hyp.core.PsiT_differentiableOn hξ ht, fun w hw =>
    ⟨H.hyp.core.phiT_mem_V hξ ht hw,
      by rw [H.hyp.core.phiT_eq_integral hξ ht hw, add_sub_cancel_left],
      H.hyp.core.phiT_eq_add_PsiT hξ ht hw, H.hyp.core.PsiT_norm_le hξ ht hw⟩⟩

/-- **Step `stepW:w5:f-par`** of `bpW:w5:flow` (modified case): for `|t| ≤ 1`,
`|φ^t - id|^λ_{p_+,r,U} ≤ 2M_F` (a sup bound `A₀` and a `ξ`-Lipschitz bound `A₁`,
`A₀ + λ A₁ ≤ 2M_F`). -/
theorem stepFlowMod_fPar
    (H : StepHypModSrc a p pb s r σ η τ α β lam ε ε₀ ε₁ γ M0 Mω MΩ Par ω Ω P X)
    [Fact (0 < r)] :
    ∀ t ∈ Icc (-1 : ℝ) 1, ∃ A₀ A₁ : ℝ, 0 ≤ A₀ ∧ 0 ≤ A₁ ∧
      A₀ + lam * A₁ ≤ 2 * (stepMF (stepCFn τ) (stepTn τ) α σ ε) ∧
      ∀ ξ ∈ Par, ∀ ζ ∈ Par, ∀ w ∈ stepDomain r (s - 2 * σ) (r / 2),
        ‖H.hyp.core.PsiT ξ t w‖ ≤ A₀ ∧
        ‖H.hyp.core.PsiT ξ t w - H.hyp.core.PsiT ζ t w‖ ≤ A₁ * ‖ξ - ζ‖ :=
  fun _ ht => H.hyp.core.PsiT_lam_bound ht

/-- **Step `stepW:w5:f-der`** of `bpW:w5:flow` (modified case): for `|t| ≤ 1`, on
`D(s-3σ, r/4)`: `Dφ^t - I = ι DΨ^t`, `|DΨ^t|_{p→p_+,r} ≤ 8M_F/σ`, `|DΨ^t|^λ ≤ 16M_F/σ`, and
`16M_F/σ ≤ η²`. -/
theorem stepFlowMod_fDer
    (H : StepHypModSrc a p pb s r σ η τ α β lam ε ε₀ ε₁ γ M0 Mω MΩ Par ω Ω P X)
    [Fact (0 < r)] :
    ∀ t ∈ Icc (-1 : ℝ) 1,
      (∀ ξ ∈ Par, ∀ w ∈ stepDomain r (s - 3 * σ) (r / 4),
        fderiv ℂ (H.hyp.core.phiT ξ t) w = ContinuousLinearMap.id ℂ _ +
          (stepEmbedCLM a p pb H.hpb r).comp (fderiv ℂ (H.hyp.core.PsiT ξ t) w) ∧
        ‖fderiv ℂ (H.hyp.core.PsiT ξ t) w‖ ≤
          8 * (stepMF (stepCFn τ) (stepTn τ) α σ ε) / σ) ∧
      (∃ B₀ B₁ : ℝ, 0 ≤ B₀ ∧ 0 ≤ B₁ ∧
        B₀ + lam * B₁ ≤ 16 * (stepMF (stepCFn τ) (stepTn τ) α σ ε) / σ ∧
        ∀ ξ ∈ Par, ∀ ζ ∈ Par, ∀ w ∈ stepDomain r (s - 3 * σ) (r / 4),
          ‖fderiv ℂ (H.hyp.core.PsiT ξ t) w‖ ≤ B₀ ∧
          ‖fderiv ℂ (H.hyp.core.PsiT ξ t) w - fderiv ℂ (H.hyp.core.PsiT ζ t) w‖ ≤
            B₁ * ‖ξ - ζ‖) ∧
      16 * (stepMF (stepCFn τ) (stepTn τ) α σ ε) / σ ≤
        η ^ 2 := fun _ ht =>
  ⟨fun _ hξ _ hw => ⟨H.hyp.core.fderiv_phiT_eq hξ ht (H.hyp.core.small_sub_U hw),
    H.hyp.core.PsiT_deriv_le hξ ht hw⟩, H.hyp.core.PsiT_deriv_lam_bound ht⟩

end KAM.Wave
