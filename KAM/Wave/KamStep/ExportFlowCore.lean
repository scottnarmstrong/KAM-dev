/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.KamStep.StepPsi
public import KAM.Wave.KamStep.RealStep
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The step flow `φ^t` at every time `|t| ≤ 1` (blueprint `bpW:w5:flow`, core layer)

For the step core `H` and `ξ ∈ Π`, `φ^t_ξ = H.phiT ξ t` is the time-`t` map of the flow of
`X_{F(ξ)} = ι ∘ Z_ξ` (`Z_ξ = stepFieldS (FT ξ)`, values in the `p_+`-representatives,
`ι = stepEmbedCLM`) and `Ψ^t_ξ = H.PsiT ξ t = ∫₀ᵗ Z_ξ(φ^τ_ξ ·) dτ` its smoothing displacement;
`H.phiT ξ 1 = H.Phi ξ`, `H.PsiT ξ 1 = H.Psi ξ` (by definition). With `V = D(s-σ, r)`,
`U = D(s-2σ, r/2)`, `δ = σ/4` and `M_F = stepMF cF tF α σ ε`, for every `t ∈ [-1, 1]`:

* `flowT_hyp`: the hypotheses of the W1 flow lemma (`FlowHyp`) with `M = M_F`, `M_F ≤ σ/256`,
  `M_F/δ ≤ 1/64`;
* `phiT_mem_V`, `phiT_eq_integral`, `phiT_eq_add_PsiT`, `PsiT_differentiableOn`, `PsiT_norm_le`
  (step `f-flow`): `φ^t(U) ⊆ V`, `φ^t w = w + ∫₀ᵗ X_F(φ^τ w) dτ = w + ι Ψ^t w`, `Ψ^t` holomorphic
  on `U`, `|Ψ^t w|_{p_+,r} ≤ |t| M_F`;
* `PsiT_lam_bound` (step `f-par`, clause (i)): `|φ^t - id|^λ_{p_+,r,U} ≤ 2 M_F`;
* `fderiv_phiT_eq`, `PsiT_deriv_le`, `PsiT_deriv_lam_bound` (step `f-der`, clause (ii)) on
  `D(s-3σ, r/4)`: `Dφ^t = I + ι ∘ DΨ^t`, `|DΨ^t| ≤ 8M_F/σ`, `|DΨ^t|^λ ≤ 16M_F/σ ≤ η²`;
* `phiT_image` (clause (iii)): `φ^t(D(s-5σ, ηr)) ⊆ D(s-4σ, 2ηr) ⊆ D(s-3σ, r/4)`;
* `phiT_translate_int` (clause (iv)): `φ^t(w + τ_k) = φ^t(w) + τ_k`, `k ∈ ℤ²`, `w ∈ U`;
* `phiT_real_of_FT_real` (clause (iv), hypothesis-taking variant: it assumes the abstract family
  `FT` real, which `StepCore` does not record; the source-facing exports in `ExportFlow` discharge
  it).

These are lemmas about the abstract `StepCore`; the source-facing statements, with only the step
data `StepHypSrc` / `StepHypModSrc` as hypotheses, are in `KAM.Wave.KamStep.ExportFlow`.
-/

@[expose] public noncomputable section

open Set Metric

namespace KAM.Wave

open KAM

/-- `FlowHyp` is monotone in the field bound `M` (below `δ`). -/
theorem FlowHyp.weakenFieldBound {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] {X : F → F}
    {V U : Set F} {M M' δ : ℝ} (h : FlowHyp X V U M δ) (hMM : M ≤ M') (hM' : M' < δ) :
    FlowHyp X V U M' δ :=
  ⟨h.isOpen_V, h.isOpen_U, h.holo, fun z hz => (h.bound z hz).trans hMM, h.margin,
    h.M_pos.trans_le hMM, hM'⟩

variable {a p pb s r σ η τ α lam ε ε₀ ε₁ γ M0 Mω MΩ M₀ M₁ cF tF : ℝ} {Par : Set (Fin 2 → ℝ)}
  {ω : (Fin 2 → ℝ) → Fin 2 → ℝ} {Ω : (Fin 2 → ℝ) → ℕ+ → ℝ}
  {P : (Fin 2 → ℝ) → KamPhase → ℂ} {X : (Fin 2 → ℝ) → KamPhase → KamPhase}
  {FT : (Fin 2 → ℝ) → HomTaylor_gen a p pb (s - σ)} [Fact (0 < r)]

omit [Fact (0 < r)] in
/-- `U + τ_k = U` for `k ∈ ℤ²`. -/
theorem stepDomain_U_add_int {w : StepPhase r} (hw : w ∈ stepDomain r (s - 2 * σ) (r / 2))
    (k : Fin 2 → ℤ) :
    w + (k 0 • stepTauS r 0 + k 1 • stepTauS r 1) ∈ stepDomain r (s - 2 * σ) (r / 2) := by
  have hlaw := fun i : Fin 2 => shift_int_law (D := stepDomain r (s - 2 * σ) (r / 2))
    (f := id) (τ := stepTauS r i) (fun w hw => stepDomain_add_tauS hw i)
    (fun w hw => stepDomain_sub_tauS hw i) (fun _ _ => rfl)
  obtain ⟨h1, -⟩ := hlaw 0 (k 0) w hw
  obtain ⟨h2, -⟩ := hlaw 1 (k 1) _ h1
  rw [← add_assoc]; exact h2

namespace StepCore

variable (H : StepCore a p pb s r σ η τ α lam ε ε₀ ε₁ γ M0 Mω MΩ M₀ M₁ cF tF Par ω Ω P X FT)

/-- The time-`t` map `φ^t_ξ` of the flow of `X_{F(ξ)}` (`bpW:w5:flow`). -/
def phiT (ξ : Fin 2 → ℝ) (t : ℝ) : StepPhase r → StepPhase r :=
  holoFlow (smoothField (stepEmbedCLM a p pb H.hpb r) (stepFieldS H.ha H.hp H.hpb (FT ξ) r)) t

/-- The smoothing displacement `Ψ^t_ξ = ∫₀ᵗ Z_ξ(φ^τ_ξ ·) dτ` (values in the `p_+`-representatives).
-/
def PsiT (ξ : Fin 2 → ℝ) (t : ℝ) : StepPhase r → StepPhase r :=
  smoothDisp (stepEmbedCLM a p pb H.hpb r) (stepFieldS H.ha H.hp H.hpb (FT ξ) r) t

theorem phiT_one (ξ : Fin 2 → ℝ) : H.phiT ξ 1 = H.Phi ξ := rfl

include H

omit [Fact (0 < r)] in
theorem M₀_le_MF : M₀ ≤ stepMF cF tF α σ ε := by
  have := mul_nonneg H.hlam0 H.M₁_nonneg
  linarith [H.M_sum]

omit [Fact (0 < r)] in
theorem MF_margins :
    stepMF cF tF α σ ε ≤ σ / 1024 ∧ stepMF cF tF α σ ε / (σ / 4) ≤ 1 / 256 ∧
      16 * stepMF cF tF α σ ε / σ ≤ η ^ 2 :=
  stepMF_margins H.hσ H.hη0 H.hη H.mf_small

theorem M₀_div_le : M₀ / (σ / 4) ≤ 1 / 64 := by
  have := H.mf_le_sigma
  have := H.hσ
  rw [div_le_iff₀ (by positivity)]; linarith

omit [Fact (0 < r)] in
/-- `M_F ≤ σ/256` and `L = M_F/δ ≤ 1/64` (`δ = σ/4`, `bpW:w5:flow`). -/
theorem MF_flow_margins :
    stepMF cF tF α σ ε ≤ σ / 256 ∧ stepMF cF tF α σ ε / (σ / 4) ≤ 1 / 64 := by
  obtain ⟨h1, h2, -⟩ := H.MF_margins
  have hσ := H.hσ
  exact ⟨by linarith, by linarith⟩

/-- **The hypotheses of the W1 flow lemma hold** (`bpW:w5:flow`): `FlowHyp` for `X_{F(ξ)}` with
`V = D(s-σ, r)`, `U = D(s-2σ, r/2)`, `M = M_F`, `δ = σ/4`; `M_F ≤ σ/256` and `M_F/δ ≤ 1/64`. -/
theorem flowT_hyp {ξ : Fin 2 → ℝ} (hξ : ξ ∈ Par) :
    FlowHyp (smoothField (stepEmbedCLM a p pb H.hpb r) (stepFieldS H.ha H.hp H.hpb (FT ξ) r))
        (stepDomain r (s - σ) r) (stepDomain r (s - 2 * σ) (r / 2)) (stepMF cF tF α σ ε)
        (σ / 4) ∧
      stepMF cF tF α σ ε ≤ σ / 256 ∧ stepMF cF tF α σ ε / (σ / 4) ≤ 1 / 64 := by
  obtain ⟨h1, h2⟩ := H.MF_flow_margins
  have hσ := H.hσ
  exact ⟨(H.flow_data hξ).1.weakenFieldBound H.M₀_le_MF (by linarith), h1, h2⟩

/-- `φ^t` maps `U` into `V` (`bpW:w5:flow` (i)). -/
theorem phiT_mem_V {ξ : Fin 2 → ℝ} (hξ : ξ ∈ Par) {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1)
    {w : StepPhase r} (hw : w ∈ stepDomain r (s - 2 * σ) (r / 2)) :
    H.phiT ξ t w ∈ stepDomain r (s - σ) r :=
  (H.flow_data hξ).1.mem_V_of_ball hw (holoFlow_mem_ball (H.flow_data hξ).1 hw ht)

/-- The integral identity `φ^t w = w + ∫₀ᵗ X_F(φ^τ w) dτ` on `U` (step `f-flow`). -/
theorem phiT_eq_integral {ξ : Fin 2 → ℝ} (hξ : ξ ∈ Par) {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1)
    {w : StepPhase r} (hw : w ∈ stepDomain r (s - 2 * σ) (r / 2)) :
    H.phiT ξ t w = w + ∫ τ in (0 : ℝ)..t,
      smoothField (stepEmbedCLM a p pb H.hpb r) (stepFieldS H.ha H.hp H.hpb (FT ξ) r)
        (H.phiT ξ τ w) :=
  holoFlow_eq_integral (H.flow_data hξ).1 hw ht

/-- `φ^t = id + ι ∘ Ψ^t` on `U` (step `f-flow`). -/
theorem phiT_eq_add_PsiT {ξ : Fin 2 → ℝ} (hξ : ξ ∈ Par) {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1)
    {w : StepPhase r} (hw : w ∈ stepDomain r (s - 2 * σ) (r / 2)) :
    H.phiT ξ t w = w + stepEmbedCLM a p pb H.hpb r (H.PsiT ξ t w) :=
  holoFlow_smooth_eq (H.flow_data hξ).1 (H.flow_data hξ).2.1 hw ht

/-- `Ψ^t = φ^t - id` (as a `p_+`-valued map) is holomorphic on `U` (step `f-flow`). -/
theorem PsiT_differentiableOn {ξ : Fin 2 → ℝ} (hξ : ξ ∈ Par) {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    DifferentiableOn ℂ (H.PsiT ξ t) (stepDomain r (s - 2 * σ) (r / 2)) :=
  differentiableOn_smoothDisp (H.flow_data hξ).1 (H.flow_data hξ).2.1 (H.flow_data hξ).2.2 ht

/-- `|Ψ^t w|_{p_+,r} ≤ |t| M_F` on `U` (step `f-flow`). -/
theorem PsiT_norm_le {ξ : Fin 2 → ℝ} (hξ : ξ ∈ Par) {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1)
    {w : StepPhase r} (hw : w ∈ stepDomain r (s - 2 * σ) (r / 2)) :
    ‖H.PsiT ξ t w‖ ≤ |t| * stepMF cF tF α σ ε := by
  have h := norm_smoothDisp_le (H.flow_data hξ).1 (H.flow_data hξ).2.2 hw ht
  rw [mul_comm] at h
  exact h.trans (mul_le_mul_of_nonneg_left H.M₀_le_MF (abs_nonneg t))

theorem PsiT_norm_le_M₀ {ξ : Fin 2 → ℝ} (hξ : ξ ∈ Par) {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1)
    {w : StepPhase r} (hw : w ∈ stepDomain r (s - 2 * σ) (r / 2)) : ‖H.PsiT ξ t w‖ ≤ M₀ :=
  flowII_disp (H.flow_data hξ).1 (H.flow_data hξ).2.2 hw ht

theorem PsiT_sub_le {ξ ζ : Fin 2 → ℝ} (hξ : ξ ∈ Par) (hζ : ζ ∈ Par) {t : ℝ}
    (ht : t ∈ Icc (-1 : ℝ) 1) {w : StepPhase r} (hw : w ∈ stepDomain r (s - 2 * σ) (r / 2)) :
    ‖H.PsiT ξ t w - H.PsiT ζ t w‖ ≤ 2 * (M₁ * ‖ξ - ζ‖) := by
  obtain ⟨hFl₁, hZ₁, -⟩ := H.flow_data hξ
  obtain ⟨hFl₂, hZ₂, hb₂⟩ := H.flow_data hζ
  have hZZ : ∀ z ∈ stepDomain r (s - σ) r,
      ‖stepFieldS H.ha H.hp H.hpb (FT ξ) r z - stepFieldS H.ha H.hp H.hpb (FT ζ) r z‖ ≤
        M₁ * ‖ξ - ζ‖ := fun z hz => by
    rw [← stepFieldS_sub H.ha H.hp H.hpb (FT ξ) (FT ζ) (stepDomain_theta_mem le_rfl hz)]
    exact stepFieldS_bound H.ha H.hp H.hpb _ r (H.F_sub ξ hξ ζ hζ) le_rfl hz
  exact flowII_disp_sub hFl₁ hFl₂ hZ₁ hZ₂ (norm_stepEmbedCLM_apply_le a p pb H.hpb r) hb₂
    H.M₀_div_le (mul_nonneg H.M₁_nonneg (norm_nonneg _)) hZZ hw ht

/-- **`|φ^t - id|^λ_{p_+,r,U} ≤ 2 M_F`** (`bpW:w5:flow` (i), step `f-par`), as a sup bound `A₀`
and a `ξ`-Lipschitz bound `A₁` with `A₀ + λ A₁ ≤ 2 M_F`. -/
theorem PsiT_lam_bound {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    ∃ A₀ A₁ : ℝ, 0 ≤ A₀ ∧ 0 ≤ A₁ ∧ A₀ + lam * A₁ ≤ 2 * stepMF cF tF α σ ε ∧
      ∀ ξ ∈ Par, ∀ ζ ∈ Par, ∀ w ∈ stepDomain r (s - 2 * σ) (r / 2),
        ‖H.PsiT ξ t w‖ ≤ A₀ ∧ ‖H.PsiT ξ t w - H.PsiT ζ t w‖ ≤ A₁ * ‖ξ - ζ‖ := by
  have hM0 := H.M₀_pos.le
  have hM1 := H.M₁_nonneg
  have hlam := H.hlam0
  have hsum := H.M_sum
  refine ⟨M₀, 2 * M₁, hM0, by positivity, by nlinarith, fun ξ hξ ζ hζ w hw =>
    ⟨H.PsiT_norm_le_M₀ hξ ht hw, (H.PsiT_sub_le hξ hζ ht hw).trans_eq (by ring)⟩⟩

omit [Fact (0 < r)] in
theorem small_sub_U : stepDomain r (s - 3 * σ) (r / 4) ⊆ stepDomain r (s - 2 * σ) (r / 2) :=
  stepDomain_mono' (by linarith [H.hσ]) (by have := H.hr; positivity) (by have := H.hr; linarith)

/-- `Dφ^t(w) = I + ι ∘ DΨ^t(w)` on `U` (`DΨ^t(w) : 𝒫^p → 𝒫^{p_+}`). -/
theorem fderiv_phiT_eq {ξ : Fin 2 → ℝ} (hξ : ξ ∈ Par) {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1)
    {w : StepPhase r} (hw : w ∈ stepDomain r (s - 2 * σ) (r / 2)) :
    fderiv ℂ (H.phiT ξ t) w =
      ContinuousLinearMap.id ℂ _ + (stepEmbedCLM a p pb H.hpb r).comp (fderiv ℂ (H.PsiT ξ t) w) :=
  fderiv_holoFlow_smooth (H.flow_data hξ).1 (H.flow_data hξ).2.1 (H.flow_data hξ).2.2 hw ht

theorem PsiT_deriv_le_M₀ {ξ : Fin 2 → ℝ} (hξ : ξ ∈ Par) {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1)
    {w : StepPhase r} (hw : w ∈ stepDomain r (s - 3 * σ) (r / 4)) :
    ‖fderiv ℂ (H.PsiT ξ t) w‖ ≤ 8 * M₀ / σ := by
  have hσ := H.hσ
  have hball := stepDomain_U_margin hσ H.hσ1 (by linarith [H.hσs]) hw
  have := flowII_deriv (H.flow_data hξ).1 (H.flow_data hξ).2.1 (H.flow_data hξ).2.2
    (by positivity : (0 : ℝ) < σ / 8) hball ht
  exact this.trans_eq (by field_simp)

/-- `|Dφ^t - I|_{p→p_+,r} = |DΨ^t|_{p→p_+,r} ≤ 8 M_F/σ` on `D(s-3σ, r/4)` (`bpW:w5:flow` (ii)). -/
theorem PsiT_deriv_le {ξ : Fin 2 → ℝ} (hξ : ξ ∈ Par) {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1)
    {w : StepPhase r} (hw : w ∈ stepDomain r (s - 3 * σ) (r / 4)) :
    ‖fderiv ℂ (H.PsiT ξ t) w‖ ≤ 8 * stepMF cF tF α σ ε / σ :=
  (H.PsiT_deriv_le_M₀ hξ ht hw).trans
    (div_le_div_of_nonneg_right (by linarith [H.M₀_le_MF]) H.hσ.le)

theorem PsiT_deriv_sub_le {ξ ζ : Fin 2 → ℝ} (hξ : ξ ∈ Par) (hζ : ζ ∈ Par) {t : ℝ}
    (ht : t ∈ Icc (-1 : ℝ) 1) {w : StepPhase r} (hw : w ∈ stepDomain r (s - 3 * σ) (r / 4)) :
    ‖fderiv ℂ (H.PsiT ξ t) w - fderiv ℂ (H.PsiT ζ t) w‖ ≤ 16 * (M₁ * ‖ξ - ζ‖) / σ := by
  have hσ := H.hσ
  obtain ⟨hFl₁, hZ₁, hb₁⟩ := H.flow_data hξ
  obtain ⟨hFl₂, hZ₂, hb₂⟩ := H.flow_data hζ
  have hZZ : ∀ z ∈ stepDomain r (s - σ) r,
      ‖stepFieldS H.ha H.hp H.hpb (FT ξ) r z - stepFieldS H.ha H.hp H.hpb (FT ζ) r z‖ ≤
        M₁ * ‖ξ - ζ‖ := fun z hz => by
    rw [← stepFieldS_sub H.ha H.hp H.hpb (FT ξ) (FT ζ) (stepDomain_theta_mem le_rfl hz)]
    exact stepFieldS_bound H.ha H.hp H.hpb _ r (H.F_sub ξ hξ ζ hζ) le_rfl hz
  have hball := stepDomain_U_margin hσ H.hσ1 (by linarith [H.hσs]) hw
  have := flowII_deriv_sub hFl₁ hFl₂ hZ₁ hb₁ hZ₂ hb₂ (norm_stepEmbedCLM_apply_le a p pb H.hpb r)
    H.M₀_div_le (mul_nonneg H.M₁_nonneg (norm_nonneg _)) hZZ (by positivity : (0 : ℝ) < σ / 8)
    hball ht
  exact this.trans_eq (by field_simp; ring)

/-- **`|Dφ^t - I|^λ_{p→p_+,r} ≤ 16 M_F/σ ≤ η²` on `D(s-3σ, r/4)`** (`bpW:w5:flow` (ii), step
`f-der`), as a sup bound `B₀` and a `ξ`-Lipschitz bound `B₁` with `B₀ + λ B₁ ≤ 16 M_F/σ`. -/
theorem PsiT_deriv_lam_bound {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    (∃ B₀ B₁ : ℝ, 0 ≤ B₀ ∧ 0 ≤ B₁ ∧ B₀ + lam * B₁ ≤ 16 * stepMF cF tF α σ ε / σ ∧
      ∀ ξ ∈ Par, ∀ ζ ∈ Par, ∀ w ∈ stepDomain r (s - 3 * σ) (r / 4),
        ‖fderiv ℂ (H.PsiT ξ t) w‖ ≤ B₀ ∧
        ‖fderiv ℂ (H.PsiT ξ t) w - fderiv ℂ (H.PsiT ζ t) w‖ ≤ B₁ * ‖ξ - ζ‖) ∧
      16 * stepMF cF tF α σ ε / σ ≤ η ^ 2 := by
  have hM0 := H.M₀_pos.le
  have hM1 := H.M₁_nonneg
  have hσ := H.hσ
  have hlam := H.hlam0
  have hsum := H.M_sum
  refine ⟨⟨8 * M₀ / σ, 16 * M₁ / σ, by positivity, by positivity, ?_, fun ξ hξ ζ hζ w hw =>
    ⟨H.PsiT_deriv_le_M₀ hξ ht hw, (H.PsiT_deriv_sub_le hξ hζ ht hw).trans_eq (by ring)⟩⟩,
    H.MF_margins.2.2⟩
  have e : 8 * M₀ / σ + lam * (16 * M₁ / σ) = (8 * M₀ + 16 * lam * M₁) / σ := by ring
  rw [e]
  exact div_le_div_of_nonneg_right (by nlinarith) hσ.le

omit [Fact (0 < r)] in
/-- `D(s-4σ, 2ηr) ⊆ D(s-3σ, r/4)` (`bpW:w5:flow` (iii)). -/
theorem image_sub_small :
    stepDomain r (s - 4 * σ) (2 * η * r) ⊆ stepDomain r (s - 3 * σ) (r / 4) :=
  stepDomain_mono' (by linarith [H.hσ]) (by have := H.hr; have := H.hη0; positivity)
    (by have := H.hr; nlinarith [H.hη])

/-- **`φ^t(D(s-5σ, ηr)) ⊆ D(s-4σ, 2ηr)`** (`bpW:w5:flow` (iii), step `f-image`). -/
theorem phiT_image {ξ : Fin 2 → ℝ} (hξ : ξ ∈ Par) {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1)
    {w : StepPhase r} (hw : w ∈ stepDomain r (s - 5 * σ) (η * r)) :
    H.phiT ξ t w ∈ stepDomain r (s - 4 * σ) (2 * η * r) := by
  have hwU := H.Dplus_sub_U hw
  have h : ‖H.phiT ξ t w - w‖ ≤ M₀ := by
    rw [H.phiT_eq_add_PsiT hξ ht hwU, add_sub_cancel_left]
    exact (norm_stepEmbedCLM_apply_le a p pb H.hpb r _).trans (H.PsiT_norm_le_M₀ hξ ht hwU)
  have hmf : M₀ ≤ σ * η ^ 2 / 16 := by
    have := H.mf_small
    linarith [H.M₀_le_MF]
  have := stepImage_mem (s := s) H.hr H.hσ H.hσ1 H.hη0 H.hη hmf (w := StepPhase.toK w)
    (W := StepPhase.toK (H.phiT ξ t w - w)) hw (by rw [← stepPhase_norm_eq]; exact h)
  have e : StepPhase.toK w + StepPhase.toK (H.phiT ξ t w - w) = StepPhase.toK (H.phiT ξ t w) := by
    simp only [StepPhase.toK]
    exact add_sub_cancel w _
  show StepPhase.toK (H.phiT ξ t w) ∈ kamDomain (s - 4 * σ) (2 * η * r)
  rw [← e]; exact this

/-- **Integer translation law at time `t`**: `φ^t(w + k₁τ₁ + k₂τ₂) = φ^t(w) + k₁τ₁ + k₂τ₂` for
`w ∈ U`, `k ∈ ℤ²` (`bpW:w5:flow` (iv); `U + τ_k = U`). -/
theorem phiT_translate_int {ξ : Fin 2 → ℝ} (hξ : ξ ∈ Par) {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1)
    {w : StepPhase r} (hw : w ∈ stepDomain r (s - 2 * σ) (r / 2)) (k : Fin 2 → ℤ) :
    H.phiT ξ t (w + (k 0 • stepTauS r 0 + k 1 • stepTauS r 1)) =
      H.phiT ξ t w + (k 0 • stepTauS r 0 + k 1 • stepTauS r 1) := by
  have hlaw := fun i : Fin 2 => shift_int_law (D := stepDomain r (s - 2 * σ) (r / 2))
    (f := H.phiT ξ t) (τ := stepTauS r i) (fun w hw => stepDomain_add_tauS hw i)
    (fun w hw => stepDomain_sub_tauS hw i)
    (fun w hw => stepFlow_translate H.ha H.hp H.hpb H.hσ H.hσ1 (by linarith [H.hσs, H.hσ])
      (FT ξ) (H.F_field ξ hξ) H.M₀_pos H.mf_lt hw i ht)
  obtain ⟨h1, h2⟩ := hlaw 0 (k 0) w hw
  obtain ⟨-, h3⟩ := hlaw 1 (k 1) _ h1
  rw [← add_assoc, h3, h2, add_assoc]

/-- `φ^t` maps real points of `U` to real points, hypothesis-taking variant: it assumes that the
abstract solution family `FT` is real (discharged for the step data in `ExportFlow`). -/
theorem phiT_real_of_FT_real (hFT : ∀ ξ ∈ Par, (FT ξ).isRealTaylor) {ξ : Fin 2 → ℝ}
    (hξ : ξ ∈ Par) {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) {w : StepPhase r}
    (hw : w ∈ stepDomain r (s - 2 * σ) (r / 2)) (hwr : StepReal (StepPhase.toK w)) :
    StepReal (StepPhase.toK (H.phiT ξ t w)) :=
  stepFlow_real H.ha H.hp H.hpb H.hσ H.hσ1 (by linarith [H.hσs, H.hσ]) (FT ξ) (H.F_field ξ hξ)
    H.M₀_pos H.mf_lt
    (fun _ _ hzr => stepField_real H.ha H.hp H.hpb (by linarith [H.hσs, H.hσ] : 0 < s - σ) (FT ξ)
      (hFT ξ hξ) hzr)
    hw hwr ht

end StepCore

end KAM.Wave
