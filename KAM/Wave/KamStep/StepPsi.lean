/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.KamStep.StepFlowClauses
public import KAM.Wave.KamStep.StepFlowFam
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The smoothing displacement `Ψ` of the step map (blueprint-W `bpW:w5:step` (i), (v))

Off-frontier, source-faithful infrastructure (W5-STEP-B-FIX, finding F1 of `W5-STEP-B-audit-1.md`);
the dependency graph is still being built.

`Φ = φ¹` is the time-one map of the smoothing field `ι ∘ X_F` (`ι = stepEmbedCLM`, `𝒫^{p_+} → 𝒫`).
On `D_+ = D(s-5σ, ηr)` it is `Φ(w) = w + ι Ψ(w)` with the displacement `Ψ = smoothDisp ι X_F 1`
taking values in the `p_+`-representatives (`StepCore.Psi`, `StepCore.phi_eq_add_Psi`), and
`DΦ(w) = I + ι ∘ DΨ(w)` with `DΨ(w) : 𝒫^p → 𝒫^{p_+}` (`StepCore.fderiv_phi_eq`). The bounds are
in the `p_+` norms (`|·|_{p_+,r}` and `|·|_{p→p_+,r}`): no inclusion `‖ι g‖ ≤ ‖g‖` is applied.

* `stepFlow_bounds_smooth`: `|Ψ₁ w|₊ ≤ M₀`, `|Ψ₁ w - Ψ₂ w|₊ ≤ 2N`, `|DΨ₁(w)| ≤ 8M₀/σ`,
  `|DΨ₁(w) - DΨ₂(w)| ≤ 16N/σ` on `D(s-3σ, r/4)`;
* `StepCore.flow_pair_smooth` (the pair `ξ, ζ` on `D_+`), `StepCore.psi_differentiableOn`,
  `StepCore.phi_differentiableOn` (holomorphy of `Φ` on `D_+`);
* `StepCore.phi_translate_int`: `Φ(w + k₁τ₁ + k₂τ₂) = Φ(w) + k₁τ₁ + k₂τ₂` for all `k ∈ ℤ²`
  (from the unit shifts, `shift_int_law`).
-/

@[expose] public noncomputable section

open Set Metric

namespace KAM.Wave

open KAM

/-! ### Integer shifts from unit shifts -/

theorem shift_int_law {E : Type*} [AddCommGroup E] {D : Set E} {f : E → E} {τ : E}
    (hp : ∀ w ∈ D, w + τ ∈ D) (hm : ∀ w ∈ D, w - τ ∈ D) (hf : ∀ w ∈ D, f (w + τ) = f w + τ) :
    ∀ n : ℤ, ∀ w ∈ D, w + n • τ ∈ D ∧ f (w + n • τ) = f w + n • τ := by
  intro n
  induction n using Int.induction_on with
  | zero => intro w hw; simpa using hw
  | succ n ih =>
    intro w hw
    obtain ⟨h1, h2⟩ := ih w hw
    have e : w + ((n : ℤ) + 1) • τ = (w + (n : ℤ) • τ) + τ := by rw [add_smul, one_smul]; abel
    rw [e]
    exact ⟨hp _ h1, by rw [hf _ h1, h2, add_smul, one_smul]; abel⟩
  | pred n ih =>
    intro w hw
    obtain ⟨h1, h2⟩ := ih w hw
    have e : w + (-(n : ℤ) - 1) • τ = (w + (-(n : ℤ)) • τ) - τ := by rw [sub_smul, one_smul]; abel
    rw [e]
    refine ⟨hm _ h1, ?_⟩
    have h3 := hf _ (hm _ h1)
    rw [sub_add_cancel, h2] at h3
    rw [sub_smul, one_smul, ← add_sub_assoc, h3]
    abel

theorem kamDomain_sub_tau {s r : ℝ} {w : KamPhase} (hw : w ∈ kamDomain s r) (i : Fin 2) :
    w - stepTau i ∈ kamDomain s r := by
  obtain ⟨h1, h2, h3⟩ := hw
  refine ⟨fun j => ?_, by simpa [stepTau] using h2, by simpa [stepTau] using h3⟩
  have : ((w - stepTau i).1 j).im = (w.1 j).im := by
    simp only [stepTau, Prod.fst_sub, Pi.sub_apply]
    by_cases h : j = i <;> simp [Pi.single_apply, h]
  show |((w - stepTau i).1 j).im| < s
  rw [this]; exact h1 j

theorem stepDomain_sub_tauS {ρ S r' : ℝ} {w : StepPhase ρ} (hw : w ∈ stepDomain ρ S r')
    (k : Fin 2) :
    w - stepTauS ρ k ∈ stepDomain ρ S r' := kamDomain_sub_tau hw k

/-! ### The concrete bounds in the `p_+` norms -/

variable {a p pb s r σ : ℝ} [Fact (0 < r)]

/-- **The displacement bounds in the `p_+` norms** (`bpW:w5:flow` (i)-(ii), `bpW:w5:step` (v)). -/
theorem stepFlow_bounds_smooth (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) (hσ : 0 < σ)
    (hσ1 : σ ≤ 1) (hσs : 3 * σ < s) {FT₁ FT₂ : HomTaylor_gen a p pb (s - σ)} {M₀ N : ℝ}
    (hF₁ : HomFieldBound_gen ha hp hpb r M₀ FT₁) (hF₂ : HomFieldBound_gen ha hp hpb r M₀ FT₂)
    (hΔF : HomFieldBound_gen ha hp hpb r N (FT₁.homSub FT₂)) (hM0 : 0 < M₀)
    (hM : M₀ ≤ σ / 1024) (hN : 0 ≤ N) {w : StepPhase r}
    (hw : w ∈ stepDomain r (s - 3 * σ) (r / 4)) :
    ‖smoothDisp (stepEmbedCLM a p pb hpb r) (stepFieldS ha hp hpb FT₁ r) 1 w‖ ≤ M₀ ∧
      ‖smoothDisp (stepEmbedCLM a p pb hpb r) (stepFieldS ha hp hpb FT₁ r) 1 w -
        smoothDisp (stepEmbedCLM a p pb hpb r) (stepFieldS ha hp hpb FT₂ r) 1 w‖ ≤ 2 * N ∧
      ‖fderiv ℂ (smoothDisp (stepEmbedCLM a p pb hpb r) (stepFieldS ha hp hpb FT₁ r) 1) w‖ ≤
        8 * M₀ / σ ∧
      ‖fderiv ℂ (smoothDisp (stepEmbedCLM a p pb hpb r) (stepFieldS ha hp hpb FT₁ r) 1) w -
        fderiv ℂ (smoothDisp (stepEmbedCLM a p pb hpb r) (stepFieldS ha hp hpb FT₂ r) 1) w‖ ≤
          16 * N / σ := by
  have hMδ : M₀ < σ / 4 := by linarith
  have hFl₁ := stepFlowHyp_concrete' (S := s) ha hp hpb FT₁ r hσ hσ1 (by linarith : 2 * σ < s)
    le_rfl hF₁ hM0 hMδ
  have hFl₂ := stepFlowHyp_concrete' (S := s) ha hp hpb FT₂ r hσ hσ1 (by linarith : 2 * σ < s)
    le_rfl hF₂ hM0 hMδ
  have hVθ : stepDomain r (s - σ) r ⊆
      {z : StepPhase r | (StepPhase.toK z).1 ∈ complexStrip 2 (s - σ)} := fun z hz =>
    stepDomain_theta_mem le_rfl hz
  have hZ₁ := (stepFieldS_differentiableOn_theta ha hp hpb FT₁).mono hVθ
  have hZ₂ := (stepFieldS_differentiableOn_theta ha hp hpb FT₂).mono hVθ
  have hb₁ : ∀ z ∈ stepDomain r (s - σ) r, ‖stepFieldS ha hp hpb FT₁ r z‖ ≤ M₀ := fun z hz =>
    stepFieldS_bound ha hp hpb FT₁ r hF₁ le_rfl hz
  have hb₂ : ∀ z ∈ stepDomain r (s - σ) r, ‖stepFieldS ha hp hpb FT₂ r z‖ ≤ M₀ := fun z hz =>
    stepFieldS_bound ha hp hpb FT₂ r hF₂ le_rfl hz
  have hZZ : ∀ z ∈ stepDomain r (s - σ) r,
      ‖stepFieldS ha hp hpb FT₁ r z - stepFieldS ha hp hpb FT₂ r z‖ ≤ N := fun z hz => by
    rw [← stepFieldS_sub ha hp hpb FT₁ FT₂ (stepDomain_theta_mem le_rfl hz)]
    exact stepFieldS_bound ha hp hpb _ r hΔF le_rfl hz
  have hL : M₀ / (σ / 4) ≤ 1 / 64 := by
    rw [div_le_iff₀ (by positivity)]; linarith
  have hU : w ∈ stepDomain r (s - 2 * σ) (r / 2) := stepDomain_mono' (by linarith)
    (by have := Fact.out (p := 0 < r); positivity)
    (by have := Fact.out (p := 0 < r); linarith) hw
  have hball := stepDomain_U_margin hσ hσ1 hσs hw
  have h1 : (1 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨by norm_num, le_rfl⟩
  have hι := norm_stepEmbedCLM_apply_le a p pb hpb r
  refine ⟨flowII_disp hFl₁ hb₁ hU h1, flowII_disp_sub hFl₁ hFl₂ hZ₁ hZ₂ hι hb₂ hL hN hZZ hU h1,
    ?_, ?_⟩
  · have := flowII_deriv hFl₁ hZ₁ hb₁ (by positivity : (0 : ℝ) < σ / 8) hball h1
    exact this.trans_eq (by field_simp)
  · have := flowII_deriv_sub hFl₁ hFl₂ hZ₁ hb₁ hZ₂ hb₂ hι hL hN hZZ
      (by positivity : (0 : ℝ) < σ / 8) hball h1
    exact this.trans_eq (by field_simp; ring)

/-! ### The step core -/

variable {η τ α lam ε ε₀ ε₁ γ M0 Mω MΩ M₀ M₁ cF tF : ℝ} {Par : Set (Fin 2 → ℝ)}
  {ω : (Fin 2 → ℝ) → Fin 2 → ℝ} {Ω : (Fin 2 → ℝ) → ℕ+ → ℝ}
  {P : (Fin 2 → ℝ) → KamPhase → ℂ} {X : (Fin 2 → ℝ) → KamPhase → KamPhase}
  {FT : (Fin 2 → ℝ) → HomTaylor_gen a p pb (s - σ)}

namespace StepCore

variable (H : StepCore a p pb s r σ η τ α lam ε ε₀ ε₁ γ M0 Mω MΩ M₀ M₁ cF tF Par ω Ω P X FT)
include H

/-- **The smoothing displacement `Ψ` of `Φ`** (values in the `p_+`-representatives). -/
def Psi (ξ : Fin 2 → ℝ) : StepPhase r → StepPhase r :=
  smoothDisp (stepEmbedCLM a p pb H.hpb r) (stepFieldS H.ha H.hp H.hpb (FT ξ) r) 1

theorem flow_data {ξ : Fin 2 → ℝ} (hξ : ξ ∈ Par) :
    FlowHyp (smoothField (stepEmbedCLM a p pb H.hpb r) (stepFieldS H.ha H.hp H.hpb (FT ξ) r))
        (stepDomain r (s - σ) r) (stepDomain r (s - 2 * σ) (r / 2)) M₀ (σ / 4) ∧
      DifferentiableOn ℂ (stepFieldS H.ha H.hp H.hpb (FT ξ) r) (stepDomain r (s - σ) r) ∧
      ∀ z ∈ stepDomain r (s - σ) r, ‖stepFieldS H.ha H.hp H.hpb (FT ξ) r z‖ ≤ M₀ := by
  have hFl := stepFlowHyp_concrete' (S := s) H.ha H.hp H.hpb (FT ξ) r H.hσ H.hσ1
    (by linarith [H.hσs, H.hσ] : 2 * σ < s) le_rfl (H.F_field ξ hξ) H.M₀_pos H.mf_lt
  have hVθ : stepDomain r (s - σ) r ⊆
      {z : StepPhase r | (StepPhase.toK z).1 ∈ complexStrip 2 (s - σ)} := fun z hz =>
    stepDomain_theta_mem le_rfl hz
  exact ⟨hFl, (stepFieldS_differentiableOn_theta H.ha H.hp H.hpb (FT ξ)).mono hVθ,
    fun z hz => stepFieldS_bound H.ha H.hp H.hpb (FT ξ) r (H.F_field ξ hξ) le_rfl hz⟩

/-- `Φ(w) = w + ι Ψ(w)` on `D_+`. -/
theorem phi_eq_add_Psi {ξ : Fin 2 → ℝ} (hξ : ξ ∈ Par) {w : StepPhase r}
    (hw : w ∈ stepDomain r (s - 5 * σ) (η * r)) :
    H.Phi ξ w = w + stepEmbedCLM a p pb H.hpb r (H.Psi ξ w) := by
  obtain ⟨hFl, hZ, -⟩ := H.flow_data hξ
  exact holoFlow_smooth_eq hFl hZ (H.Dplus_sub_U hw) ⟨by norm_num, le_rfl⟩

/-- `DΦ(w) = I + ι ∘ DΨ(w)` on `D_+`, `DΨ(w) : 𝒫^p → 𝒫^{p_+}`. -/
theorem fderiv_phi_eq {ξ : Fin 2 → ℝ} (hξ : ξ ∈ Par) {w : StepPhase r}
    (hw : w ∈ stepDomain r (s - 5 * σ) (η * r)) :
    fderiv ℂ (H.Phi ξ) w =
      ContinuousLinearMap.id ℂ _ + (stepEmbedCLM a p pb H.hpb r).comp (fderiv ℂ (H.Psi ξ) w) := by
  obtain ⟨hFl, hZ, hb⟩ := H.flow_data hξ
  exact fderiv_holoFlow_smooth hFl hZ hb (H.Dplus_sub_U hw) ⟨by norm_num, le_rfl⟩

/-- `Ψ` is holomorphic on `D_+` (into the `p_+`-representatives). -/
theorem psi_differentiableOn {ξ : Fin 2 → ℝ} (hξ : ξ ∈ Par) :
    DifferentiableOn ℂ (H.Psi ξ) (stepDomain r (s - 5 * σ) (η * r)) := by
  obtain ⟨hFl, hZ, hb⟩ := H.flow_data hξ
  exact (differentiableOn_smoothDisp hFl hZ hb ⟨by norm_num, le_rfl⟩).mono H.Dplus_sub_U

/-- **`Φ` is holomorphic on `D_+`** (`bpW:w5:step`, opening sentence). -/
theorem phi_differentiableOn {ξ : Fin 2 → ℝ} (hξ : ξ ∈ Par) :
    DifferentiableOn ℂ (H.Phi ξ) (stepDomain r (s - 5 * σ) (η * r)) := by
  obtain ⟨hFl, -, -⟩ := H.flow_data hξ
  exact (holomorphicOn_holoFlow hFl ⟨by norm_num, le_rfl⟩).mono H.Dplus_sub_U

/-- **The four bounds of the transformation in the `p_+` norms** (pair `ξ, ζ`, on `D_+`). -/
theorem flow_pair_smooth {ξ ζ : Fin 2 → ℝ} (hξ : ξ ∈ Par) (hζ : ζ ∈ Par) {w : StepPhase r}
    (hw : w ∈ stepDomain r (s - 5 * σ) (η * r)) :
    ‖H.Psi ξ w‖ ≤ M₀ ∧ ‖H.Psi ξ w - H.Psi ζ w‖ ≤ 2 * (M₁ * ‖ξ - ζ‖) ∧
      ‖fderiv ℂ (H.Psi ξ) w‖ ≤ 8 * M₀ / σ ∧
      ‖fderiv ℂ (H.Psi ξ) w - fderiv ℂ (H.Psi ζ) w‖ ≤ 16 * (M₁ * ‖ξ - ζ‖) / σ := by
  have hN : 0 ≤ M₁ * ‖ξ - ζ‖ := mul_nonneg H.M₁_nonneg (norm_nonneg _)
  exact stepFlow_bounds_smooth H.ha H.hp H.hpb H.hσ H.hσ1 (by linarith [H.hσs, H.hσ])
    (H.F_field ξ hξ) (H.F_field ζ hζ) (H.F_sub ξ hξ ζ hζ) H.M₀_pos H.mf_le_sigma hN
    (H.Dplus_sub_small hw)

/-- **Integer translation law** `Φ(w + k₁τ₁ + k₂τ₂) = Φ(w) + k₁τ₁ + k₂τ₂`, `k ∈ ℤ²`
(`bpW:w5:step` (i), `bpW:w5:flow` (iv)). -/
theorem phi_translate_int {ξ : Fin 2 → ℝ} (hξ : ξ ∈ Par) {w : StepPhase r}
    (hw : w ∈ stepDomain r (s - 5 * σ) (η * r)) (k : Fin 2 → ℤ) :
    H.Phi ξ (w + (k 0 • stepTauS r 0 + k 1 • stepTauS r 1)) =
      H.Phi ξ w + (k 0 • stepTauS r 0 + k 1 • stepTauS r 1) := by
  have hlaw := fun i : Fin 2 => shift_int_law (D := stepDomain r (s - 5 * σ) (η * r))
    (f := H.Phi ξ) (τ := stepTauS r i) (fun w hw => stepDomain_add_tauS hw i)
    (fun w hw => stepDomain_sub_tauS hw i) (fun w hw => H.phi_translate hξ hw i)
  obtain ⟨h1, h2⟩ := hlaw 0 (k 0) w hw
  obtain ⟨-, h3⟩ := hlaw 1 (k 1) _ h1
  rw [← add_assoc, h3, h2, add_assoc]

/-- **Clause (v) in the `p_+` norms** (`bpW:w5:step` (v)):
`|Φ - id|^λ_{p_+,r,D_+} = |Ψ|^λ ≤ 2M_F` and `|DΦ - I|^λ_{p→p_+,r,D_+} = |DΨ|^λ ≤ 16M_F/σ`, as
conjunctions of sup and Lipschitz bounds. -/
theorem smooth_clause_v :
    ∃ A₀ A₁ B₀ B₁ : ℝ, 0 ≤ A₀ ∧ 0 ≤ A₁ ∧ 0 ≤ B₀ ∧ 0 ≤ B₁ ∧
      A₀ + lam * A₁ ≤ 2 * stepMF cF tF α σ ε ∧ B₀ + lam * B₁ ≤ 16 * stepMF cF tF α σ ε / σ ∧
      ∀ ξ ∈ Par, ∀ ζ ∈ Par, ∀ w ∈ stepDomain r (s - 5 * σ) (η * r),
        ‖H.Psi ξ w‖ ≤ A₀ ∧ ‖H.Psi ξ w - H.Psi ζ w‖ ≤ A₁ * ‖ξ - ζ‖ ∧
        ‖fderiv ℂ (H.Psi ξ) w‖ ≤ B₀ ∧
        ‖fderiv ℂ (H.Psi ξ) w - fderiv ℂ (H.Psi ζ) w‖ ≤ B₁ * ‖ξ - ζ‖ := by
  have hM0 := H.M₀_pos.le
  have hM1 := H.M₁_nonneg
  have hσ := H.hσ
  have hlam := H.hlam0
  have hsum := H.M_sum
  refine ⟨M₀, 2 * M₁, 8 * M₀ / σ, 16 * M₁ / σ, hM0, by positivity, by positivity, by positivity,
    by nlinarith, ?_, fun ξ hξ ζ hζ w hw => ?_⟩
  · have e : 8 * M₀ / σ + lam * (16 * M₁ / σ) = (8 * M₀ + 16 * lam * M₁) / σ := by ring
    rw [e]
    exact div_le_div_of_nonneg_right (by nlinarith) hσ.le
  · obtain ⟨d1, d2, d3, d4⟩ := H.flow_pair_smooth hξ hζ hw
    exact ⟨d1, d2.trans_eq (by ring), d3, d4.trans_eq (by ring)⟩

/-- **The sharp sup bound** `|Φ - id|_{p_+,r,D_+} = |Ψ|_{p_+,r} ≤ M_F` (step `f-flow`,
`w5-kamstep.tex:400-402`; ruling D3: a separate export, the `λ`-clause keeps `2M_F`). -/
theorem psi_le_MF {ξ : Fin 2 → ℝ} (hξ : ξ ∈ Par) {w : StepPhase r}
    (hw : w ∈ stepDomain r (s - 5 * σ) (η * r)) : ‖H.Psi ξ w‖ ≤ stepMF cF tF α σ ε := by
  have h := (H.flow_pair_smooth hξ hξ hw).1
  have := mul_nonneg H.hlam0 H.M₁_nonneg
  linarith [H.M_sum]

end StepCore

end KAM.Wave

end
