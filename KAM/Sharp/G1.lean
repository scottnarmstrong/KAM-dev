/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Sharp.Scheme
public import KAM.Sharp.CohData
public import KAM.Apost.G1
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The sharp G1 (blueprint `bp:p2s:g1`)

`KAM.Sharp.g1_gen` is the frozen statement of `KAM.aposteriori_kam` (`G1Body`, copied verbatim from
`KAM.Apost.g1_explicit`) with the sharp constants `C₁♯`, `C₂♯` for general small-divisor data
`(κ, c_R)`. The instances `g1_sharp` (Rüssmann), `g1_sharp_parseval`, `g1_sharp_crude` have the
binders of `KAM.Apost.g1_explicit`. `g1_sharp_uniform` is the ρ-uniform smallness.

The proof is `g1_core`: the fixed-frequency scheme (`KAM.Sharp.fixedScheme`) is run by the engine
(`Engine.Scheme.iterate`, `Engine.Scheme.limit`); the ball, derivative and invariance clauses of the
limit are the cap, `KAM.Apost.lim_margins` and `KAM.Apost.lim_invariance`.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator
open Matrix Filter Topology

namespace KAM.Sharp

open KAM KAM.Torus KAM.Apost

/-- The body of the frozen G1 (`KAM.aposteriori_kam`, verbatim from `KAM.Apost.g1_explicit`) for
given constants `C₁`, `C₂`: every hypothesis H1–H5 and the smallness `C₁ e/(γ⁴ ρ^{4τ}) < 1` imply
the seven conclusions with `C₂`. -/
def G1Body (n : ℕ) (τ ρ ρinf M σK σB σT μ γbar C₁ C₂ : ℝ) : Prop :=
  ∀ (𝔅 : Set ((Fin n → ℂ) × (Fin n → ℂ))) (h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ)
    (K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)) (ω : Fin n → ℝ) (γ e : ℝ),
    IsOpen 𝔅 →
    (∀ z ∈ 𝔅, ∀ k : Fin n → ℤ, (z.1 + (fun i => (k i : ℂ)), z.2) ∈ 𝔅) →
    DifferentiableOn ℂ h 𝔅 →
    (∀ z ∈ 𝔅, ∀ k : Fin n → ℤ, h (z.1 + (fun i => (k i : ℂ)), z.2) = h z) →
    (∀ θ I : Fin n → ℝ, ((fun i => (θ i : ℂ)), (fun i => (I i : ℂ))) ∈ 𝔅 →
      (h ((fun i => (θ i : ℂ)), (fun i => (I i : ℂ)))).im = 0) →
    (∀ z ∈ 𝔅, ‖fderiv ℂ h z‖ ≤ M ∧ ‖hamiltonianVectorFieldℂ h z‖ ≤ M ∧
      ‖fderiv ℂ (hamiltonianVectorFieldℂ h) z‖ ≤ M ∧
      ‖iteratedFDeriv ℂ 2 (hamiltonianVectorFieldℂ h) z‖ ≤ M) →
    DifferentiableOn ℂ K (complexStrip n ρ) → IsPrimaryOnStrip K ρ → IsRealOnReals K →
    (∀ θ ∈ complexStrip n ρ, Metric.ball (K θ) μ ⊆ 𝔅) →
    (∀ θ ∈ complexStrip n ρ, ‖fderiv ℂ K θ‖ ≤ σK - μ) →
    (∀ θ ∈ complexStrip n ρ, IsUnit (gramMatrix K θ).det ∧
      ∀ i, ∑ j, ‖(gramMatrix K θ)⁻¹ i j‖ ≤ σB - μ) →
    IsUnit (torsionAverage h K ω).det →
    (∀ i, ∑ j, ‖(torsionAverage h K ω)⁻¹ i j‖ ≤ σT - μ) →
    0 < γ → γ ≤ γbar → IsDiophantine γ τ ω →
    (∀ θ ∈ complexStrip n ρ, ‖invarianceError h K ω θ‖ ≤ e) →
    C₁ * e / (γ ^ 4 * ρ ^ (4 * τ)) < 1 →
    ∃ Kinf : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ),
      DifferentiableOn ℂ Kinf (complexStrip n ρinf) ∧ IsPrimaryOnStrip Kinf ρinf ∧
      IsRealOnReals Kinf ∧
      (∀ θ ∈ complexStrip n ρinf, invarianceError h Kinf ω θ = 0) ∧
      (∀ θ ∈ complexStrip n ρinf, Metric.ball (Kinf θ) (μ / 2) ⊆ 𝔅) ∧
      (∀ θ ∈ complexStrip n ρinf, ‖fderiv ℂ Kinf θ‖ ≤ σK - μ / 2) ∧
      ∀ θ ∈ complexStrip n ρinf, ‖Kinf θ - K θ‖ ≤ C₂ * e / (γ ^ 2 * ρ ^ (2 * τ))

variable {n : ℕ} {τ κ cR : ℝ}

/-- The core of `g1_gen`: the conclusion of G1 with the closeness `2 C_ΔK e/(γ² δ₀^a)`, from
`e ≤ 1` and `𝔠_* e/(γ⁴ δ₀^{2a}) ≤ 1`. -/
theorem g1_core (hn : 2 ≤ n) (hτ : (n : ℝ) - 1 ≤ τ) (hC : CohData n τ κ cR) {ρ ρinf : ℝ}
    (hρinf : 0 < ρinf) (hρinfρ : ρinf < ρ) {M σK σB σT μ : ℝ} (hM : 0 < M) (hσK : 0 < σK)
    (hσB : 0 < σB) (hσT : 0 < σT) (hμ : 0 < μ) {γbar : ℝ}
    (𝔅 : Set ((Fin n → ℂ) × (Fin n → ℂ))) (h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ)
    (K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)) (ω : Fin n → ℝ) (γ e : ℝ)
    (hopen : IsOpen 𝔅) (htransl : ∀ z ∈ 𝔅, ∀ k : Fin n → ℤ, (z.1 + (fun i => (k i : ℂ)), z.2) ∈ 𝔅)
    (hholo : DifferentiableOn ℂ h 𝔅)
    (hper : ∀ z ∈ 𝔅, ∀ k : Fin n → ℤ, h (z.1 + (fun i => (k i : ℂ)), z.2) = h z)
    (hreal : ∀ θ I : Fin n → ℝ, ((fun i => (θ i : ℂ)), (fun i => (I i : ℂ))) ∈ 𝔅 →
      (h ((fun i => (θ i : ℂ)), (fun i => (I i : ℂ)))).im = 0)
    (hbd : ∀ z ∈ 𝔅, ‖fderiv ℂ h z‖ ≤ M ∧ ‖hamiltonianVectorFieldℂ h z‖ ≤ M ∧
      ‖fderiv ℂ (hamiltonianVectorFieldℂ h) z‖ ≤ M ∧
      ‖iteratedFDeriv ℂ 2 (hamiltonianVectorFieldℂ h) z‖ ≤ M)
    (hK : DifferentiableOn ℂ K (complexStrip n ρ)) (hKp : IsPrimaryOnStrip K ρ)
    (hKr : IsRealOnReals K) (hball : ∀ θ ∈ complexStrip n ρ, Metric.ball (K θ) μ ⊆ 𝔅)
    (hDK : ∀ θ ∈ complexStrip n ρ, ‖fderiv ℂ K θ‖ ≤ σK - μ)
    (hG : ∀ θ ∈ complexStrip n ρ, IsUnit (gramMatrix K θ).det ∧
      ∀ i, ∑ j, ‖(gramMatrix K θ)⁻¹ i j‖ ≤ σB - μ)
    (hTu : IsUnit (torsionAverage h K ω).det)
    (hTb : ∀ i, ∑ j, ‖(torsionAverage h K ω)⁻¹ i j‖ ≤ σT - μ)
    (hγ : 0 < γ) (hγγbar : γ ≤ γbar) (hdio : IsDiophantine γ τ ω)
    (hE : ∀ θ ∈ complexStrip n ρ, ‖invarianceError h K ω θ‖ ≤ e) (he1 : e ≤ 1)
    (hsm : cStar n κ cR M σK σB σT γbar μ * e / (γ ^ 4 * delta0s ρ ρinf ^ (2 * (2 * κ))) ≤ 1) :
    ∃ Kinf : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ),
      DifferentiableOn ℂ Kinf (complexStrip n ρinf) ∧ IsPrimaryOnStrip Kinf ρinf ∧
      IsRealOnReals Kinf ∧
      (∀ θ ∈ complexStrip n ρinf, invarianceError h Kinf ω θ = 0) ∧
      (∀ θ ∈ complexStrip n ρinf, Metric.ball (Kinf θ) (μ / 2) ⊆ 𝔅) ∧
      (∀ θ ∈ complexStrip n ρinf, ‖fderiv ℂ Kinf θ‖ ≤ σK - μ / 2) ∧
      ∀ θ ∈ complexStrip n ρinf, ‖Kinf θ - K θ‖ ≤
        2 * cDK n cR M σK σB σT γbar * e / (γ ^ 2 * delta0s ρ ρinf ^ (2 * κ)) := by
  have hP : Params n τ M σK σB σT := ⟨hn, hτ, hM, hσK, hσB, hσT⟩
  have hρ0 : 0 < ρ := hρinf.trans hρinfρ
  have hS : Standing n τ M σK σB σT 𝔅 h ω γ :=
    { toParams := hP
      isOpen := hopen
      transl_mem := htransl
      holo := hholo
      periodic := hper
      real := hreal
      bounds := fun z hz => ⟨(hbd z hz).2.1, (hbd z hz).2.2.1, (hbd z hz).2.2.2⟩
      gamma_pos := hγ
      dio := hdio }
  have h00 : (0 : Fin n → ℂ) ∈ complexStrip n ρ := fun i => by simpa using hρ0
  have he0 : 0 ≤ e := (norm_nonneg _).trans (hE 0 h00)
  let m₀ : Fin 3 → ℝ := ![σK - μ, σB - μ, σT - μ]
  have hadm : (fixedScheme n h 𝔅 ω).Adm ρ μ e m₀ K :=
    { r_pos := hρ0
      β_pos := hμ
      ε_nonneg := he0
      ε_le_one := he1
      holo := hK
      primary := hKp
      real := hKr
      ball_sub := hball
      deriv_le := hDK
      gram := fun θ hθ => ⟨(hG θ hθ).1, norm_le_of_rowSum_le hn (hG θ hθ).2⟩
      twist := ⟨hTu, norm_le_of_rowSum_le hn hTb⟩
      error_le := hE }
  have hN := fixedScheme_isNewton hC hS hγγbar hμ.le
  obtain ⟨hEh, hst, hbl, hcap⟩ := engine_hyps hC hP hρinf hρinfρ hγ hγγbar hμ he0 hsm
  have hit := Engine.Scheme.iterate hN hρinf hρinfρ hγ hadm hEh hst hbl hcap
  obtain ⟨hconv, hconvd, hholo', hprim, hreal', hclose, -, -, hεz⟩ :=
    Engine.Scheme.limit hN hρinf hρinfρ hγ hadm hEh hst hbl hcap
  have hsch := Engine.schedule (lam := (fixedConsts n κ cR M σK σB σT γbar μ).lam)
    hN.lam_pos hρinf hρinfρ
  have hsub : ∀ s, complexStrip n ρinf ⊆
      complexStrip n (Engine.rSeq (fixedConsts n κ cR M σK σB σT γbar μ).lam ρ ρinf s) :=
    fun s => Triangular.strip_mono (hsch.2.2.2.2.1 s).le
  have hmarg : ∀ θ ∈ complexStrip n ρinf, Metric.ball
      ((fixedScheme n h 𝔅 ω).limTor (fixedConsts n κ cR M σK σB σT γbar μ).lam ρ ρinf K θ)
      (μ / 2) ⊆ 𝔅 := fun θ hθ =>
    lim_margins ((hclose θ hθ).trans hbl) (hball θ
      (Triangular.strip_mono hρinfρ.le hθ))
  have hAdm : ∀ s, Admissible
      ((Engine.Consts.mSeq (fixedConsts n κ cR M σK σB σT γbar μ) m₀ ρ ρinf γ e s) 0)
      ((Engine.Consts.mSeq (fixedConsts n κ cR M σK σB σT γbar μ) m₀ ρ ρinf γ e s) 1)
      ((Engine.Consts.mSeq (fixedConsts n κ cR M σK σB σT γbar μ) m₀ ρ ρinf γ e s) 2) 𝔅 h ω
      (Engine.rSeq (fixedConsts n κ cR M σK σB σT γbar μ).lam ρ ρinf s) _ _
      ((fixedScheme n h 𝔅 ω).iter (fixedConsts n κ cR M σK σB σT γbar μ).lam ρ ρinf K s) :=
    fun s => (hit s).1
  refine ⟨_, hholo', hprim, hreal', fun θ hθ => ?_, hmarg, fun θ hθ => ?_, hclose⟩
  · refine lim_invariance hS
      (Ks := fun s => (fixedScheme n h 𝔅 ω).tor
        ((fixedScheme n h 𝔅 ω).iter (fixedConsts n κ cR M σK σB σT γbar μ).lam ρ ρinf K s))
      (ε := fun s => (fixedConsts n κ cR M σK σB σT γbar μ).eps ρ ρinf γ e s)
      (hmarg θ hθ (Metric.mem_ball_self (half_pos hμ))) (hconv.tendsto_at hθ)
      (hconvd.tendsto_at hθ) (fun s => (hAdm s).error_le θ (hsub s hθ)) hεz
  · refine le_of_tendsto (hconvd.tendsto_at hθ).norm (Eventually.of_forall fun s => ?_)
    have h1 := (hAdm s).deriv_le θ (hsub s hθ)
    have h2 := (hit s).2.2.1 0
    have h3 : (fixedConsts n κ cR M σK σB σT γbar μ).cap 0 = σK - μ / 2 := rfl
    exact h1.trans (h2.trans h3.le)

/-- Blueprint `bp:p2s:g1` for general small-divisor data `(κ, c_R)`. A conditional helper: the
source results are the instances `g1_sharp`, `g1_sharp_parseval`, `g1_sharp_crude`, which have no
hypothesis on `(κ, c_R)`. -/
theorem g1_gen {n : ℕ} (hn : 2 ≤ n) {τ : ℝ} (hτ : (n : ℝ) - 1 ≤ τ) {κ cR : ℝ}
    (hC : CohData n τ κ cR) {ρ ρinf : ℝ} (hρinf : 0 < ρinf) (hρinfρ : ρinf < ρ)
    {M σK σB σT μ : ℝ} (hM : 0 < M) (hσK : 0 < σK) (hσB : 0 < σB) (hσT : 0 < σT) (hμ : 0 < μ)
    {γbar : ℝ} (hγbar : 0 < γbar) :
    0 < sharpC1 n κ cR M σK σB σT γbar μ τ ρ ρinf ∧ 0 < sharpC2 n κ cR M σK σB σT γbar τ ρ ρinf ∧
      G1Body n τ ρ ρinf M σK σB σT μ γbar (sharpC1 n κ cR M σK σB σT γbar μ τ ρ ρinf)
        (sharpC2 n κ cR M σK σB σT γbar τ ρ ρinf) := by
  have hP : Params n τ M σK σB σT := ⟨hn, hτ, hM, hσK, hσB, hσT⟩
  have hρ0 : 0 < ρ := hρinf.trans hρinfρ
  have hγb0 := hγbar
  obtain ⟨hDK, -, -, -, -⟩ := fixed_consts_pos hC hP hγb0
  have hD0 : 0 < delta0s ρ ρinf := Engine.delta0_pos (by norm_num : (0 : ℝ) < 3) hρinfρ
  refine ⟨mul_pos (Real.rpow_pos_of_pos hρ0 _) (lt_max_of_lt_left (pow_pos hγbar 4)),
    mul_pos (mul_pos (mul_pos two_pos hDK) (Real.rpow_pos_of_pos hρ0 _))
      (Real.rpow_pos_of_pos hD0 _), ?_⟩
  intro 𝔅 h K ω γ e hopen htransl hholo hper hreal hbd hK hKp hKr hball hDK' hG hTu hTb hγ hγγbar
    hdio hE hC1
  have h00 : (0 : Fin n → ℂ) ∈ complexStrip n ρ := fun i => by simpa using hρ0
  have hcs := (consts_pos (n := n) (κ := κ) (by omega) hC.cR_pos hM hσK hσB hσT hγb0 hμ).2.2.2.2.2.2
  obtain ⟨he1, hsm⟩ := g1_error_small_aux (τ' := τ) (a := 2 * κ) hρ0 hγ hγγbar hD0 hcs.le hC1
  obtain ⟨Kinf, h1, h2, h3, h4, h5, h6, h7⟩ := g1_core hn hτ hC hρinf hρinfρ hM hσK hσB hσT hμ
    𝔅 h K ω γ e hopen htransl hholo hper hreal hbd hK hKp hKr hball hDK' hG hTu hTb hγ hγγbar
    hdio hE he1.le hsm.le
  refine ⟨Kinf, h1, h2, h3, h4, h5, h6, fun θ hθ => ?_⟩
  have := h7 θ hθ
  rw [g1_closeness_eq (τ' := τ) hρ0 hγ hD0] at this
  exact this



/-- Blueprint `bp:p2s:g1-instances`(a), the headline: Rüssmann's data `(τ, cohConstR n τ)`,
`a = 2τ`. Hypotheses: those of `KAM.Apost.g1_explicit`, verbatim. -/
theorem g1_sharp {n : ℕ} (hn : 2 ≤ n) {τ : ℝ} (hτ : (n : ℝ) - 1 ≤ τ)
    {ρ ρinf : ℝ} (hρinf : 0 < ρinf) (hρinfρ : ρinf < ρ)
    {M σK σB σT μ : ℝ} (hM : 0 < M) (hσK : 0 < σK) (hσB : 0 < σB) (hσT : 0 < σT) (hμ : 0 < μ)
    {γbar : ℝ} (hγbar : 0 < γbar) :
    0 < sharpC1 n τ (cohConstR n τ) M σK σB σT γbar μ τ ρ ρinf ∧
      0 < sharpC2 n τ (cohConstR n τ) M σK σB σT γbar τ ρ ρinf ∧
      G1Body n τ ρ ρinf M σK σB σT μ γbar (sharpC1 n τ (cohConstR n τ) M σK σB σT γbar μ τ ρ ρinf)
        (sharpC2 n τ (cohConstR n τ) M σK σB σT γbar τ ρ ρinf) := by
  have hn1 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  exact g1_gen hn hτ (cohData_russmann (n := n) (by linarith)) hρinf hρinfρ hM hσK hσB hσT hμ hγbar

/-- Blueprint `bp:p2s:g1-instances`(b): Parseval's data `(τ + n/2, cohConstP n τ)`. -/
theorem g1_sharp_parseval {n : ℕ} (hn : 2 ≤ n) {τ : ℝ} (hτ : (n : ℝ) - 1 ≤ τ)
    {ρ ρinf : ℝ} (hρinf : 0 < ρinf) (hρinfρ : ρinf < ρ)
    {M σK σB σT μ : ℝ} (hM : 0 < M) (hσK : 0 < σK) (hσB : 0 < σB) (hσT : 0 < σT) (hμ : 0 < μ)
    {γbar : ℝ} (hγbar : 0 < γbar) :
    0 < sharpC1 n (τ + (n : ℝ) / 2) (cohConstP n τ) M σK σB σT γbar μ τ ρ ρinf ∧
      0 < sharpC2 n (τ + (n : ℝ) / 2) (cohConstP n τ) M σK σB σT γbar τ ρ ρinf ∧
      G1Body n τ ρ ρinf M σK σB σT μ γbar
        (sharpC1 n (τ + (n : ℝ) / 2) (cohConstP n τ) M σK σB σT γbar μ τ ρ ρinf)
        (sharpC2 n (τ + (n : ℝ) / 2) (cohConstP n τ) M σK σB σT γbar τ ρ ρinf) := by
  have hn1 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  exact g1_gen hn hτ (cohData_parseval (by omega) (by linarith) (by linarith)) hρinf hρinfρ hM
    hσK hσB
    hσT hμ hγbar

/-- Blueprint `bp:p2s:g1-instances`(c): the crude data `(τ + n, cohConst n τ)`. -/
theorem g1_sharp_crude {n : ℕ} (hn : 2 ≤ n) {τ : ℝ} (hτ : (n : ℝ) - 1 ≤ τ)
    {ρ ρinf : ℝ} (hρinf : 0 < ρinf) (hρinfρ : ρinf < ρ)
    {M σK σB σT μ : ℝ} (hM : 0 < M) (hσK : 0 < σK) (hσB : 0 < σB) (hσT : 0 < σT) (hμ : 0 < μ)
    {γbar : ℝ} (hγbar : 0 < γbar) :
    0 < sharpC1 n (τ + n) (cohConst n τ) M σK σB σT γbar μ τ ρ ρinf ∧
      0 < sharpC2 n (τ + n) (cohConst n τ) M σK σB σT γbar τ ρ ρinf ∧
      G1Body n τ ρ ρinf M σK σB σT μ γbar
        (sharpC1 n (τ + n) (cohConst n τ) M σK σB σT γbar μ τ ρ ρinf)
        (sharpC2 n (τ + n) (cohConst n τ) M σK σB σT γbar τ ρ ρinf) := by
  have hn1 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  exact g1_gen hn hτ (cohData_crude (by omega) (by linarith)) hρinf hρinfρ hM hσK hσB hσT hμ hγbar


/-- Remark `bp:p2s:uniform`: the threshold `C e/(γ⁴ δ₀^{2a}) < 1` with `C = max {γ̄⁴, 𝔠_*}`
independent of `ρ` (Rüssmann's data); a corollary of `g1_sharp`. -/
theorem g1_sharp_uniform {n : ℕ} (hn : 2 ≤ n) {τ : ℝ} (hτ : (n : ℝ) - 1 ≤ τ)
    {ρ ρinf : ℝ} (hρinf : 0 < ρinf) (hρinfρ : ρinf < ρ)
    {M σK σB σT μ : ℝ} (hM : 0 < M) (hσK : 0 < σK) (hσB : 0 < σB) (hσT : 0 < σT) (hμ : 0 < μ)
    {γbar : ℝ} (hγbar : 0 < γbar)
    (𝔅 : Set ((Fin n → ℂ) × (Fin n → ℂ))) (h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ)
    (K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)) (ω : Fin n → ℝ) (γ e : ℝ)
    (hopen : IsOpen 𝔅) (htransl : ∀ z ∈ 𝔅, ∀ k : Fin n → ℤ, (z.1 + (fun i => (k i : ℂ)), z.2) ∈ 𝔅)
    (hholo : DifferentiableOn ℂ h 𝔅)
    (hper : ∀ z ∈ 𝔅, ∀ k : Fin n → ℤ, h (z.1 + (fun i => (k i : ℂ)), z.2) = h z)
    (hreal : ∀ θ I : Fin n → ℝ, ((fun i => (θ i : ℂ)), (fun i => (I i : ℂ))) ∈ 𝔅 →
      (h ((fun i => (θ i : ℂ)), (fun i => (I i : ℂ)))).im = 0)
    (hbd : ∀ z ∈ 𝔅, ‖fderiv ℂ h z‖ ≤ M ∧ ‖hamiltonianVectorFieldℂ h z‖ ≤ M ∧
      ‖fderiv ℂ (hamiltonianVectorFieldℂ h) z‖ ≤ M ∧
      ‖iteratedFDeriv ℂ 2 (hamiltonianVectorFieldℂ h) z‖ ≤ M)
    (hK : DifferentiableOn ℂ K (complexStrip n ρ)) (hKp : IsPrimaryOnStrip K ρ)
    (hKr : IsRealOnReals K) (hball : ∀ θ ∈ complexStrip n ρ, Metric.ball (K θ) μ ⊆ 𝔅)
    (hDK : ∀ θ ∈ complexStrip n ρ, ‖fderiv ℂ K θ‖ ≤ σK - μ)
    (hG : ∀ θ ∈ complexStrip n ρ, IsUnit (gramMatrix K θ).det ∧
      ∀ i, ∑ j, ‖(gramMatrix K θ)⁻¹ i j‖ ≤ σB - μ)
    (hTu : IsUnit (torsionAverage h K ω).det)
    (hTb : ∀ i, ∑ j, ‖(torsionAverage h K ω)⁻¹ i j‖ ≤ σT - μ)
    (hγ : 0 < γ) (hγγbar : γ ≤ γbar) (hdio : IsDiophantine γ τ ω)
    (hE : ∀ θ ∈ complexStrip n ρ, ‖invarianceError h K ω θ‖ ≤ e)
    (hsmall : max (γbar ^ 4) (cStar n τ (cohConstR n τ) M σK σB σT γbar μ) * e /
      (γ ^ 4 * delta0s ρ ρinf ^ (2 * (2 * τ))) < 1) :
    ∃ Kinf : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ),
      DifferentiableOn ℂ Kinf (complexStrip n ρinf) ∧ IsPrimaryOnStrip Kinf ρinf ∧
      IsRealOnReals Kinf ∧
      (∀ θ ∈ complexStrip n ρinf, invarianceError h Kinf ω θ = 0) ∧
      (∀ θ ∈ complexStrip n ρinf, Metric.ball (Kinf θ) (μ / 2) ⊆ 𝔅) ∧
      (∀ θ ∈ complexStrip n ρinf, ‖fderiv ℂ Kinf θ‖ ≤ σK - μ / 2) ∧
      ∀ θ ∈ complexStrip n ρinf, ‖Kinf θ - K θ‖ ≤
        2 * cDK n (cohConstR n τ) M σK σB σT γbar * e / (γ ^ 2 * delta0s ρ ρinf ^ (2 * τ)) := by
  have hρ0 : 0 < ρ := hρinf.trans hρinfρ
  have hD0 : 0 < delta0s ρ ρinf := Engine.delta0_pos (by norm_num : (0 : ℝ) < 3) hρinfρ
  have hD1 : delta0s ρ ρinf ≤ 1 := Engine.delta0_le_one _ _ _
  have h00 : (0 : Fin n → ℂ) ∈ complexStrip n ρ := fun i => by simpa using hρ0
  have he0 : 0 ≤ e := (norm_nonneg _).trans (hE 0 h00)
  have hC : CohData n τ τ (cohConstR n τ) := cohData_russmann (n := n)
    (by have : (2:ℝ) ≤ n := by exact_mod_cast hn
        linarith)
  have hD : 0 < γ ^ 4 * delta0s ρ ρinf ^ (2 * (2 * τ)) := by positivity
  have hq : max (γbar ^ 4) (cStar n τ (cohConstR n τ) M σK σB σT γbar μ) * e /
      (γ ^ 4 * delta0s ρ ρinf ^ (2 * (2 * τ))) < 1 := hsmall
  have hsm : cStar n τ (cohConstR n τ) M σK σB σT γbar μ * e /
      (γ ^ 4 * delta0s ρ ρinf ^ (2 * (2 * τ))) ≤ 1 :=
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) he0) hD.le).trans
      hq.le
  have he1 : e ≤ 1 := by
    have h1 : γ ^ 4 * delta0s ρ ρinf ^ (2 * (2 * τ)) ≤ γbar ^ 4 := by
      have hp : delta0s ρ ρinf ^ (2 * (2 * τ)) ≤ 1 :=
        Real.rpow_le_one hD0.le hD1 (by linarith [hC.tau_nonneg])
      calc _ ≤ γ ^ 4 * 1 := mul_le_mul_of_nonneg_left hp (pow_nonneg hγ.le 4)
        _ ≤ γbar ^ 4 := by rw [mul_one]; exact pow_le_pow_left₀ hγ.le hγγbar 4
    have h2 : e ≤ γbar ^ 4 * e / (γ ^ 4 * delta0s ρ ρinf ^ (2 * (2 * τ))) := by
      rw [le_div_iff₀ hD]; nlinarith
    have h3 : γbar ^ 4 * e / (γ ^ 4 * delta0s ρ ρinf ^ (2 * (2 * τ))) ≤
        max (γbar ^ 4) (cStar n τ (cohConstR n τ) M σK σB σT γbar μ) * e /
          (γ ^ 4 * delta0s ρ ρinf ^ (2 * (2 * τ))) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) he0) hD.le
    linarith
  exact g1_core hn hτ hC hρinf hρinfρ hM hσK hσB hσT hμ 𝔅 h K ω γ e hopen htransl hholo hper
    hreal hbd hK hKp hKr hball hDK hG hTu hTb hγ hγγbar hdio hE he1 hsm


end KAM.Sharp

end
