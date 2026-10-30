/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Sharp2.RouteA.Scheme
public import KAM.Sharp.G1
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# The v2 a-posteriori theorem, route A (blueprint `bp:p2s2:g1`, `bp:p2s2:frozen-form`)

* `InitA`, `RefHypA`: the refined data `(R1)–(R3)`: bounds on explicit objects of `h`, `K`, `ω`,
  with
  their initial values (the caps of `NumA` may be larger: free budgets, L8);
* `g1_core_A`: Theorem `bp:p2s2:g1`, route A: from `routeAOk` at `X⋆` and
  `e/(γ⁴ δ₀^{2a}) ≤ X⋆`, the conclusion of the frozen G1 with the budgets `μ/2`, and closeness
  proportional to `e`;
* `G1BodyA`: the frozen body with the refined data and the certificates;
* `c1A`, `c2A`: the route-A constants. `c1A = ρ^{4τ}/(X⋆ δ₀^{4τ})`; `c2A = ρ^{2τ} S/(X⋆ δ₀^{4τ})`,
  where `S` is the ball sum at `X⋆` with `γ̄` replaced by `1`: the sums are superlinear in `X₀` and
  carry `γ²`, so `|K∞ - K| ≤ (X₀/X⋆) γ² S`, and there is no factor `γ̄²` (audit finding F6);
* `g1_v2A`: Corollary `bp:p2s2:frozen-form`, route A, with `C₁ = min {C₁♯, c1A}`,
  `C₂ = max {C₂♯, c2A}`,
  by cases on the branch of the minimum.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator
open Matrix Filter Topology KAM.Sharp.Engine

namespace KAM.Sharp2.RouteA

open KAM KAM.Torus KAM.Apost KAM.Sharp

/-- The initial values of the refined data. -/
structure InitA where
  iLt : ℝ
  iN : ℝ
  iNt : ℝ
  iH : ℝ

/-- The refined hypotheses `(R1)–(R3)`, with the initial values `I`. Each bounds an explicit object
of
`h`, `K`, `ω`; `T` is bounded on `T_{ρ-δ₀}`. -/
structure RefHypA (N : NumA) (I : InitA) (𝔅 : Set ((Fin N.n → ℂ) × (Fin N.n → ℂ)))
    (h : (Fin N.n → ℂ) × (Fin N.n → ℂ) → ℂ) (K : (Fin N.n → ℂ) → (Fin N.n → ℂ) × (Fin N.n → ℂ))
    (ω : Fin N.n → ℝ) : Prop where
  dX : ∀ z ∈ 𝔅, ‖fderiv ℂ (hamiltonianVectorFieldℂ h) z‖ ≤ N.M1
  d2X : ∀ z ∈ 𝔅, ‖iteratedFDeriv ℂ 2 (hamiltonianVectorFieldℂ h) z‖ ≤ N.M2
  tangentT : ∀ θ ∈ complexStrip N.n N.ρ, ‖(tangentMat K θ)ᵀ‖ ≤ I.iLt
  normal : ∀ θ ∈ complexStrip N.n N.ρ, ‖normalMat K θ‖ ≤ I.iN
  normalT : ∀ θ ∈ complexStrip N.n N.ρ, ‖(normalMat K θ)ᵀ‖ ≤ I.iNt
  tors : ∀ θ ∈ complexStrip N.n (N.ρ - N.δ 0), ‖torsion h K ω θ‖ ≤ I.iH

/-- The initial cap values: nothing of the ball budget used, the frozen margins `σ - μ`. -/
def initV (I : InitA) (σK σB σT μ : ℝ) : Fin 8 → ℝ :=
  ![0, σK - μ, σB - μ, σT - μ, I.iLt, I.iN, I.iNt, I.iH]

/-- `C₁` of route A. -/
def c1A (N : NumA) (Xs : ℝ) : ℝ := N.ρ ^ (4 * N.τ) / (Xs * delta0 3 N.ρ N.ρinf ^ (4 * N.τ))

/-- `C₂` of route A. -/
def c2A (N : NumA) (Xs : ℝ) : ℝ :=
  N.ρ ^ (2 * N.τ) * sumA (2 * N.τ) 3 N.ρ N.ρinf 1 (N.xS Xs) (fun s => (N.stage s).CD) (2 * N.τ) N.kp
      /
    (Xs * delta0 3 N.ρ N.ρinf ^ (4 * N.τ))

variable {N : NumA}

/-- Blueprint `bp:p2s2:g1`, route A. -/
theorem g1_core_A (hN : N.Wf) (hfix : N.iso = false) (hΘ : N.Θ = 0) {τ M μ γ e Xs : ℝ}
    {𝔅 : Set ((Fin N.n → ℂ) × (Fin N.n → ℂ))} {h : (Fin N.n → ℂ) × (Fin N.n → ℂ) → ℂ}
    {ω : Fin N.n → ℝ} {Ω : Set (Fin N.n → ℝ)} {m₀ : Fin 8 → ℝ}
    {K : (Fin N.n → ℂ) → (Fin N.n → ℂ) × (Fin N.n → ℂ)}
    (hS : Standing N.n τ M N.sK N.sB N.sT 𝔅 h ω γ)
    (hd1 : ∀ z ∈ 𝔅, ‖fderiv ℂ (hamiltonianVectorFieldℂ h) z‖ ≤ N.M1)
    (hd2 : ∀ z ∈ 𝔅, ‖iteratedFDeriv ℂ 2 (hamiltonianVectorFieldℂ h) z‖ ≤ N.M2)
    (hγb : γ ≤ N.γb) (hω : ω ∈ Ω) (hC : N.Cert γ Ω) (hμ : 0 < μ) (hm0 : m₀ 0 = 0)
    (hOk : routeAOk N (N.capV (μ / 2)) m₀ Xs)
    (h0 : AdmA 𝔅 h ω (N.r 0) (N.r 0 - N.δ 0) μ e (m₀ 1) (m₀ 2) (m₀ 3) (m₀ 4) (m₀ 5) (m₀ 6) (m₀ 7) K)
    (hX : e / (γ ^ 4 * delta0 3 N.ρ N.ρinf ^ (2 * (2 * N.τ))) ≤ Xs) (hXpos : 0 < Xs) :
    ∃ Kinf : (Fin N.n → ℂ) → (Fin N.n → ℂ) × (Fin N.n → ℂ),
      DifferentiableOn ℂ Kinf (complexStrip N.n N.ρinf) ∧ IsPrimaryOnStrip Kinf N.ρinf ∧
      IsRealOnReals Kinf ∧
      (∀ θ ∈ complexStrip N.n N.ρinf, invarianceError h Kinf ω θ = 0) ∧
      (∀ θ ∈ complexStrip N.n N.ρinf, Metric.ball (Kinf θ) (μ / 2) ⊆ 𝔅) ∧
      (∀ θ ∈ complexStrip N.n N.ρinf, ‖fderiv ℂ Kinf θ‖ ≤ N.sK) ∧
      ∀ θ ∈ complexStrip N.n N.ρinf, ‖Kinf θ - K θ‖ ≤
        c2A N Xs * e / (γ ^ 2 * N.ρ ^ (2 * N.τ)) := by
  have hγ := hS.gamma_pos
  have hρ0 : 0 < N.ρ := hN.ρinf_pos.trans hN.ρinf_lt
  have hb : μ / 2 < μ := by linarith
  have hNw := schemeA_isNewton hN hfix hΘ hS hd1 hd2 hγb hω hC hb
  have R := hOk.runData hN
  have h0' : (schemeA N 𝔅 h ω μ).Adm 0 e m₀ K := by
    show AdmA 𝔅 h ω (N.r 0) (N.r 0 - N.δ 0) (μ - m₀ 0) e (m₀ 1) (m₀ 2) (m₀ 3) (m₀ 4) (m₀ 5) (m₀ 6)
      (m₀ 7) K
    rw [hm0, sub_zero]
    exact h0
  have hlam : (0 : ℝ) < 3 := by norm_num
  have hit := SchemeA.run hNw R hlam hN.ρinf_lt hγ hγb h0' hX
  obtain ⟨hconv, hconvd, hholo, hprim, hreal, hclose, hclose', -, -, -, hεz⟩ :=
    SchemeA.limit hNw R hlam hN.ρinf_pos hN.ρinf_lt hγ hγb h0' hX
  have hsub : ∀ s, complexStrip N.n N.ρinf ⊆ complexStrip N.n (N.r s) := fun s =>
    Triangular.strip_mono (hN.ρinf_lt_r s).le
  -- the ball budget
  have hball : ∀ θ ∈ complexStrip N.n N.ρinf,
      ‖(schemeA N 𝔅 h ω μ).limTor N.ρinf K θ - K θ‖ ≤ μ / 2 := fun θ hθ => by
    have h1 := hclose θ hθ
    have h2 := R.J3 0
    rw [hm0, zero_add] at h2
    have e1 : (2 * N.τ + ((jA 0 : ℕ) : ℝ)) = 2 * N.τ := by simp [jA]
    rw [e1] at h2
    exact h1.trans h2
  have hmarg : ∀ θ ∈ complexStrip N.n N.ρinf,
      Metric.ball ((schemeA N 𝔅 h ω μ).limTor N.ρinf K θ) (μ / 2) ⊆ 𝔅 := fun θ hθ => by
    have := PerturbationAux.ball_subset_of_close (h0.ball_sub θ (hsub 0 hθ)) (hball θ hθ)
    rwa [show μ - μ / 2 = μ / 2 by ring] at this
  refine ⟨_, hholo, hprim, hreal, fun θ hθ => ?_, hmarg, fun θ hθ => ?_, fun θ hθ => ?_⟩
  · exact lim_invariance hS (Ks := fun s => (schemeA N 𝔅 h ω μ).tor ((schemeA N 𝔅 h ω μ).iter K s))
      (ε := runEps (2 * N.τ) 3 N.ρ N.ρinf γ N.stage e)
      (hmarg θ hθ (Metric.mem_ball_self (half_pos hμ))) (hconv.tendsto_at hθ)
      (hconvd.tendsto_at hθ) (fun s => AdmA.error_le (hit s).1 θ (hsub s hθ)) hεz
  · refine le_of_tendsto (hconvd.tendsto_at hθ).norm (Eventually.of_forall fun s => ?_)
    have h1 := AdmA.deriv_le (hit s).1 θ (hsub s hθ)
    exact h1.trans ((hit s).2.1 1)
  · refine (hclose' θ hθ).trans (le_of_eq ?_)
    have hD : 0 < delta0 3 N.ρ N.ρinf := delta0_pos hlam hN.ρinf_lt
    have hDp : 0 < delta0 3 N.ρ N.ρinf ^ (4 * N.τ) := Real.rpow_pos_of_pos hD _
    have hρp : 0 < N.ρ ^ (2 * N.τ) := Real.rpow_pos_of_pos hρ0 _
    rw [show 2 * (2 * N.τ) = 4 * N.τ by ring]
    unfold c2A
    have : sumA (2 * N.τ) 3 N.ρ N.ρinf 1 (xA (2 * N.τ) (fun s => (N.stage s).CE) Xs)
        (fun s => (N.stage s).CD) (2 * N.τ) N.kp =
      sumA (2 * N.τ) 3 N.ρ N.ρinf 1 (N.xS Xs) (fun s => (N.stage s).CD) (2 * N.τ) N.kp := rfl
    rw [this]
    field_simp

/-- The frozen G1 body (`KAM.Sharp.G1Body`) with the refined data of route A and the certificates
bound to the frequency: the additional hypotheses are `RefHypA` and `N.Cert` on a set `Ω ∋ ω`. -/
def G1BodyA (N : NumA) (I : InitA) (M σK σB σT μ γbar C₁ C₂ : ℝ) : Prop :=
  ∀ (𝔅 : Set ((Fin N.n → ℂ) × (Fin N.n → ℂ))) (h : (Fin N.n → ℂ) × (Fin N.n → ℂ) → ℂ)
    (K : (Fin N.n → ℂ) → (Fin N.n → ℂ) × (Fin N.n → ℂ)) (ω : Fin N.n → ℝ) (γ e : ℝ)
    (Ω : Set (Fin N.n → ℝ)),
    IsOpen 𝔅 →
    (∀ z ∈ 𝔅, ∀ k : Fin N.n → ℤ, (z.1 + (fun i => (k i : ℂ)), z.2) ∈ 𝔅) →
    DifferentiableOn ℂ h 𝔅 →
    (∀ z ∈ 𝔅, ∀ k : Fin N.n → ℤ, h (z.1 + (fun i => (k i : ℂ)), z.2) = h z) →
    (∀ θ I : Fin N.n → ℝ, ((fun i => (θ i : ℂ)), (fun i => (I i : ℂ))) ∈ 𝔅 →
      (h ((fun i => (θ i : ℂ)), (fun i => (I i : ℂ)))).im = 0) →
    (∀ z ∈ 𝔅, ‖fderiv ℂ h z‖ ≤ M ∧ ‖hamiltonianVectorFieldℂ h z‖ ≤ M ∧
      ‖fderiv ℂ (hamiltonianVectorFieldℂ h) z‖ ≤ M ∧
      ‖iteratedFDeriv ℂ 2 (hamiltonianVectorFieldℂ h) z‖ ≤ M) →
    DifferentiableOn ℂ K (complexStrip N.n N.ρ) → IsPrimaryOnStrip K N.ρ → IsRealOnReals K →
    (∀ θ ∈ complexStrip N.n N.ρ, Metric.ball (K θ) μ ⊆ 𝔅) →
    (∀ θ ∈ complexStrip N.n N.ρ, ‖fderiv ℂ K θ‖ ≤ σK - μ) →
    (∀ θ ∈ complexStrip N.n N.ρ, IsUnit (gramMatrix K θ).det ∧
      ∀ i, ∑ j, ‖(gramMatrix K θ)⁻¹ i j‖ ≤ σB - μ) →
    IsUnit (torsionAverage h K ω).det →
    (∀ i, ∑ j, ‖(torsionAverage h K ω)⁻¹ i j‖ ≤ σT - μ) →
    RefHypA N I 𝔅 h K ω → ω ∈ Ω → N.Cert γ Ω →
    0 < γ → γ ≤ γbar → IsDiophantine γ N.τ ω →
    (∀ θ ∈ complexStrip N.n N.ρ, ‖invarianceError h K ω θ‖ ≤ e) →
    C₁ * e / (γ ^ 4 * N.ρ ^ (4 * N.τ)) < 1 →
    ∃ Kinf : (Fin N.n → ℂ) → (Fin N.n → ℂ) × (Fin N.n → ℂ),
      DifferentiableOn ℂ Kinf (complexStrip N.n N.ρinf) ∧ IsPrimaryOnStrip Kinf N.ρinf ∧
      IsRealOnReals Kinf ∧
      (∀ θ ∈ complexStrip N.n N.ρinf, invarianceError h Kinf ω θ = 0) ∧
      (∀ θ ∈ complexStrip N.n N.ρinf, Metric.ball (Kinf θ) (μ / 2) ⊆ 𝔅) ∧
      (∀ θ ∈ complexStrip N.n N.ρinf, ‖fderiv ℂ Kinf θ‖ ≤ σK - μ / 2) ∧
      ∀ θ ∈ complexStrip N.n N.ρinf, ‖Kinf θ - K θ‖ ≤ C₂ * e / (γ ^ 2 * N.ρ ^ (2 * N.τ))

/-- The route-A branch of the frozen form: every hypothesis of the frozen G1, the refined data, the
certificates, and `e/(γ⁴ δ₀^{2a}) < X⋆`. -/
theorem g1_branch_A (hN : N.Wf) (hfix : N.iso = false) (hΘ : N.Θ = 0) (hτ : (N.n : ℝ) - 1 ≤ N.τ)
    {M σK σB σT μ γbar Xs : ℝ} {I : InitA} (hM : 0 < M) (hμ : 0 < μ) (hγbar : γbar = N.γb)
    (hsK : N.sK = σK - μ / 2) (hOk : routeAOk N (N.capV (μ / 2)) (initV I σK σB σT μ) Xs)
    (hXpos : 0 < Xs) {𝔅 : Set ((Fin N.n → ℂ) × (Fin N.n → ℂ))}
    {h : (Fin N.n → ℂ) × (Fin N.n → ℂ) → ℂ}
    {K : (Fin N.n → ℂ) → (Fin N.n → ℂ) × (Fin N.n → ℂ)} {ω : Fin N.n → ℝ} {γ e : ℝ}
    {Ω : Set (Fin N.n → ℝ)} (hopen : IsOpen 𝔅)
    (htransl : ∀ z ∈ 𝔅, ∀ k : Fin N.n → ℤ, (z.1 + (fun i => (k i : ℂ)), z.2) ∈ 𝔅)
    (hholo : DifferentiableOn ℂ h 𝔅)
    (hper : ∀ z ∈ 𝔅, ∀ k : Fin N.n → ℤ, h (z.1 + (fun i => (k i : ℂ)), z.2) = h z)
    (hreal : ∀ θ I : Fin N.n → ℝ, ((fun i => (θ i : ℂ)), (fun i => (I i : ℂ))) ∈ 𝔅 →
      (h ((fun i => (θ i : ℂ)), (fun i => (I i : ℂ)))).im = 0)
    (hbd : ∀ z ∈ 𝔅, ‖fderiv ℂ h z‖ ≤ M ∧ ‖hamiltonianVectorFieldℂ h z‖ ≤ M ∧
      ‖fderiv ℂ (hamiltonianVectorFieldℂ h) z‖ ≤ M ∧
      ‖iteratedFDeriv ℂ 2 (hamiltonianVectorFieldℂ h) z‖ ≤ M)
    (hK : DifferentiableOn ℂ K (complexStrip N.n N.ρ)) (hKp : IsPrimaryOnStrip K N.ρ)
    (hKr : IsRealOnReals K) (hball : ∀ θ ∈ complexStrip N.n N.ρ, Metric.ball (K θ) μ ⊆ 𝔅)
    (hDK : ∀ θ ∈ complexStrip N.n N.ρ, ‖fderiv ℂ K θ‖ ≤ σK - μ)
    (hG : ∀ θ ∈ complexStrip N.n N.ρ, IsUnit (gramMatrix K θ).det ∧
      ∀ i, ∑ j, ‖(gramMatrix K θ)⁻¹ i j‖ ≤ σB - μ)
    (hTu : IsUnit (torsionAverage h K ω).det)
    (hTb : ∀ i, ∑ j, ‖(torsionAverage h K ω)⁻¹ i j‖ ≤ σT - μ)
    (hRef : RefHypA N I 𝔅 h K ω) (hω : ω ∈ Ω) (hCt : N.Cert γ Ω) (hγ : 0 < γ) (hγγbar : γ ≤ γbar)
    (hdio : IsDiophantine γ N.τ ω) (he0 : 0 ≤ e)
    (hE : ∀ θ ∈ complexStrip N.n N.ρ, ‖invarianceError h K ω θ‖ ≤ e)
    (hsm : e / (γ ^ 4 * delta0 3 N.ρ N.ρinf ^ (2 * (2 * N.τ))) < Xs) :
    ∃ Kinf : (Fin N.n → ℂ) → (Fin N.n → ℂ) × (Fin N.n → ℂ),
      DifferentiableOn ℂ Kinf (complexStrip N.n N.ρinf) ∧ IsPrimaryOnStrip Kinf N.ρinf ∧
      IsRealOnReals Kinf ∧
      (∀ θ ∈ complexStrip N.n N.ρinf, invarianceError h Kinf ω θ = 0) ∧
      (∀ θ ∈ complexStrip N.n N.ρinf, Metric.ball (Kinf θ) (μ / 2) ⊆ 𝔅) ∧
      (∀ θ ∈ complexStrip N.n N.ρinf, ‖fderiv ℂ Kinf θ‖ ≤ σK - μ / 2) ∧
      ∀ θ ∈ complexStrip N.n N.ρinf, ‖Kinf θ - K θ‖ ≤
        c2A N Xs * e / (γ ^ 2 * N.ρ ^ (2 * N.τ)) := by
  have hρ0 : 0 < N.ρ := hN.ρinf_pos.trans hN.ρinf_lt
  have hP : Params N.n N.τ M N.sK N.sB N.sT := ⟨hN.two_le, hτ, hM, hN.sK, hN.sB, hN.sT⟩
  have hS : Standing N.n N.τ M N.sK N.sB N.sT 𝔅 h ω γ :=
    { toParams := hP
      isOpen := hopen
      transl_mem := htransl
      holo := hholo
      periodic := hper
      real := hreal
      bounds := fun z hz => ⟨(hbd z hz).2.1, (hbd z hz).2.2.1, (hbd z hz).2.2.2⟩
      gamma_pos := hγ
      dio := hdio }
  have hr0 : N.r 0 = N.ρ := rSeq_zero
  have h0 : AdmA 𝔅 h ω (N.r 0) (N.r 0 - N.δ 0) μ e (σK - μ) (σB - μ) (σT - μ) I.iLt I.iN I.iNt
      I.iH K := by
    rw [hr0]
    exact
      { r_pos := hρ0
        β_pos := hμ
        ε_nonneg := he0
        holo := hK
        primary := hKp
        real := hKr
        ball_sub := hball
        deriv_le := hDK
        gram := fun θ hθ => ⟨(hG θ hθ).1, norm_le_of_rowSum_le hN.two_le (hG θ hθ).2⟩
        tangentT := hRef.tangentT
        normal := hRef.normal
        normalT := hRef.normalT
        tors := hRef.tors
        twist := ⟨hTu, norm_le_of_rowSum_le hN.two_le hTb⟩
        error_le := hE }
  obtain ⟨Kinf, h1, h2, h3, h4, h5, h6, h7⟩ := g1_core_A hN hfix hΘ hS hRef.dX hRef.d2X
    (hγγbar.trans_eq hγbar) hω hCt hμ rfl hOk h0 hsm.le hXpos
  exact ⟨Kinf, h1, h2, h3, h4, h5, fun θ hθ => (h6 θ hθ).trans_eq hsK, h7⟩

/-- Corollary `bp:p2s2:frozen-form`, route A: the frozen conclusion with
`C₁ = min {C₁♯, ρ^{4τ}/(X⋆ δ₀^{4τ})}` and `C₂ = max {C₂♯, c2A}`, whenever `routeAOk` holds at
`X⋆ > 0`. `C₁♯` is v1's `sharpC1` with Rüssmann's data, so the theorem is never worse than v1. -/
theorem g1_v2A (hN : N.Wf) (hfix : N.iso = false) (hΘ : N.Θ = 0) (hτ : (N.n : ℝ) - 1 ≤ N.τ)
    {M σK σB σT μ γbar Xs : ℝ} (I : InitA) (hM : 0 < M) (hσK : 0 < σK) (hσB : 0 < σB) (hσT : 0 < σT)
    (hμ : 0 < μ) (hγbar : γbar = N.γb) (hsK : N.sK = σK - μ / 2)
    (hOk : routeAOk N (N.capV (μ / 2)) (initV I σK σB σT μ) Xs) (hXpos : 0 < Xs) :
    0 < min (sharpC1 N.n N.τ (cohConstR N.n N.τ) M σK σB σT γbar μ N.τ N.ρ N.ρinf) (c1A N Xs) ∧
      0 < max (sharpC2 N.n N.τ (cohConstR N.n N.τ) M σK σB σT γbar N.τ N.ρ N.ρinf) (c2A N Xs) ∧
      G1BodyA N I M σK σB σT μ γbar
        (min (sharpC1 N.n N.τ (cohConstR N.n N.τ) M σK σB σT γbar μ N.τ N.ρ N.ρinf) (c1A N Xs))
        (max (sharpC2 N.n N.τ (cohConstR N.n N.τ) M σK σB σT γbar N.τ N.ρ N.ρinf) (c2A N Xs)) := by
  have hρ0 : 0 < N.ρ := hN.ρinf_pos.trans hN.ρinf_lt
  have hlam : (0 : ℝ) < 3 := by norm_num
  have hD : 0 < delta0 3 N.ρ N.ρinf := delta0_pos hlam hN.ρinf_lt
  have hDp : 0 < delta0 3 N.ρ N.ρinf ^ (4 * N.τ) := Real.rpow_pos_of_pos hD _
  have hγb0 : 0 < γbar := hγbar ▸ hN.γb
  obtain ⟨hC1, hC2, hbody⟩ := g1_sharp (n := N.n) hN.two_le hτ hN.ρinf_pos hN.ρinf_lt hM hσK hσB hσT
    hμ hγb0
  have hc1 : 0 < c1A N Xs := div_pos (Real.rpow_pos_of_pos hρ0 _) (mul_pos hXpos hDp)
  refine ⟨lt_min hC1 hc1, lt_max_of_lt_left hC2, ?_⟩
  intro 𝔅 h K ω γ e Ω hopen htransl hholo hper hreal hbd hK hKp hKr hball hDK hG hTu hTb hRef hω hCt
    hγ hγγbar hdio hE hsm
  have h00 : (0 : Fin N.n → ℂ) ∈ complexStrip N.n N.ρ := fun i => by simpa using hρ0
  have he0 : 0 ≤ e := (norm_nonneg _).trans (hE 0 h00)
  have hp4 : 0 < γ ^ 4 * N.ρ ^ (4 * N.τ) := mul_pos (pow_pos hγ 4) (Real.rpow_pos_of_pos hρ0 _)
  have hp2 : 0 ≤ e / (γ ^ 2 * N.ρ ^ (2 * N.τ)) :=
    div_nonneg he0 (mul_pos (pow_pos hγ 2) (Real.rpow_pos_of_pos hρ0 _)).le
  have hclose_mono : ∀ {K' : (Fin N.n → ℂ) → (Fin N.n → ℂ) × (Fin N.n → ℂ)} {c c' : ℝ}, c ≤ c' →
      (∀ θ ∈ complexStrip N.n N.ρinf, ‖K' θ - K θ‖ ≤ c * e / (γ ^ 2 * N.ρ ^ (2 * N.τ))) →
      ∀ θ ∈ complexStrip N.n N.ρinf, ‖K' θ - K θ‖ ≤ c' * e / (γ ^ 2 * N.ρ ^ (2 * N.τ)) :=
    fun {K' c c'} hc hb θ hθ => (hb θ hθ).trans (by
      rw [mul_div_assoc, mul_div_assoc]
      exact mul_le_mul_of_nonneg_right hc hp2)
  by_cases hcase : sharpC1 N.n N.τ (cohConstR N.n N.τ) M σK σB σT γbar μ N.τ N.ρ N.ρinf ≤ c1A N Xs
  · -- the branch of v1
    rw [min_eq_left hcase] at hsm
    obtain ⟨Kinf, h1, h2, h3, h4, h5, h6, h7⟩ := hbody 𝔅 h K ω γ e hopen htransl hholo hper hreal
        hbd
      hK hKp hKr hball hDK hG hTu hTb hγ hγγbar hdio hE hsm
    exact ⟨Kinf, h1, h2, h3, h4, h5, h6, hclose_mono (le_max_left _ _) h7⟩
  · -- route A
    rw [min_eq_right (not_le.1 hcase).le] at hsm
    have hsm' : e / (γ ^ 4 * delta0 3 N.ρ N.ρinf ^ (2 * (2 * N.τ))) < Xs := by
      rw [show 2 * (2 * N.τ) = 4 * N.τ by ring]
      have hρp : 0 < N.ρ ^ (4 * N.τ) := Real.rpow_pos_of_pos hρ0 _
      have e1 : c1A N Xs * e / (γ ^ 4 * N.ρ ^ (4 * N.τ)) =
          (e / (γ ^ 4 * delta0 3 N.ρ N.ρinf ^ (4 * N.τ))) / Xs := by
        unfold c1A
        field_simp
      rw [e1, div_lt_one hXpos] at hsm
      exact hsm
    obtain ⟨Kinf, h1, h2, h3, h4, h5, h6, h7⟩ := g1_branch_A hN hfix hΘ hτ hM hμ hγbar hsK hOk hXpos
      hopen htransl hholo hper hreal hbd hK hKp hKr hball hDK hG hTu hTb hRef hω hCt hγ hγγbar hdio
      he0 hE hsm'
    exact ⟨Kinf, h1, h2, h3, h4, h5, h6, hclose_mono (le_max_right _ _) h7⟩

/-- Never worse than v1: `C₁ ≤ C₁♯`. -/
theorem c1_min_le_sharpC1 {M σK σB σT μ γbar Xs : ℝ} :
    min (sharpC1 N.n N.τ (cohConstR N.n N.τ) M σK σB σT γbar μ N.τ N.ρ N.ρinf) (c1A N Xs) ≤
      sharpC1 N.n N.τ (cohConstR N.n N.τ) M σK σB σT γbar μ N.τ N.ρ N.ρinf :=
  min_le_left _ _

end KAM.Sharp2.RouteA

end
