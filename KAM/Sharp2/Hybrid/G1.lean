/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Sharp2.Hybrid.Core
public import KAM.Sharp2.Hybrid.Transfer
import Mathlib.Tactic.Linarith

/-!
# The hybrid theorem and the minimum with the existing routes (`bp:p2s2hc:g1`, `:frozen`)

* `g1_hybrid_R`, `g1_hybrid_B`: Theorem `bp:p2s2hc:g1`, route A with L8′ and route B, the step
  form. The hypotheses for the new torus are derived from the step bounds (`StepHyp`), then the
  core form applies;
* `g1_v2A'_hybrid`: Corollary `bp:p2s2hc:frozen`: the plain branch or the hybrid branch, by cases.
  Acceptance is never worse because the first disjunct remains available. The transfer formulas are
  conservative and do not reproduce a route at `ΔK = 0` (AUDIT-HYBRID-1, F3). The maximum is a
  common bound: a consumer that needs a branch's own closeness applies `g1_hybrid_R` or `g1_v2A'`
  directly.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator
open Matrix KAM.Sharp.Engine

namespace KAM.Sharp2.Hybrid

open KAM KAM.Torus KAM.Apost KAM.Sharp KAM.Sharp2 KAM.Sharp2.RouteA

variable {n : ℕ}

/-- `G1Concl` is monotone in the closeness. -/
theorem G1Concl.mono {𝔅 : Set ((Fin n → ℂ) × (Fin n → ℂ))} {h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
    {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {ω : Fin n → ℝ} {ρinf μ σK D D' : ℝ}
    (hD : D ≤ D') (h1 : G1Concl 𝔅 h K ω ρinf μ σK D) : G1Concl 𝔅 h K ω ρinf μ σK D' := by
  obtain ⟨Kinf, h1, h2, h3, h4, h5, h6, h7⟩ := h1
  exact ⟨Kinf, h1, h2, h3, h4, h5, h6, fun θ hθ => (h7 θ hθ).trans hD⟩

/-- `δ₀ ≤ (ρ - ρ∞)/6`. -/
theorem δ_zero_le (N : NumA) : N.δ 0 ≤ (N.ρ - N.ρinf) / 6 := by
  have e : N.δ 0 = min 1 ((N.ρ - N.ρinf) / (2 * 3)) := by
    simp [NumA.δ, Engine.deltaSeq, Engine.delta0]
  rw [e]
  refine (min_le_right _ _).trans (le_of_eq ?_)
  norm_num

/-- `ρ - δ₀ > 0`. -/
theorem ρ_sub_δ_pos {N : NumA} (hN : N.Wf) : 0 < N.ρ - N.δ 0 := by
  have h0 := hN.ρinf_pos
  have h1 := hN.ρinf_lt
  have h2 := δ_zero_le N
  linarith

/-- `x ↦ x - min {1, (x - ρ∞)/6}` is increasing: the torsion strip of the restart lies in the
original one (`step:p2s2hc:g-hyp`). -/
theorem bite_mono {a b' ρinf : ℝ} (hab : a ≤ b') :
    a - deltaSeq 3 a ρinf 0 ≤ b' - deltaSeq 3 b' ρinf 0 := by
  simp only [Engine.deltaSeq, Engine.delta0, pow_zero, one_mul, min_def]
  split_ifs <;> linarith

/-- Theorem `bp:p2s2hc:g1`, route A with L8′, the step form: frozen hypotheses and refined data of
`K` on `T_{ρ₀}`, a step with the bounds `(S1)–(S7)`, the restart numbers `N₁` with the transferred
initial values, and `HybOk_A'`. Conclusion: the frozen conclusion for `K` with closeness
`d∞ + c2A N₁ X⋆ e₁/(γ² ρ₁^{2τ})`. -/
theorem g1_hybrid_R {N₁ : NumA} (hN : N₁.Wf) (hfix : N₁.iso = false) (hΘ : N₁.Θ = 0)
    (hτ : (N₁.n : ℝ) - 1 ≤ N₁.τ) {M σK σB σT μ μ₁ γbar ρ₀ Xs bF bT cTh : ℝ} (k : KData)
    (b : StepNum) (hM : 0 < M) (hμ₁ : 0 < μ₁) (hγbar : γbar = N₁.γb) (hρ : N₁.ρ ≤ ρ₀)
    (hℓ : k.ℓ = σK - μ) (hβ : k.β = σB - μ) (hm : k.m = σT - μ)
    (hsK : N₁.sK = b.sK1 k μ₁ - μ₁ / 2)
    (hOk : routeAOkR N₁ bF (N₁.capR (μ₁ / 2) bT)
      (initR (b.init1 k N₁.n N₁.M1 N₁.M2 (N₁.δ 0) cTh) (b.sK1 k μ₁) (b.sB1 k μ₁) μ₁) Xs)
    (hB : Ref.Budget N₁ (b.sT1 k N₁.n N₁.M1 N₁.M2 (N₁.δ 0) cTh μ₁ - μ₁)
      (b.init1 k N₁.n N₁.M1 N₁.M2 (N₁.δ 0) cTh).iH bF bT) (hXpos : 0 < Xs)
    (hm1 : b.d0 + μ₁ ≤ μ) (hm2 : b.d1 + μ₁ / 2 ≤ μ / 2) (hgS : k.β * (b.frS k).g < 1)
    (hgR : k.β * (b.frR k).g < 1) (htA : k.m * b.tA k N₁.n N₁.M1 N₁.M2 (N₁.δ 0) cTh < 1)
    {𝔅 : Set ((Fin N₁.n → ℂ) × (Fin N₁.n → ℂ))} {h : (Fin N₁.n → ℂ) × (Fin N₁.n → ℂ) → ℂ}
    {K ΔK : (Fin N₁.n → ℂ) → (Fin N₁.n → ℂ) × (Fin N₁.n → ℂ)} {ω : Fin N₁.n → ℝ} {γ : ℝ}
    {Ω : Set (Fin N₁.n → ℝ)} (hopen : IsOpen 𝔅)
    (htransl : ∀ z ∈ 𝔅, ∀ k : Fin N₁.n → ℤ, (z.1 + (fun i => (k i : ℂ)), z.2) ∈ 𝔅)
    (hholo : DifferentiableOn ℂ h 𝔅)
    (hper : ∀ z ∈ 𝔅, ∀ k : Fin N₁.n → ℤ, h (z.1 + (fun i => (k i : ℂ)), z.2) = h z)
    (hreal : ∀ θ I : Fin N₁.n → ℝ, ((fun i => (θ i : ℂ)), (fun i => (I i : ℂ))) ∈ 𝔅 →
      (h ((fun i => (θ i : ℂ)), (fun i => (I i : ℂ)))).im = 0)
    (hbd : ∀ z ∈ 𝔅, ‖fderiv ℂ h z‖ ≤ M ∧ ‖hamiltonianVectorFieldℂ h z‖ ≤ M ∧
      ‖fderiv ℂ (hamiltonianVectorFieldℂ h) z‖ ≤ M ∧
      ‖iteratedFDeriv ℂ 2 (hamiltonianVectorFieldℂ h) z‖ ≤ M)
    (hdX : ∀ z ∈ 𝔅, ‖fderiv ℂ (hamiltonianVectorFieldℂ h) z‖ ≤ N₁.M1)
    (hd2X : ∀ z ∈ 𝔅, ‖iteratedFDeriv ℂ 2 (hamiltonianVectorFieldℂ h) z‖ ≤ N₁.M2)
    (hcTh : ∀ z ∈ 𝔅, ‖hamComm h z‖ ≤ cTh)
    (hK : DifferentiableOn ℂ K (complexStrip N₁.n ρ₀)) (hKp : IsPrimaryOnStrip K ρ₀)
    (hKr : IsRealOnReals K) (hball : ∀ θ ∈ complexStrip N₁.n ρ₀, Metric.ball (K θ) μ ⊆ 𝔅)
    (hDK : ∀ θ ∈ complexStrip N₁.n ρ₀, ‖fderiv ℂ K θ‖ ≤ σK - μ)
    (hG : ∀ θ ∈ complexStrip N₁.n ρ₀, IsUnit (gramMatrix K θ).det ∧
      ∀ i, ∑ j, ‖(gramMatrix K θ)⁻¹ i j‖ ≤ σB - μ)
    (hTu : IsUnit (torsionAverage h K ω).det)
    (hTb : ∀ i, ∑ j, ‖(torsionAverage h K ω)⁻¹ i j‖ ≤ σT - μ)
    (hLt : ∀ θ ∈ complexStrip N₁.n ρ₀, ‖(tangentMat K θ)ᵀ‖ ≤ k.ℓt)
    (hNm : ∀ θ ∈ complexStrip N₁.n ρ₀, ‖normalMat K θ‖ ≤ k.ν)
    (hNt : ∀ θ ∈ complexStrip N₁.n ρ₀, ‖(normalMat K θ)ᵀ‖ ≤ k.νt)
    (hT : ∀ θ ∈ complexStrip N₁.n (N₁.ρ - N₁.δ 0), ‖torsion h K ω θ‖ ≤ k.t)
    (hS : IsStep ΔK ρ₀) (hb : StepBounds h K ΔK ω ω N₁.ρ N₁.ρinf (N₁.ρ - N₁.δ 0) b)
    (hω : ω ∈ Ω) (hCt : N₁.Cert γ Ω) (hγ : 0 < γ) (hγγbar : γ ≤ γbar)
    (hdio : IsDiophantine γ N₁.τ ω)
    (hsm : b.e1 N₁.M2 / (γ ^ 4 * delta0 3 N₁.ρ N₁.ρinf ^ (2 * (2 * N₁.τ))) < Xs)
    (hbud : b.dinf + c2A N₁ Xs * b.e1 N₁.M2 / (γ ^ 2 * N₁.ρ ^ (2 * N₁.τ)) ≤ μ / 2) :
    G1Concl 𝔅 h K ω N₁.ρinf μ σK
      (b.dinf + c2A N₁ Xs * b.e1 N₁.M2 / (γ ^ 2 * N₁.ρ ^ (2 * N₁.τ))) := by
  have hρ₁ : 0 < N₁.ρ := hN.ρinf_pos.trans hN.ρinf_lt
  have hSt : Standing N₁.n N₁.τ M N₁.sK N₁.sB N₁.sT 𝔅 h ω γ :=
    { toParams := ⟨hN.two_le, hτ, hM, hN.sK, hN.sB, hN.sT⟩
      isOpen := hopen
      transl_mem := htransl
      holo := hholo
      periodic := hper
      real := hreal
      bounds := fun z hz => ⟨(hbd z hz).2.1, (hbd z hz).2.2.1, (hbd z hz).2.2.2⟩
      gamma_pos := hγ
      dio := hdio }
  have H : StepHyp 𝔅 h K ΔK ω ω ρ₀ N₁.ρ N₁.ρinf (N₁.δ 0) N₁.M1 N₁.M2 cTh μ μ₁ k b :=
    { one_le := by have := hN.two_le; omega
      std := ⟨_, _, _, _, _, _, hSt⟩
      std₁ := ⟨_, _, _, _, _, _, hSt⟩
      δ_pos := hN.δ_pos 0
      ρδ_pos := ρ_sub_δ_pos hN
      ρ_le := hρ
      holo := hK
      ball := hball
      L := fun θ hθ => by rw [FrameAux.norm_tangentMat, hℓ]; exact hDK θ hθ
      Lt := hLt
      gram := fun θ hθ => (hG θ hθ).1
      B := fun θ hθ => by rw [hβ]; exact norm_le_of_rowSum_le hN.two_le (hG θ hθ).2
      Nm := hNm
      Nt := hNt
      step := hS
      bd := hb
      dX := hdX
      d2X := hd2X
      comm := hcTh
      m1 := hm1
      μ₁_pos := hμ₁
      gS := hgS
      gR := hgR }
  obtain ⟨h1, h2, h3, h4, h5⟩ := H.struct hKp hKr
  have hq : 0 < 1 - k.m * b.tA k N₁.n N₁.M1 N₁.M2 (N₁.δ 0) cTh := by linarith
  have hm0 : 0 < k.m := by
    have := hB.mT_pos
    rw [StepNum.sT1, add_sub_cancel_right] at this
    exact (div_pos_iff_of_pos_right hq).1 this
  obtain ⟨hTu₁, hTn₁⟩ := H.twist hTu (by rw [hm]; exact norm_le_of_rowSum_le hN.two_le hTb) hm0 htA
  refine g1_hybrid_core_R hN hfix hΘ hτ hM hμ₁ hγbar hsK hOk hB hXpos hopen htransl hholo hper hreal
    hbd h1 h2 h3 h4 ?_ ?_ hTu₁ ?_ ?_ hω hCt hγ hγγbar hdio
    ((norm_nonneg _).trans (H.err _ (H.real₁ 0))) H.err hsm
    (fun θ hθ => hball θ (strip_le (hN.ρinf_lt.le.trans hρ) hθ))
    (fun θ hθ => by simpa using hb.dinf θ hθ) hbud ?_
  · intro θ hθ
    rw [StepNum.sK1, add_sub_cancel_right]
    exact h5 θ hθ
  · intro θ hθ
    refine ⟨(H.frames hθ).1, fun i => ?_⟩
    rw [StepNum.sB1, add_sub_cancel_right]
    exact (H.gramRow hθ).2 i
  · intro i
    rw [StepNum.sT1, add_sub_cancel_right]
    exact hTn₁ i
  · exact ⟨hdX, hd2X, fun θ hθ => (H.frames hθ).2.1, fun θ hθ => (H.frames hθ).2.2.2.2.2.2.1,
      fun θ hθ => (H.frames hθ).2.2.2.2.2.2.2, H.tors₁ hT⟩
  · rw [StepNum.sK1, hℓ]
    linarith

/-- The transferred initial values of `K₁` for route B (Definition `bp:p2s2hc:data`). -/
def StepNum.initB1 (b : StepNum) (k : KData) : RouteB.InitB :=
  ⟨k.ℓt + b.d1t, k.ν + (b.frS k).nΔ, k.νt + (b.frS k).nΔt⟩

/-- Theorem `bp:p2s2hc:g1`, route B, the step form: as `g1_hybrid_R` with `g1_hybrid_core_B`.
`δ` is the bite of the strip of the local bounds; route B has no bound `k.t`, since it derives the
torsion cap. -/
theorem g1_hybrid_B {n : ℕ} {N₁ : RouteB.NumB n} (hN : N₁.Wf) (hfix : N₁.iso = false)
    (hτ : (n : ℝ) - 1 ≤ N₁.τ) {M σK σB σT μ μ₁ γbar ρ₀ δ Xs : ℝ} (k : KData) (b : StepNum)
    (hM : 0 < M) (hμ₁ : 0 < μ₁) (hγbar : γbar = N₁.γb) (hρ : N₁.ρ ≤ ρ₀) (hδ : 0 < δ)
    (hδρ : 0 < N₁.ρ - δ) (hℓ : k.ℓ = σK - μ) (hβ : k.β = σB - μ) (hm : k.m = σT - μ)
    (hsK : N₁.sK = b.sK1 k μ₁ - μ₁ / 2)
    (hI : (b.initB1 k).Wf N₁ (b.sT1 k n N₁.M1 N₁.M2 δ N₁.cTh μ₁) μ₁)
    (hfit : N₁.Fits (b.initB1 k))
    (hOk : RouteB.routeBOk N₁ (RouteB.capB N₁ (b.sT1 k n N₁.M1 N₁.M2 δ N₁.cTh μ₁) μ₁ 0)
      (RouteB.initB (b.initB1 k) (b.sK1 k μ₁) (b.sB1 k μ₁) μ₁) (μ₁ / 2) Xs) (hXpos : 0 < Xs)
    (hm1 : b.d0 + μ₁ ≤ μ) (hm2 : b.d1 + μ₁ / 2 ≤ μ / 2) (hgS : k.β * (b.frS k).g < 1)
    (hgR : k.β * (b.frR k).g < 1) (htA : k.m * b.tA k n N₁.M1 N₁.M2 δ N₁.cTh < 1)
    {𝔅 : Set ((Fin n → ℂ) × (Fin n → ℂ))} {h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
    {K ΔK : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {ω : Fin n → ℝ} {γ : ℝ}
    {Ω : Set (Fin n → ℝ)} (hopen : IsOpen 𝔅)
    (htransl : ∀ z ∈ 𝔅, ∀ k : Fin n → ℤ, (z.1 + (fun i => (k i : ℂ)), z.2) ∈ 𝔅)
    (hholo : DifferentiableOn ℂ h 𝔅)
    (hper : ∀ z ∈ 𝔅, ∀ k : Fin n → ℤ, h (z.1 + (fun i => (k i : ℂ)), z.2) = h z)
    (hreal : ∀ θ I : Fin n → ℝ, ((fun i => (θ i : ℂ)), (fun i => (I i : ℂ))) ∈ 𝔅 →
      (h ((fun i => (θ i : ℂ)), (fun i => (I i : ℂ)))).im = 0)
    (hbd : ∀ z ∈ 𝔅, ‖fderiv ℂ h z‖ ≤ M ∧ ‖hamiltonianVectorFieldℂ h z‖ ≤ M ∧
      ‖fderiv ℂ (hamiltonianVectorFieldℂ h) z‖ ≤ M ∧
      ‖iteratedFDeriv ℂ 2 (hamiltonianVectorFieldℂ h) z‖ ≤ M)
    (hdX : ∀ z ∈ 𝔅, ‖fderiv ℂ (hamiltonianVectorFieldℂ h) z‖ ≤ N₁.M1)
    (hd2X : ∀ z ∈ 𝔅, ‖iteratedFDeriv ℂ 2 (hamiltonianVectorFieldℂ h) z‖ ≤ N₁.M2)
    (hcTh : ∀ z ∈ 𝔅, ‖hamComm h z‖ ≤ N₁.cTh)
    (hlip : ∀ z ∈ 𝔅, ∀ z' ∈ 𝔅, segment ℝ z z' ⊆ 𝔅 →
      ‖hamComm h z - hamComm h z'‖ ≤ N₁.cDTh * ‖z - z'‖)
    (hK : DifferentiableOn ℂ K (complexStrip n ρ₀)) (hKp : IsPrimaryOnStrip K ρ₀)
    (hKr : IsRealOnReals K) (hball : ∀ θ ∈ complexStrip n ρ₀, Metric.ball (K θ) μ ⊆ 𝔅)
    (hDK : ∀ θ ∈ complexStrip n ρ₀, ‖fderiv ℂ K θ‖ ≤ σK - μ)
    (hG : ∀ θ ∈ complexStrip n ρ₀, IsUnit (gramMatrix K θ).det ∧
      ∀ i, ∑ j, ‖(gramMatrix K θ)⁻¹ i j‖ ≤ σB - μ)
    (hTu : IsUnit (torsionAverage h K ω).det)
    (hTb : ∀ i, ∑ j, ‖(torsionAverage h K ω)⁻¹ i j‖ ≤ σT - μ)
    (hLt : ∀ θ ∈ complexStrip n ρ₀, ‖(tangentMat K θ)ᵀ‖ ≤ k.ℓt)
    (hNm : ∀ θ ∈ complexStrip n ρ₀, ‖normalMat K θ‖ ≤ k.ν)
    (hNt : ∀ θ ∈ complexStrip n ρ₀, ‖(normalMat K θ)ᵀ‖ ≤ k.νt)
    (hS : IsStep ΔK ρ₀) (hb : StepBounds h K ΔK ω ω N₁.ρ N₁.ρinf (N₁.ρ - δ) b)
    (hω : ω ∈ Ω) (hCt : N₁.Cert γ Ω) (hγ : 0 < γ) (hγγbar : γ ≤ γbar)
    (hdio : IsDiophantine γ N₁.τ ω)
    (hsm : RouteB.c1B N₁ (b.initB1 k) Xs * b.e1 N₁.M2 / (γ ^ 4 * N₁.ρ ^ (4 * N₁.τ)) < 1)
    (hbud : b.dinf + RouteB.c2B N₁ (b.initB1 k) Xs * b.e1 N₁.M2 / (γ ^ 2 * N₁.ρ ^ (2 * N₁.τ)) ≤
      μ / 2) :
    G1Concl 𝔅 h K ω N₁.ρinf μ σK
      (b.dinf + RouteB.c2B N₁ (b.initB1 k) Xs * b.e1 N₁.M2 / (γ ^ 2 * N₁.ρ ^ (2 * N₁.τ))) := by
  have hρinf : N₁.ρinf ≤ N₁.ρ := hN.ρinf_lt.le
  have hSt : Standing n N₁.τ M N₁.sK N₁.sB N₁.sT 𝔅 h ω γ :=
    { toParams := ⟨hN.two_le, hτ, hM, hN.caps.1, hN.caps.2.2.1, hN.caps.2.2.2.2.2⟩
      isOpen := hopen
      transl_mem := htransl
      holo := hholo
      periodic := hper
      real := hreal
      bounds := fun z hz => ⟨(hbd z hz).2.1, (hbd z hz).2.2.1, (hbd z hz).2.2.2⟩
      gamma_pos := hγ
      dio := hdio }
  have H : StepHyp 𝔅 h K ΔK ω ω ρ₀ N₁.ρ N₁.ρinf δ N₁.M1 N₁.M2 N₁.cTh μ μ₁ k b :=
    { one_le := by have := hN.two_le; omega
      std := ⟨_, _, _, _, _, _, hSt⟩
      std₁ := ⟨_, _, _, _, _, _, hSt⟩
      δ_pos := hδ
      ρδ_pos := hδρ
      ρ_le := hρ
      holo := hK
      ball := hball
      L := fun θ hθ => by rw [FrameAux.norm_tangentMat, hℓ]; exact hDK θ hθ
      Lt := hLt
      gram := fun θ hθ => (hG θ hθ).1
      B := fun θ hθ => by rw [hβ]; exact norm_le_of_rowSum_le hN.two_le (hG θ hθ).2
      Nm := hNm
      Nt := hNt
      step := hS
      bd := hb
      dX := hdX
      d2X := hd2X
      comm := hcTh
      m1 := hm1
      μ₁_pos := hμ₁
      gS := hgS
      gR := hgR }
  obtain ⟨h1, h2, h3, h4, h5⟩ := H.struct hKp hKr
  have hq : 0 < 1 - k.m * b.tA k n N₁.M1 N₁.M2 δ N₁.cTh := by linarith
  have hm0 : 0 < k.m := by
    have := hI.torsion.1
    rw [StepNum.sT1, add_sub_cancel_right] at this
    exact (div_pos_iff_of_pos_right hq).1 this
  obtain ⟨hTu₁, hTn₁⟩ := H.twist hTu (by rw [hm]; exact norm_le_of_rowSum_le hN.two_le hTb) hm0 htA
  refine g1_hybrid_core_B hN hfix hτ hM hμ₁ hγbar hsK hI hfit hOk hXpos hopen htransl hholo hper
    hreal hbd h1 h2 h3 h4 ?_ ?_ hTu₁ ?_ ?_ hω hCt hγ hγγbar hdio H.err hsm
    (fun θ hθ => hball θ (strip_le (hρinf.trans hρ) hθ))
    (fun θ hθ => by simpa using hb.dinf θ hθ) hbud ?_
  · intro θ hθ
    rw [StepNum.sK1, add_sub_cancel_right]
    exact h5 θ hθ
  · intro θ hθ
    refine ⟨(H.frames hθ).1, fun i => ?_⟩
    rw [StepNum.sB1, add_sub_cancel_right]
    exact (H.gramRow hθ).2 i
  · intro i
    rw [StepNum.sT1, add_sub_cancel_right]
    exact hTn₁ i
  · exact ⟨hdX, hd2X, hcTh, hlip, fun θ hθ => (H.frames hθ).2.1,
      fun θ hθ => (H.frames hθ).2.2.2.2.2.2.1, fun θ hθ => (H.frames hθ).2.2.2.2.2.2.2⟩
  · rw [StepNum.sK1, hℓ]
    linarith

/-- Corollary `bp:p2s2hc:frozen`, route A with L8′: the plain branch (`g1_v2A'`'s constants at
`N`) or the hybrid branch (`HybOkR` at `N.restart R`), by cases; the closeness is the maximum.
Every hypothesis of `G1BodyA` is kept; the step `ΔK`, its bounds and the hybrid numbers are
additional and are used only in the hybrid branch. -/
theorem g1_v2A'_hybrid (N : NumA) (hN : N.Wf) (hfix : N.iso = false) (hΘ : N.Θ = 0)
    (hτ : (N.n : ℝ) - 1 ≤ N.τ) {M σK σB σT μ γbar Xs bF bT : ℝ} (I : InitA) (hM : 0 < M)
    (hσK : 0 < σK) (hσB : 0 < σB) (hσT : 0 < σT) (hμ : 0 < μ) (hγbar : γbar = N.γb)
    (hsK : N.sK = σK - μ / 2) (hOk : routeAOkR N bF (N.capR (μ / 2) bT) (initR I σK σB μ) Xs)
    (hB : Ref.Budget N (σT - μ) I.iH bF bT) (hXpos : 0 < Xs) :
    ∀ (𝔅 : Set ((Fin N.n → ℂ) × (Fin N.n → ℂ))) (h : (Fin N.n → ℂ) × (Fin N.n → ℂ) → ℂ)
      (K ΔK : (Fin N.n → ℂ) → (Fin N.n → ℂ) × (Fin N.n → ℂ)) (ω : Fin N.n → ℝ) (γ e : ℝ)
      (Ω : Set (Fin N.n → ℝ)) (R : RestartA) (k : KData) (b : StepNum)
      (μ₁ X₁ bF₁ bT₁ cTh : ℝ),
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
      -- the hybrid data (used in the second branch only)
      (∀ z ∈ 𝔅, ‖hamComm h z‖ ≤ cTh) → I.iLt ≤ k.ℓt → I.iN ≤ k.ν → I.iNt ≤ k.νt →
      I.iH ≤ k.t → IsStep ΔK N.ρ →
      StepBounds h K ΔK ω ω R.ρ₁ N.ρinf (R.ρ₁ - (N.restart R).δ 0) b →
      (N.restart R).Cert γ Ω →
      (min (sharpC1 N.n N.τ (cohConstR N.n N.τ) M σK σB σT γbar μ N.τ N.ρ N.ρinf) (c1A N Xs) *
          e / (γ ^ 4 * N.ρ ^ (4 * N.τ)) < 1 ∨
        HybOkR N R k b σK σB σT μ μ₁ γ X₁ bF₁ bT₁ cTh) →
      G1Concl 𝔅 h K ω N.ρinf μ σK
        (max (max (sharpC2 N.n N.τ (cohConstR N.n N.τ) M σK σB σT γbar N.τ N.ρ N.ρinf)
            (c2A N Xs) * e / (γ ^ 2 * N.ρ ^ (2 * N.τ)))
          (b.dinf + c2A (N.restart R) X₁ * b.e1 N.M2 / (γ ^ 2 * R.ρ₁ ^ (2 * N.τ)))) := by
  intro 𝔅 h K ΔK ω γ e Ω R k b μ₁ X₁ bF₁ bT₁ cTh hopen htransl hholo hper hreal hbd hK hKp hKr hball
    hDK hG hTu hTb hRef hω hCt hγ hγγbar hdio hE hcTh hLt hNu hNtt hHt hS hb hCt₁ hor
  rcases hor with hsm | hy
  · obtain ⟨-, -, hbody⟩ := g1_v2A' hN hfix hΘ hτ I hM hσK hσB hσT hμ hγbar hsK hOk hB hXpos
    exact G1Concl.mono (le_max_left _ _) (hbody 𝔅 h K ω γ e Ω hopen htransl hholo hper hreal hbd hK
      hKp hKr hball hDK hG hTu hTb hRef hω hCt hγ hγγbar hdio hE hsm)
  · refine G1Concl.mono (le_max_right _ _) (g1_hybrid_R (N₁ := N.restart R) (ρ₀ := N.ρ) hy.wf hfix
      hΘ hτ k b hM hy.μ₁_pos hγbar hy.ρ_le hy.ℓ hy.β hy.m hy.sK hy.ok hy.budget hy.Xs_pos hy.m1
      hy.m2 hy.gS hy.gR hy.tA hopen htransl hholo hper hreal hbd hRef.dX hRef.d2X hcTh hK hKp hKr
      hball hDK hG hTu hTb (fun θ hθ => (hRef.tangentT θ hθ).trans hLt)
      (fun θ hθ => (hRef.normal θ hθ).trans hNu) (fun θ hθ => (hRef.normalT θ hθ).trans hNtt)
      (fun θ hθ => (hRef.tors θ (strip_le (bite_mono hy.ρ_le) hθ)).trans hHt) hS hb hω hCt₁ hγ
      hγγbar hdio hy.small hy.bud)

end KAM.Sharp2.Hybrid

end
