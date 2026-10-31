/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Sharp2.Hybrid.Restart
public import KAM.Sharp2.RouteA.Ref.G1
public import KAM.Sharp2.RouteB.G1

/-!
# The hybrid theorem with a direct new torus (`bp:p2s2hc:g1`)

`g1_hybrid_core_R`, `g1_hybrid_core_B`: a route's branch theorem applied to any `K₁` at the restart
numbers `N₁`, followed by the restart `concl_restart`. Every hypothesis of the branch for `K₁` is a
hypothesis here; `KAM/Sharp2/Hybrid/G1.lean` derives them from the step bounds.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator
open Matrix KAM.Sharp.Engine

namespace KAM.Sharp2.Hybrid

open KAM KAM.Torus KAM.Apost KAM.Sharp KAM.Sharp2 KAM.Sharp2.RouteA

/-- Core form, route A with L8′ (`bp:p2s2hc:g1` with a direct new torus): every hypothesis of
`g1_branch_R` for `K₁` at the restart numbers `N₁` (strip `N₁.ρ`, margin `μ₁`, caps `σ₁`), the ball
of `K` on `T_{ρ∞}`, the displacement and the two restart inequalities. -/
theorem g1_hybrid_core_R {N₁ : NumA} (hN : N₁.Wf) (hfix : N₁.iso = false) (hΘ : N₁.Θ = 0)
    (hτ : (N₁.n : ℝ) - 1 ≤ N₁.τ) {M σK μ σK₁ σB₁ σT₁ μ₁ γbar Xs bF bT dinf : ℝ} {I₁ : InitA}
    (hM : 0 < M) (hμ₁ : 0 < μ₁) (hγbar : γbar = N₁.γb) (hsK : N₁.sK = σK₁ - μ₁ / 2)
    (hOk : routeAOkR N₁ bF (N₁.capR (μ₁ / 2) bT) (initR I₁ σK₁ σB₁ μ₁) Xs)
    (hB : Ref.Budget N₁ (σT₁ - μ₁) I₁.iH bF bT) (hXpos : 0 < Xs)
    {𝔅 : Set ((Fin N₁.n → ℂ) × (Fin N₁.n → ℂ))} {h : (Fin N₁.n → ℂ) × (Fin N₁.n → ℂ) → ℂ}
    {K K₁ : (Fin N₁.n → ℂ) → (Fin N₁.n → ℂ) × (Fin N₁.n → ℂ)} {ω : Fin N₁.n → ℝ} {γ e₁ : ℝ}
    {Ω : Set (Fin N₁.n → ℝ)} (hopen : IsOpen 𝔅)
    (htransl : ∀ z ∈ 𝔅, ∀ k : Fin N₁.n → ℤ, (z.1 + (fun i => (k i : ℂ)), z.2) ∈ 𝔅)
    (hholo : DifferentiableOn ℂ h 𝔅)
    (hper : ∀ z ∈ 𝔅, ∀ k : Fin N₁.n → ℤ, h (z.1 + (fun i => (k i : ℂ)), z.2) = h z)
    (hreal : ∀ θ I : Fin N₁.n → ℝ, ((fun i => (θ i : ℂ)), (fun i => (I i : ℂ))) ∈ 𝔅 →
      (h ((fun i => (θ i : ℂ)), (fun i => (I i : ℂ)))).im = 0)
    (hbd : ∀ z ∈ 𝔅, ‖fderiv ℂ h z‖ ≤ M ∧ ‖hamiltonianVectorFieldℂ h z‖ ≤ M ∧
      ‖fderiv ℂ (hamiltonianVectorFieldℂ h) z‖ ≤ M ∧
      ‖iteratedFDeriv ℂ 2 (hamiltonianVectorFieldℂ h) z‖ ≤ M)
    (hK₁ : DifferentiableOn ℂ K₁ (complexStrip N₁.n N₁.ρ)) (hKp₁ : IsPrimaryOnStrip K₁ N₁.ρ)
    (hKr₁ : IsRealOnReals K₁)
    (hball₁ : ∀ θ ∈ complexStrip N₁.n N₁.ρ, Metric.ball (K₁ θ) μ₁ ⊆ 𝔅)
    (hDK₁ : ∀ θ ∈ complexStrip N₁.n N₁.ρ, ‖fderiv ℂ K₁ θ‖ ≤ σK₁ - μ₁)
    (hG₁ : ∀ θ ∈ complexStrip N₁.n N₁.ρ, IsUnit (gramMatrix K₁ θ).det ∧
      ∀ i, ∑ j, ‖(gramMatrix K₁ θ)⁻¹ i j‖ ≤ σB₁ - μ₁)
    (hTu₁ : IsUnit (torsionAverage h K₁ ω).det)
    (hTb₁ : ∀ i, ∑ j, ‖(torsionAverage h K₁ ω)⁻¹ i j‖ ≤ σT₁ - μ₁)
    (hRef₁ : RefHypA N₁ I₁ 𝔅 h K₁ ω) (hω : ω ∈ Ω) (hCt : N₁.Cert γ Ω) (hγ : 0 < γ)
    (hγγbar : γ ≤ γbar) (hdio : IsDiophantine γ N₁.τ ω) (he0 : 0 ≤ e₁)
    (hE₁ : ∀ θ ∈ complexStrip N₁.n N₁.ρ, ‖invarianceError h K₁ ω θ‖ ≤ e₁)
    (hsm : e₁ / (γ ^ 4 * delta0 3 N₁.ρ N₁.ρinf ^ (2 * (2 * N₁.τ))) < Xs)
    (hball : ∀ θ ∈ complexStrip N₁.n N₁.ρinf, Metric.ball (K θ) μ ⊆ 𝔅)
    (hd : ∀ θ ∈ complexStrip N₁.n N₁.ρinf, ‖K₁ θ - K θ‖ ≤ dinf)
    (hbud : dinf + c2A N₁ Xs * e₁ / (γ ^ 2 * N₁.ρ ^ (2 * N₁.τ)) ≤ μ / 2)
    (hσ : σK₁ - μ₁ / 2 ≤ σK - μ / 2) :
    G1Concl 𝔅 h K ω N₁.ρinf μ σK (dinf + c2A N₁ Xs * e₁ / (γ ^ 2 * N₁.ρ ^ (2 * N₁.τ))) :=
  concl_restart hball hd hbud hσ (Ref.g1_branch_R hN hfix hΘ hτ hM hμ₁ hγbar hsK hOk hB hXpos hopen
    htransl hholo hper hreal hbd hK₁ hKp₁ hKr₁ hball₁ hDK₁ hG₁ hTu₁ hTb₁ hRef₁ hω hCt hγ hγγbar
    hdio he0 hE₁ hsm)

/-- Core form, route B: as `g1_hybrid_core_R` with `g1_branch_B` (`RefHypB`, `routeBOk`). -/
theorem g1_hybrid_core_B {n : ℕ} {N₁ : RouteB.NumB n} (hN : N₁.Wf) (hfix : N₁.iso = false)
    (hτ : (n : ℝ) - 1 ≤ N₁.τ) {M σK μ σK₁ σB₁ σT₁ μ₁ γbar Xs dinf : ℝ} {I₁ : RouteB.InitB}
    (hM : 0 < M) (hμ₁ : 0 < μ₁) (hγbar : γbar = N₁.γb) (hsK : N₁.sK = σK₁ - μ₁ / 2)
    (hI : I₁.Wf N₁ σT₁ μ₁) (hfit : N₁.Fits I₁)
    (hOk : RouteB.routeBOk N₁ (RouteB.capB N₁ σT₁ μ₁ 0) (RouteB.initB I₁ σK₁ σB₁ μ₁) (μ₁ / 2) Xs)
    (hXpos : 0 < Xs) {𝔅 : Set ((Fin n → ℂ) × (Fin n → ℂ))}
    {h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {K K₁ : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}
    {ω : Fin n → ℝ} {γ e₁ : ℝ} {Ω : Set (Fin n → ℝ)} (hopen : IsOpen 𝔅)
    (htransl : ∀ z ∈ 𝔅, ∀ k : Fin n → ℤ, (z.1 + (fun i => (k i : ℂ)), z.2) ∈ 𝔅)
    (hholo : DifferentiableOn ℂ h 𝔅)
    (hper : ∀ z ∈ 𝔅, ∀ k : Fin n → ℤ, h (z.1 + (fun i => (k i : ℂ)), z.2) = h z)
    (hreal : ∀ θ I : Fin n → ℝ, ((fun i => (θ i : ℂ)), (fun i => (I i : ℂ))) ∈ 𝔅 →
      (h ((fun i => (θ i : ℂ)), (fun i => (I i : ℂ)))).im = 0)
    (hbd : ∀ z ∈ 𝔅, ‖fderiv ℂ h z‖ ≤ M ∧ ‖hamiltonianVectorFieldℂ h z‖ ≤ M ∧
      ‖fderiv ℂ (hamiltonianVectorFieldℂ h) z‖ ≤ M ∧
      ‖iteratedFDeriv ℂ 2 (hamiltonianVectorFieldℂ h) z‖ ≤ M)
    (hK₁ : DifferentiableOn ℂ K₁ (complexStrip n N₁.ρ)) (hKp₁ : IsPrimaryOnStrip K₁ N₁.ρ)
    (hKr₁ : IsRealOnReals K₁) (hball₁ : ∀ θ ∈ complexStrip n N₁.ρ, Metric.ball (K₁ θ) μ₁ ⊆ 𝔅)
    (hDK₁ : ∀ θ ∈ complexStrip n N₁.ρ, ‖fderiv ℂ K₁ θ‖ ≤ σK₁ - μ₁)
    (hG₁ : ∀ θ ∈ complexStrip n N₁.ρ, IsUnit (gramMatrix K₁ θ).det ∧
      ∀ i, ∑ j, ‖(gramMatrix K₁ θ)⁻¹ i j‖ ≤ σB₁ - μ₁)
    (hTu₁ : IsUnit (torsionAverage h K₁ ω).det)
    (hTb₁ : ∀ i, ∑ j, ‖(torsionAverage h K₁ ω)⁻¹ i j‖ ≤ σT₁ - μ₁)
    (hRef₁ : RouteB.RefHypB N₁ I₁ 𝔅 h K₁ N₁.ρ) (hω : ω ∈ Ω) (hCt : N₁.Cert γ Ω) (hγ : 0 < γ)
    (hγγbar : γ ≤ γbar) (hdio : IsDiophantine γ N₁.τ ω)
    (hE₁ : ∀ θ ∈ complexStrip n N₁.ρ, ‖invarianceError h K₁ ω θ‖ ≤ e₁)
    (hsm : RouteB.c1B N₁ I₁ Xs * e₁ / (γ ^ 4 * N₁.ρ ^ (4 * N₁.τ)) < 1)
    (hball : ∀ θ ∈ complexStrip n N₁.ρinf, Metric.ball (K θ) μ ⊆ 𝔅)
    (hd : ∀ θ ∈ complexStrip n N₁.ρinf, ‖K₁ θ - K θ‖ ≤ dinf)
    (hbud : dinf + RouteB.c2B N₁ I₁ Xs * e₁ / (γ ^ 2 * N₁.ρ ^ (2 * N₁.τ)) ≤ μ / 2)
    (hσ : σK₁ - μ₁ / 2 ≤ σK - μ / 2) :
    G1Concl 𝔅 h K ω N₁.ρinf μ σK
      (dinf + RouteB.c2B N₁ I₁ Xs * e₁ / (γ ^ 2 * N₁.ρ ^ (2 * N₁.τ))) :=
  concl_restart hball hd hbud hσ (RouteB.g1_branch_B hN hfix hτ hM hμ₁ hγbar hsK hI hfit hOk hXpos
    hopen htransl hholo hper hreal hbd hK₁ hKp₁ hKr₁ hball₁ hDK₁ hG₁ hTu₁ hTb₁ hRef₁ hω hCt hγ
    hγγbar hdio hE₁ hsm)

end KAM.Sharp2.Hybrid

end
