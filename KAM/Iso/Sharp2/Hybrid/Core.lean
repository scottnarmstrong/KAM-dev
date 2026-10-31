/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Sharp2.Hybrid.Restart
public import KAM.Iso.Sharp2.RouteA.Ref.G1

/-!
# The isoenergetic hybrid theorem with a direct new torus (`bpI:p2s2hc:g1`)

`iso_g1_hybrid_core_R`: the isoenergetic branch of route A with L8′ applied to any `(K₁, s₁)` at the
restart numbers `N₁`, followed by the restart `iconcl_restart`.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator
open Matrix KAM.Sharp.Engine

namespace KAM.Iso.Sharp2.Hybrid

open KAM KAM.Torus KAM.Apost KAM.Iso.Linear KAM.Iso.Apost KAM.Sharp KAM.Sharp2
open KAM.Sharp2.RouteA KAM.Iso.Sharp2.RouteA KAM.Sharp2.RouteA.Ref KAM.Iso.Sharp2.RouteA.Ref
open KAM.Sharp2.Hybrid

/-- Core form, isoenergetic route A with L8′ (`bpI:p2s2hc:g1` with a direct new torus): every
hypothesis of `iso_g1_branch_R` for `(K₁, s₁)` at `N₁` (margin `μ₁`, ray margin `ν₁`), the ball of
`K`, the displacement, the frequency change and the restart inequalities. -/
theorem iso_g1_hybrid_core_R {N₁ : NumA} (hN : N₁.Wf) (hiso : N₁.iso = true)
    (hτ : (N₁.n : ℝ) - 1 ≤ N₁.τ) {M σK μ σK₁ σB₁ σT₁ μ₁ γbar σω ν₁ Xs Mh1 bF bT dinf dω : ℝ}
    {I₁ : InitA} (hM : 0 < M) (hμ₁ : 0 < μ₁) (hσω : 1 < σω) (hν₁ : 0 < ν₁)
    {ωstar : Fin N₁.n → ℝ} (hωstar : ωstar ≠ 0) (hγbar : γbar = N₁.γb)
    (hsK : N₁.sK = σK₁ - μ₁ / 2) (hΘ : N₁.Θ = σω * ‖ωstar‖) (hHY : N₁.HY = Mh1 * N₁.sN)
    (hOk : routeAOkRI N₁ bF (capRI N₁ (μ₁ / 2) bT (ν₁ / 2)) (initRI I₁ σK₁ σB₁ μ₁) Xs)
    (hB : Budget N₁ (σT₁ - μ₁) I₁.iH bF bT) (hXpos : 0 < Xs)
    {D : Set ((Fin N₁.n → ℂ) × (Fin N₁.n → ℂ))} {H : (Fin N₁.n → ℂ) × (Fin N₁.n → ℂ) → ℂ}
    {K K₁ : (Fin N₁.n → ℂ) → (Fin N₁.n → ℂ) × (Fin N₁.n → ℂ)} {s s₁ γ e₁ E₀ : ℝ}
    {Ω : Set (Fin N₁.n → ℝ)} (hopen : IsOpen D)
    (htransl : ∀ z ∈ D, ∀ k : Fin N₁.n → ℤ, (z.1 + (fun i => (k i : ℂ)), z.2) ∈ D)
    (hholo : DifferentiableOn ℂ H D)
    (hper : ∀ z ∈ D, ∀ k : Fin N₁.n → ℤ, H (z.1 + (fun i => (k i : ℂ)), z.2) = H z)
    (hreal : ∀ θ I : Fin N₁.n → ℝ, ((fun i => (θ i : ℂ)), (fun i => (I i : ℂ))) ∈ D →
      (H ((fun i => (θ i : ℂ)), (fun i => (I i : ℂ)))).im = 0)
    (hbd : ∀ z ∈ D, ‖fderiv ℂ H z‖ ≤ M ∧ ‖hamiltonianVectorFieldℂ H z‖ ≤ M ∧
      ‖fderiv ℂ (hamiltonianVectorFieldℂ H) z‖ ≤ M ∧
      ‖iteratedFDeriv ℂ 2 (hamiltonianVectorFieldℂ H) z‖ ≤ M ∧ ‖iteratedFDeriv ℂ 2 H z‖ ≤ M)
    (hK₁ : DifferentiableOn ℂ K₁ (complexStrip N₁.n N₁.ρ)) (hKp₁ : IsPrimaryOnStrip K₁ N₁.ρ)
    (hKr₁ : IsRealOnReals K₁)
    (hball₁ : ∀ θ ∈ complexStrip N₁.n N₁.ρ, Metric.ball (K₁ θ) μ₁ ⊆ D)
    (hDK₁ : ∀ θ ∈ complexStrip N₁.n N₁.ρ, ‖fderiv ℂ K₁ θ‖ ≤ σK₁ - μ₁)
    (hG₁ : ∀ θ ∈ complexStrip N₁.n N₁.ρ, IsUnit (gramMatrix K₁ θ).det ∧
      ∀ i, ∑ j, ‖(gramMatrix K₁ θ)⁻¹ i j‖ ≤ σB₁ - μ₁)
    (hTu₁ : IsUnit (KAM.Iso.extendedTorsionAverage H K₁ (s₁ • ωstar)).det)
    (hTb₁ : ∀ i, ∑ j, ‖(KAM.Iso.extendedTorsionAverage H K₁ (s₁ • ωstar))⁻¹ i j‖ ≤ σT₁ - μ₁)
    (hs1 : 1 < s₁) (hν1 : ν₁ ≤ (s₁ - 1) * ‖ωstar‖) (hν2 : ν₁ ≤ (σω - s₁) * ‖ωstar‖)
    (hRef₁ : RefHypIA N₁ I₁ Mh1 D H K₁ (s₁ • ωstar)) (hΩ : ∀ s' : ℝ, 1 ≤ s' → s' • ωstar ∈ Ω)
    (hCt : N₁.Cert γ Ω) (hγ : 0 < γ) (hγγbar : γ ≤ γbar) (hdio : IsDiophantine γ N₁.τ ωstar)
    (he0 : 0 ≤ e₁)
    (hE₁ : ∀ θ ∈ complexStrip N₁.n N₁.ρ, ‖invarianceError H K₁ (s₁ • ωstar) θ‖ ≤ e₁)
    (hEn₁ : ‖KAM.Iso.energyAverage H K₁ - (E₀ : ℂ)‖ ≤ e₁)
    (hsm : e₁ / (γ ^ 4 * delta0 3 N₁.ρ N₁.ρinf ^ (2 * (2 * N₁.τ))) < Xs)
    (hball : ∀ θ ∈ complexStrip N₁.n N₁.ρinf, Metric.ball (K θ) μ ⊆ D)
    (hd : ∀ θ ∈ complexStrip N₁.n N₁.ρinf, ‖K₁ θ - K θ‖ ≤ dinf)
    (hdω : ‖s₁ • ωstar - s • ωstar‖ ≤ dω)
    (hbud : dinf + c2I N₁ Xs * e₁ / (γ ^ 2 * N₁.ρ ^ (2 * N₁.τ)) ≤ μ / 2)
    (hσ : σK₁ - μ₁ / 2 ≤ σK - μ / 2) :
    IG1Concl D H K ωstar s E₀ N₁.ρinf μ σK σω
      (dinf + c2I N₁ Xs * e₁ / (γ ^ 2 * N₁.ρ ^ (2 * N₁.τ)))
      (dω + c3I N₁ Xs * e₁ / (γ ^ 2 * N₁.ρ ^ (2 * N₁.τ))) :=
  iconcl_restart hball hd hdω hbud hσ (iso_g1_branch_R hN hiso hτ hM hμ₁ hσω hν₁ hωstar hγbar hsK hΘ
    hHY hOk hB hXpos hopen htransl hholo hper hreal hbd hK₁ hKp₁ hKr₁ hball₁ hDK₁ hG₁ hTu₁ hTb₁ hs1
    hν1 hν2 hRef₁ hΩ hCt hγ hγγbar hdio he0 hE₁ hEn₁ hsm)

end KAM.Iso.Sharp2.Hybrid

end
