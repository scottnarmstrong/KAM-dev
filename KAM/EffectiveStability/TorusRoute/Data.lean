/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.TorusLagrangianCert
public import KAM.EffectiveStability.TorusRoute.Strip
public import KAM.EffectiveStability.TorusRoute.Real
public import KAM.EffectiveStability.TorusNormalForm

/-!
# Chart data and torus data of a certified torus (track B, package B5-ROUTE, items 1 and 2)

For `CertifiedTorusAt c ω* K∞ s∞` (under `G1Hyps c ω*` and the Diophantine condition on `ω*`):

* `certifiedTorus_chartData`: `TorusChartData (torusRealU K∞) (torusRealV K∞) (κc + disp/δ)`,
  from the B5-LAG outputs and the finite check `κc + disp/δ < 1`;
* `certifiedTorus_nfTorus`: `TorusNFTorus (torusRealU K∞) (torusRealV K∞) (realHam c.H) E₀ (s∞ ω*)`;
* `torusNFGraph_torusReal`: the graph torus is the real restriction of `K∞`.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator

namespace KAM.EffectiveStability

open KAM KAM.Torus KAM.Certificate KAM.Application CertArith

variable {n : ℕ} {α : Type} [CertArith α] {c : TorusCertificate n α} {ωstar : Fin n → ℝ}
  {Kinf : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {sinf : ℝ}

theorem torusNFGraph_torusReal (K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)) :
    torusNFGraph (torusRealU K) (torusRealV K) = realRestriction K := by
  funext φ
  refine Prod.ext ?_ rfl
  simp [torusNFGraph, torusChartX_torusRealU, torusRealX]

/-- The finite checks on the reference embedding: its angle derivative on the strip `T_{δφ}`. -/
theorem certifiedTorus_angle_fderiv_le (hG : G1Hyps c ωstar)
    (hT : CertifiedTorusAt c ωstar Kinf sinf) {δ δφ κc : ℝ} (hδ : 0 < δ)
    (hδφρ : δφ + δ ≤ (c.params.rhoInf : ℝ))
    (hκc : ∀ θ ∈ complexStrip n δφ, ‖fderiv ℂ (fun θ => (c.K θ).1 - θ) θ‖ ≤ κc)
    {θ : Fin n → ℂ} (hθ : θ ∈ complexStrip n δφ) :
    ‖fderiv ℂ (fun θ => (Kinf θ).1 - θ) θ‖ ≤ κc + (c.params.disp : ℝ) / δ :=
  norm_fderiv_angle_le_cx hT.2.2.1
    (hG.hK.mono fun _ hθ i => (hθ i).trans hG.hρinfρ) hδ
    (fun i => by have := hθ i; linarith) (hκc θ hθ) hT.2.2.2.2.2.2.2.2.2.1

/-- **Item 1.** The chart data of the exact torus of a certificate. -/
theorem certifiedTorus_chartData (hG : G1Hyps c ωstar)
    (hdio : IsDiophantine (c.params.γ : ℝ) (c.params.tau : ℝ) ωstar)
    (hT : CertifiedTorusAt c ωstar Kinf sinf) {δ δφ κc : ℝ} (hδ : 0 < δ) (hδφ : 0 < δφ)
    (hδφρ : δφ + δ ≤ (c.params.rhoInf : ℝ))
    (hκc : ∀ θ ∈ complexStrip n δφ, ‖fderiv ℂ (fun θ => (c.K θ).1 - θ) θ‖ ≤ κc)
    (hκ : κc + (c.params.disp : ℝ) / δ < 1) :
    TorusChartData (torusRealU Kinf) (torusRealV Kinf) (κc + (c.params.disp : ℝ) / δ) := by
  have hρ := hG.hρinf
  have hK := hT.2.2.1
  have hδρ : δ < (c.params.rhoInf : ℝ) := by linarith
  have hκr : ∀ φ : Fin n → ℝ, ‖fderiv ℂ (fun θ => (c.K θ).1 - θ) (realInclusion n φ)‖ ≤ κc :=
    fun φ => hκc _ (realInclusion_mem_complexStrip hδφ φ)
  refine
    { baseSmooth := (torusRealU_contDiff hρ hK).of_le
        (WithTop.coe_le_coe.2 (le_top : ((3 : ℕ) : ℕ∞) ≤ ⊤))
      baseContract := hκ
      baseBound := certifiedTorusAt_projection hG hT hδ hδρ hκr
      uPeriodic := fun φ k => torusRealU_add_int hρ hT.2.2.2.1 hT.2.2.2.2.1 φ k
      vPeriodic := fun φ k => torusRealV_add_int hρ hT.2.2.2.1 hT.2.2.2.2.1 φ k
      vSmooth := (torusRealV_contDiff hρ hK).of_le
        (WithTop.coe_le_coe.2 (le_top : ((2 : ℕ) : ℕ∞) ≤ ⊤))
      lagrangian := fun φ i j => ?_ }
  rw [torusChartX_torusRealU]
  exact certifiedTorusAt_realLagrangian hG hdio hT hδ hδρ φ i j

/-- `Re c.H ∘ ι₂` is differentiable at the real points over `D`. -/
theorem differentiableAt_realHam_of_mem (hG : G1Hyps c ωstar)
    {y : (Fin n → ℝ) × (Fin n → ℝ)} (hy : realInclusion₂ n y ∈ c.D) :
    DifferentiableAt ℝ (realHam c.H) y := by
  have hd := (hG.hholo.differentiableAt (hG.hopen.mem_nhds hy)).hasFDerivAt
  have h2 := (Complex.reCLM.hasFDerivAt (x := c.H (realInclusion₂ n y))).comp y
    (hd.restrictScalars ℝ |>.comp y (realInclusion₂ n).hasFDerivAt)
  exact h2.differentiableAt

/-- **Item 2.** The torus data of the exact torus of a certificate for the real Hamiltonian
`realHam c.H`, with frequency `ω' = s∞ ω*` and energy `E₀`. -/
theorem certifiedTorus_nfTorus (hG : G1Hyps c ωstar)
    (hT : CertifiedTorusAt c ωstar Kinf sinf) :
    TorusNFTorus (torusRealU Kinf) (torusRealV Kinf) (realHam c.H) (c.params.E0 : ℝ)
      (sinf • ωstar) := by
  have hg := torusNFGraph_torusReal Kinf
  refine ⟨fun φ => ?_, fun φ => ?_, fun φ => ?_⟩
  · rw [hg]
    refine differentiableAt_realHam_of_mem hG ?_
    rw [realInclusion₂_realRestriction hT.2.2.2.2.1]
    exact certifiedTorusAt_mem_D hG hT _ (realInclusion_mem_complexStrip hG.hρinf φ)
  · rw [hg]
    exact certifiedTorusAt_frequency hG hT φ
  · rw [hg]
    exact certifiedTorusAt_energy hG hT φ

end KAM.EffectiveStability

end
