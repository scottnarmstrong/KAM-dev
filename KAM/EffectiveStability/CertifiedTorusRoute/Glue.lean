/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.TorusRoute.Bound
public import KAM.EffectiveStability.CauchyThird
public import KAM.EffectiveStability.Domains

/-!
# Gluing the real and complexified charts (track B, package B5-ROUTE, items 3 and 4)

* `RouteChecks.chartData`: the real chart data with `κ = κc + disp/δ` (item 1).
* `realHam_comp_chart_eq`: `realHam c.H ∘ Ψ = Re (c.H ∘ Ψ_ℂ) ∘ ι₂` (so `hG`, `hD3` reduce to the
  complexified Hamiltonian).
* `contDiffOn_realPart_of_holo`: the real slice of a holomorphic map is smooth.
* `ball_subset_routeDomain`: the Cauchy ball about a chart point of the cylinder lies in the domain.
* `realHam_chart_mem` / `realHam_chart_shift`: the chart image lies over `D`, and `realHam c.H`
  is angle-periodic along it.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator

namespace KAM.EffectiveStability

open KAM KAM.Torus KAM.Certificate KAM.Application CertArith Metric

variable {n : ℕ} {α : Type} [CertArith α] {c : TorusCertificate n α} {ωstar : Fin n → ℝ}
  {Kinf : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {sinf : ℝ} {κc δ δφ ρJ : ℝ}

theorem contDiffOn_realPart_of_holo {f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
    {U : Set ((Fin n → ℂ) × (Fin n → ℂ))} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (m : WithTop ℕ∞) :
    ContDiffOn ℝ m (fun y => (f (realInclusion₂ n y)).re) (realInclusion₂ n ⁻¹' U) := by
  have hcC : ContDiffOn ℂ m f U :=
    (KAM.analyticOnNhd_of_differentiableOn hU hf).contDiffOn hU.uniqueDiffOn
  have hcR : ContDiffOn ℝ m f U := hcC.restrict_scalars ℝ
  exact Complex.reCLM.contDiff.comp_contDiffOn
    (hcR.comp (realInclusion₂ n).contDiff.contDiffOn fun _ h => h)

theorem RouteChecks.routeKappa_lt_one (hG : G1Hyps c ωstar) (hT : CertifiedTorusAt c ωstar Kinf sinf)
    (h : RouteChecks c κc δ δφ ρJ) : κc + (c.params.disp : ℝ) / δ < 1 := by
  have h0 := h.routeKappa_nonneg hG hT
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast (by have := hG.hn; omega : 1 ≤ n)
  nlinarith [h.hκ]

/-- **Item 1** for a `RouteChecks` bundle. -/
theorem RouteChecks.chartData (hG : G1Hyps c ωstar)
    (hdio : IsDiophantine (c.params.γ : ℝ) (c.params.tau : ℝ) ωstar)
    (hT : CertifiedTorusAt c ωstar Kinf sinf) (h : RouteChecks c κc δ δφ ρJ) :
    TorusChartData (torusRealU Kinf) (torusRealV Kinf) (κc + (c.params.disp : ℝ) / δ) :=
  certifiedTorus_chartData hG hdio hT h.hδ h.hδφ h.hδφρ h.hκc (h.routeKappa_lt_one hG hT)

theorem RouteChecks.chart_det_ne (hG : G1Hyps c ωstar)
    (hdio : IsDiophantine (c.params.γ : ℝ) (c.params.tau : ℝ) ωstar)
    (hT : CertifiedTorusAt c ωstar Kinf sinf) (h : RouteChecks c κc δ δφ ρJ) (φ : Fin n → ℝ) :
    (torusChartJac (torusRealU Kinf) φ).det ≠ 0 :=
  torusChartJac_det_ne (h.chartData hG hdio hT).toTorusBaseData φ

/-- The real Hamiltonian along the real chart is the real slice of `c.H ∘ Ψ_ℂ`. -/
theorem RouteChecks.realHam_comp_chart_eq (hG : G1Hyps c ωstar)
    (hdio : IsDiophantine (c.params.γ : ℝ) (c.params.tau : ℝ) ωstar)
    (hT : CertifiedTorusAt c ωstar Kinf sinf) (h : RouteChecks c κc δ δφ ρJ)
    (w : (Fin n → ℝ) × (Fin n → ℝ)) :
    realHam c.H (torusChartMap (torusRealU Kinf) (torusRealV Kinf) w) =
      (c.H (torusCxChart Kinf (realInclusion₂ n w))).re := by
  unfold realHam
  rw [← torusCxChart_realInclusion hG.hρinf hT.2.2.1 hT.2.2.2.2.1 (h.chart_det_ne hG hdio hT) w]

/-- The Cauchy ball about a chart point of the cylinder lies in the domain. -/
theorem ball_subset_routeDomain {b : Fin n → ℝ} {ε r : ℝ} (hr : r ≤ δφ)
    (hrJ : ∀ j, b j + ε + r ≤ ρJ) (hρJ0 : 0 < ρJ) {y : (Fin n → ℝ) × (Fin n → ℝ)}
    (hy : ∀ j, |y.2 j| < b j + ε) :
    ball (realInclusion₂ n y) r ⊆ routeDomain n δφ ρJ := by
  intro z hz
  rw [mem_ball, dist_eq_norm, Prod.norm_def, max_lt_iff] at hz
  obtain ⟨hz1, hz2⟩ := hz
  simp only [Prod.fst_sub, Prod.snd_sub, realInclusion₂_apply] at hz1 hz2
  refine ⟨fun i => ?_, (pi_norm_lt_iff hρJ0).2 fun j => ?_⟩
  · have h1 : |(z.1 i).im| ≤ ‖z.1 i - realInclusion n y.1 i‖ := by
      have : (z.1 i).im = (z.1 i - realInclusion n y.1 i).im := by simp
      rw [this]; exact Complex.abs_im_le_norm _
    have h2 := norm_le_pi_norm (z.1 - realInclusion n y.1) i
    simp only [Pi.sub_apply] at h2 h1
    linarith
  · have h2 := norm_le_pi_norm (z.2 - (realInclusion₂ n y).2) j
    simp only [realInclusion₂_apply, Pi.sub_apply] at h2
    have h3 : ‖z.2 j‖ ≤ ‖z.2 j - realInclusion n y.2 j‖ + |y.2 j| := by
      calc ‖z.2 j‖ = ‖(z.2 j - realInclusion n y.2 j) + realInclusion n y.2 j‖ := by ring_nf
        _ ≤ _ := norm_add_le _ _ |>.trans (by simp)
    linarith [hrJ j, hy j]

end KAM.EffectiveStability

end
