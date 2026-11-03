/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.TorusRoute.Data

/-!
# The complexified Hamiltonian `c.H ∘ Ψ_ℂ` of a certified torus (track B, B5-ROUTE, item 3)

* `RouteChecks`: the finite checks on the radii (projection constant `κc`, `n (κc + disp/δ) < 1`,
  action radius `ρJ ≤ (1 - n κ) μ/2`).
* `routeDomain`: `T_{δφ} × {‖J‖ < ρJ}`.
* `routeChart_mem_ball`: `Ψ_ℂ` maps the domain into `ball (K∞ θ) (μ/2) ⊆ D`.
* `routeHam_differentiableOn`: `c.H ∘ Ψ_ℂ` is holomorphic on the domain.
* `routeHam_sub_le`: `‖c.H (Ψ_ℂ w) - E₀‖ ≤ M μ / 2` on the domain, by the mean value theorem on
  the convex ball `ball (K∞ θ) (μ/2) ⊆ D` with `‖DH‖ ≤ M` and `c.H (K∞ θ) = E₀`.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator

namespace KAM.EffectiveStability

open KAM KAM.Torus KAM.Certificate KAM.Application CertArith Metric

variable {n : ℕ} {α : Type} [CertArith α] {c : TorusCertificate n α} {ωstar : Fin n → ℝ}
  {Kinf : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {sinf : ℝ}

/-- The finite checks on the radii of the complexified chart: `κ = κc + disp/δ` with
`n κ < 1`, and an action radius `ρJ ≤ (1 - n κ) μ / 2`. -/
structure RouteChecks (c : TorusCertificate n α) (κc δ δφ ρJ : ℝ) : Prop where
  hδ : 0 < δ
  hδφ : 0 < δφ
  hδφρ : δφ + δ ≤ (c.params.rhoInf : ℝ)
  hκc : ∀ θ ∈ complexStrip n δφ, ‖fderiv ℂ (fun θ => (c.K θ).1 - θ) θ‖ ≤ κc
  hκ : (n : ℝ) * (κc + (c.params.disp : ℝ) / δ) < 1
  hρJ0 : 0 < ρJ
  hρJ : ρJ ≤ (1 - n * (κc + (c.params.disp : ℝ) / δ)) * ((c.params.μ : ℝ) / 2)

/-- The domain `T_{δφ} × {‖J‖ < ρJ}` of the complexified chart. -/
def routeDomain (n : ℕ) (δφ ρJ : ℝ) : Set ((Fin n → ℂ) × (Fin n → ℂ)) :=
  {w | w.1 ∈ complexStrip n δφ ∧ ‖w.2‖ < ρJ}

theorem isOpen_routeDomain (δφ ρJ : ℝ) : IsOpen (routeDomain n δφ ρJ) :=
  ((isOpen_complexStrip n δφ).preimage continuous_fst).inter
    (isOpen_lt continuous_snd.norm continuous_const)

variable {κc δ δφ ρJ : ℝ}

theorem RouteChecks.routeKappa_nonneg (hG : G1Hyps c ωstar) (hT : CertifiedTorusAt c ωstar Kinf sinf)
    (h : RouteChecks c κc δ δφ ρJ) : 0 ≤ κc + (c.params.disp : ℝ) / δ := by
  have h0 : (0 : Fin n → ℂ) ∈ complexStrip n δφ := fun i => by simpa using h.hδφ
  have h1 : 0 ≤ κc := (norm_nonneg _).trans (h.hκc 0 h0)
  have h2 : 0 ≤ (c.params.disp : ℝ) :=
    (norm_nonneg _).trans (hT.2.2.2.2.2.2.2.2.2.1 0 (fun i => by simpa using hG.hρinf))
  have := h.hδ
  positivity

theorem RouteChecks.jac_le (hG : G1Hyps c ωstar) (hT : CertifiedTorusAt c ωstar Kinf sinf)
    (h : RouteChecks c κc δ δφ ρJ) {θ : Fin n → ℂ} (hθ : θ ∈ complexStrip n δφ) (i j : Fin n) :
    ‖torusCxJac Kinf θ i j - (1 : Matrix (Fin n) (Fin n) ℂ) i j‖ ≤
      κc + (c.params.disp : ℝ) / δ := by
  have hθρ : θ ∈ complexStrip n (c.params.rhoInf : ℝ) := fun i => by
    have := hθ i; have := h.hδφρ; have := h.hδ; linarith
  have hK1 : DifferentiableAt ℂ (fun θ => (Kinf θ).1) θ :=
    (hT.2.2.1.differentiableAt ((isOpen_complexStrip n _).mem_nhds hθρ)).fst
  exact torusCxJac_sub_one_le hK1 (certifiedTorus_angle_fderiv_le hG hT h.hδ h.hδφρ h.hκc hθ) i j

theorem RouteChecks.chart_differentiableOn (hG : G1Hyps c ωstar)
    (hT : CertifiedTorusAt c ωstar Kinf sinf) (h : RouteChecks c κc δ δφ ρJ) :
    DifferentiableOn ℂ (torusCxChart Kinf) {w | w.1 ∈ complexStrip n δφ} :=
  torusCxChart_differentiableOn (h.routeKappa_nonneg hG hT) h.hκ (by linarith [h.hδφρ, h.hδ])
    hT.2.2.1 (fun _ hθ => h.jac_le hG hT hθ)

theorem RouteChecks.chart_mem_ball (hG : G1Hyps c ωstar) (hT : CertifiedTorusAt c ωstar Kinf sinf)
    (h : RouteChecks c κc δ δφ ρJ) {w : (Fin n → ℂ) × (Fin n → ℂ)} (hw : w ∈ routeDomain n δφ ρJ) :
    torusCxChart Kinf w ∈ ball (Kinf w.1) ((c.params.μ : ℝ) / 2) := by
  obtain ⟨hθ, hJ⟩ := hw
  have hκ0 := h.routeKappa_nonneg hG hT
  have h1 : 0 < 1 - n * (κc + (c.params.disp : ℝ) / δ) := by linarith [h.hκ]
  have h2 := norm_torusCxChart_sub_le (K := Kinf) hκ0 h.hκ (θ := w.1)
    (fun i j => h.jac_le hG hT hθ i j) w.2
  rw [mem_ball, dist_eq_norm, Prod.norm_def]
  refine max_lt ?_ ?_
  · simp [torusCxChart, hG.hμ]
  · refine lt_of_le_of_lt h2 ?_
    rw [div_lt_iff₀ h1]
    have := h.hρJ
    nlinarith

theorem RouteChecks.chart_mem_D (hG : G1Hyps c ωstar) (hT : CertifiedTorusAt c ωstar Kinf sinf)
    (h : RouteChecks c κc δ δφ ρJ) {w : (Fin n → ℂ) × (Fin n → ℂ)} (hw : w ∈ routeDomain n δφ ρJ) :
    torusCxChart Kinf w ∈ c.D := by
  have hθρ : w.1 ∈ complexStrip n (c.params.rhoInf : ℝ) := fun i => by
    have := hw.1 i; have := h.hδφρ; have := h.hδ; linarith
  exact hT.2.2.2.2.2.2.2.1 w.1 hθρ (h.chart_mem_ball hG hT hw)

theorem RouteChecks.ham_differentiableOn (hG : G1Hyps c ωstar)
    (hT : CertifiedTorusAt c ωstar Kinf sinf) (h : RouteChecks c κc δ δφ ρJ) :
    DifferentiableOn ℂ (fun w => c.H (torusCxChart Kinf w)) (routeDomain n δφ ρJ) :=
  hG.hholo.comp ((h.chart_differentiableOn hG hT).mono fun _ hw => hw.1)
    (fun _ hw => h.chart_mem_D hG hT hw)

/-- **The sup bound `M` on the complexified Hamiltonian**, derived from the certificate: on the
domain, `‖c.H (Ψ_ℂ w) - E₀‖ ≤ M μ / 2`. -/
theorem RouteChecks.ham_sub_le (hG : G1Hyps c ωstar) (hT : CertifiedTorusAt c ωstar Kinf sinf)
    (h : RouteChecks c κc δ δφ ρJ) {w : (Fin n → ℂ) × (Fin n → ℂ)} (hw : w ∈ routeDomain n δφ ρJ) :
    ‖c.H (torusCxChart Kinf w) - ((c.params.E0 : ℝ) : ℂ)‖ ≤
      (c.params.M : ℝ) * ((c.params.μ : ℝ) / 2) := by
  have hθρ : w.1 ∈ complexStrip n (c.params.rhoInf : ℝ) := fun i => by
    have := hw.1 i; have := h.hδφρ; have := h.hδ; linarith
  have hball : ball (Kinf w.1) ((c.params.μ : ℝ) / 2) ⊆ c.D := hT.2.2.2.2.2.2.2.1 w.1 hθρ
  have hE : c.H (Kinf w.1) = ((c.params.E0 : ℝ) : ℂ) := hT.2.2.2.2.2.2.1 w.1 hθρ
  have hmem : Kinf w.1 ∈ ball (Kinf w.1) ((c.params.μ : ℝ) / 2) := mem_ball_self (by
    have := hG.hμ; positivity)
  have := (convex_ball (Kinf w.1) ((c.params.μ : ℝ) / 2)).norm_image_sub_le_of_norm_fderiv_le
    (f := c.H) (C := (c.params.M : ℝ))
    (fun z hz => hG.hholo.differentiableAt (hG.hopen.mem_nhds (hball hz)))
    (fun z hz => (hG.hbd z (hball hz)).1) hmem (h.chart_mem_ball hG hT hw)
  rw [hE] at this
  refine this.trans ?_
  have hM := hG.hM
  have h3 := (mem_ball.mp (h.chart_mem_ball hG hT hw))
  rw [dist_eq_norm] at h3
  exact mul_le_mul_of_nonneg_left h3.le hM.le

end KAM.EffectiveStability

end
