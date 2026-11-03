/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.Cauchy
public import KAM.Strip.RealRestriction

/-!
# Strip Cauchy estimates at complex points (track B, package B5-ROUTE)

* `norm_fderiv_le_of_strip_bound_cx`: for `F` holomorphic on `T_ρ` and bounded by `d` there,
  `‖DF(θ)‖ ≤ d/δ` at every `θ ∈ T_{ρ-δ}` (B5-LAG's real-point estimate at complex points).
* `norm_fderiv_angle_le_cx`: `‖D(K^θ - id)(θ)‖ ≤ κc + disp/δ` on `T_{ρ-δ}`, from a bound
  `κc` on the derivative of a reference embedding and the displacement `disp`.
-/

@[expose] public noncomputable section

namespace KAM.EffectiveStability

open KAM

variable {n : ℕ} {ρ δ : ℝ}

theorem norm_fderiv_le_of_strip_bound_cx {F : (Fin n → ℂ) → (Fin n → ℂ)} {d : ℝ}
    (hF : DifferentiableOn ℂ F (complexStrip n ρ)) (hδ : 0 < δ) {θ : Fin n → ℂ}
    (hθ : θ ∈ complexStrip n (ρ - δ)) (hd : ∀ θ ∈ complexStrip n ρ, ‖F θ‖ ≤ d) :
    ‖fderiv ℂ F θ‖ ≤ d / δ := by
  have hθρ : θ ∈ complexStrip n ρ := fun i => by have := hθ i; linarith
  have hd0 : 0 ≤ d := (norm_nonneg _).trans (hd _ hθρ)
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun e => ?_
  rcases eq_or_ne e 0 with rfl | he
  · simp
  have hte : 0 < ‖e‖ := norm_pos_iff.mpr he
  have hFd : DifferentiableAt ℂ F θ :=
    hF.differentiableAt ((isOpen_complexStrip n ρ).mem_nhds hθρ)
  have hmem : ∀ ζ : ℂ, ‖ζ‖ ≤ δ / ‖e‖ → θ + ζ • e ∈ complexStrip n ρ := by
    intro ζ hζ i
    have h1 : ‖ζ‖ * ‖e‖ ≤ δ := by
      calc ‖ζ‖ * ‖e‖ ≤ δ / ‖e‖ * ‖e‖ := by gcongr
        _ = δ := by field_simp
    have h2 : ‖ζ * e i‖ ≤ ‖ζ‖ * ‖e‖ := by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (norm_le_pi_norm e i) (norm_nonneg _)
    have h3 : |((θ + ζ • e) i).im| ≤ |(θ i).im| + ‖ζ * e i‖ := by
      have : ((θ + ζ • e) i).im = (θ i).im + (ζ * e i).im := by simp
      rw [this]
      exact (abs_add_le _ _).trans (add_le_add le_rfl (Complex.abs_im_le_norm _))
    have h4 := hθ i
    linarith
  have hcoord : ∀ i, ‖fderiv ℂ F θ e i‖ ≤ d * ‖e‖ / δ := by
    intro i
    have hfi : DifferentiableOn ℂ (fun θ => F θ i) (complexStrip n ρ) :=
      (differentiableOn_pi.mp hF) i
    have hder : fderiv ℂ (fun θ => F θ i) θ e = fderiv ℂ F θ e i := by
      rw [(hasFDerivAt_pi'.mp hFd.hasFDerivAt i).fderiv]
      rfl
    have := norm_fderiv_le_of_closedDisc (isOpen_complexStrip n ρ) hfi (z := θ)
      e (δ := δ / ‖e‖) (M := d) (by positivity) hmem
      (fun ζ hζ => (norm_le_pi_norm _ i).trans (hd _ (hmem ζ hζ)))
    rw [hder] at this
    calc _ ≤ d / (δ / ‖e‖) := this
      _ = d * ‖e‖ / δ := by field_simp
  have : ‖fderiv ℂ F θ e‖ ≤ d * ‖e‖ / δ :=
    (pi_norm_le_iff_of_nonneg (by positivity)).2 hcoord
  calc _ ≤ d * ‖e‖ / δ := this
    _ = d / δ * ‖e‖ := by ring

variable {K Kc : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}

theorem norm_fderiv_angle_le_cx (hK : DifferentiableOn ℂ K (complexStrip n ρ))
    (hKc : DifferentiableOn ℂ Kc (complexStrip n ρ)) (hδ : 0 < δ) {κc disp : ℝ}
    {θ : Fin n → ℂ} (hθ : θ ∈ complexStrip n (ρ - δ))
    (hκ : ‖fderiv ℂ (fun θ => (Kc θ).1 - θ) θ‖ ≤ κc)
    (hdisp : ∀ θ ∈ complexStrip n ρ, ‖K θ - Kc θ‖ ≤ disp) :
    ‖fderiv ℂ (fun θ => (K θ).1 - θ) θ‖ ≤ κc + disp / δ := by
  have hθρ : θ ∈ complexStrip n ρ := fun i => by have := hθ i; linarith
  have hnb := (isOpen_complexStrip n ρ).mem_nhds hθρ
  have hKd : DifferentiableAt ℂ K θ := hK.differentiableAt hnb
  have hKcd : DifferentiableAt ℂ Kc θ := hKc.differentiableAt hnb
  have hFd : DifferentiableAt ℂ (fun θ => (K θ).1 - θ) θ := hKd.fst.sub differentiableAt_id
  have hGd : DifferentiableAt ℂ (fun θ => (Kc θ).1 - θ) θ := hKcd.fst.sub differentiableAt_id
  have hdiff : DifferentiableOn ℂ (fun θ => ((K θ).1 - θ) - ((Kc θ).1 - θ))
      (complexStrip n ρ) := by
    intro θ' hθ'
    have h1 := hK.differentiableAt ((isOpen_complexStrip n ρ).mem_nhds hθ')
    have h2 := hKc.differentiableAt ((isOpen_complexStrip n ρ).mem_nhds hθ')
    exact ((h1.fst.sub differentiableAt_id).sub
      (h2.fst.sub differentiableAt_id)).differentiableWithinAt
  have hcau := norm_fderiv_le_of_strip_bound_cx hdiff hδ hθ (d := disp) (fun θ' hθ' => by
    have : ((K θ').1 - θ') - ((Kc θ').1 - θ') = (K θ' - Kc θ').1 := by simp
    rw [this]
    exact (norm_fst_le _).trans (hdisp θ' hθ'))
  have hsplit : fderiv ℂ (fun θ => (K θ).1 - θ) θ = fderiv ℂ (fun θ => (Kc θ).1 - θ) θ +
      fderiv ℂ (fun θ => ((K θ).1 - θ) - ((Kc θ).1 - θ)) θ := by
    rw [fderiv_fun_sub hFd hGd]
    abel
  rw [hsplit]
  exact (norm_add_le _ _).trans (add_le_add hκ hcau)

end KAM.EffectiveStability

end
