/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Strip.Cauchy
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Cauchy estimates on Banach domains, and continuity of derivatives

Blueprint-W `bpW:w1:cauchy` and `bpW:w1:deriv-continuous` (package W1-ANALYTIC). This is
source-faithful infrastructure used by several nodes; the dependency graph is still being built.

For `f` holomorphic on a ball `B(v, r)` of a complex normed space with values in a complex Banach
space and `‖f‖ ≤ M` there, `‖Df(v)‖ ≤ M / r` (`KAM.Wave.norm_fderiv_le_div_of_ball`); on an open set
with a margin `δ` the derivative is bounded by `M / δ` and `f` is `(M/δ)`-Lipschitz on convex sets
with margin `δ` (`KAM.Wave.norm_fderiv_le_div_of_ball_subset`, `KAM.Wave.lipschitz_of_margin`). The
derivative of a holomorphic map is locally Lipschitz with the constant `2 B ρ⁻²`
(`KAM.Wave.norm_fderiv_sub_le_holoMargin`), hence continuous
(`KAM.Wave.continuousOn_fderiv_of_holomorphic`).
-/

@[expose] public section

open Metric Set

namespace KAM.Wave

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Cauchy estimate on an open ball (blueprint `bpW:w1:cauchy`, first assertion). -/
theorem norm_fderiv_le_div_of_ball {f : E → F} {v : E} {r M : ℝ} (hr : 0 < r) (hM : 0 ≤ M)
    (hf : DifferentiableOn ℂ f (ball v r)) (hbd : ∀ z ∈ ball v r, ‖f z‖ ≤ M) :
    ‖fderiv ℂ f v‖ ≤ M / r := by
  have key : ∀ r' : ℝ, 0 < r' → r' < r → ‖fderiv ℂ f v‖ ≤ M / r' := fun r' h0 h1 =>
    KAM.norm_fderiv_le_of_closedBall_bound isOpen_ball hf h0
      (closedBall_subset_ball h1) (fun w hw => hbd w (closedBall_subset_ball h1 hw))
  by_contra hlt
  push Not at hlt
  have hD : 0 < ‖fderiv ℂ f v‖ := lt_of_le_of_lt (div_nonneg hM hr.le) hlt
  have h1 : M < ‖fderiv ℂ f v‖ * r := by rwa [div_lt_iff₀ hr] at hlt
  obtain ⟨r', hr'1, hr'2⟩ := exists_between (show M / ‖fderiv ℂ f v‖ < r by
    rw [div_lt_iff₀ hD]; linarith)
  have hr'0 : 0 < r' := lt_of_le_of_lt (div_nonneg hM hD.le) hr'1
  have := key r' hr'0 hr'2
  rw [le_div_iff₀ hr'0] at this
  rw [div_lt_iff₀ hD] at hr'1
  linarith

/-- Cauchy estimate with a margin on an open set (blueprint `bpW:w1:cauchy`, second assertion). -/
theorem norm_fderiv_le_div_of_ball_subset {f : E → F} {V : Set E} {w : E} {δ M : ℝ}
    (hδ : 0 < δ) (hM : 0 ≤ M) (hf : DifferentiableOn ℂ f V) (hbd : ∀ z ∈ V, ‖f z‖ ≤ M)
    (hw : ball w δ ⊆ V) : ‖fderiv ℂ f w‖ ≤ M / δ :=
  norm_fderiv_le_div_of_ball hδ hM (hf.mono hw) (fun z hz => hbd z (hw hz))

/-- Lipschitz estimate on convex sets with a margin (blueprint `bpW:w1:cauchy`, third assertion). -/
theorem lipschitz_of_margin {f : E → F} {V : Set E} {δ M : ℝ} (hδ : 0 < δ) (hM : 0 ≤ M)
    (hV : IsOpen V) (hf : DifferentiableOn ℂ f V) (hbd : ∀ z ∈ V, ‖f z‖ ≤ M)
    {C : Set E} (hC : Convex ℝ C) (hCV : ∀ z ∈ C, ball z δ ⊆ V) :
    ∀ x ∈ C, ∀ y ∈ C, ‖f x - f y‖ ≤ M / δ * ‖x - y‖ := by
  intro x hx y hy
  refine Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (f := f) (C := M / δ) ?_ ?_ hC hy hx
  · intro z hz
    exact ((hf.differentiableAt (hV.mem_nhds (hCV z hz (mem_ball_self hδ)))).restrictScalars ℝ)
  · intro z hz
    have hd := hf.differentiableAt (hV.mem_nhds (hCV z hz (mem_ball_self hδ)))
    rw [hd.fderiv_restrictScalars ℝ]
    have h := norm_fderiv_le_div_of_ball_subset hδ hM hf hbd (hCV z hz)
    exact ContinuousLinearMap.opNorm_le_bound _ (div_nonneg hM hδ.le) fun x =>
      ((fderiv ℂ f z).le_opNorm x).trans (mul_le_mul_of_nonneg_right h (norm_nonneg x))


/-- Local Lipschitz bound for the derivative of a holomorphic map (blueprint
`bpW:w1:deriv-continuous`, quantitative part). -/
theorem norm_fderiv_sub_le_holoMargin {f : E → F} {U : Set E} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U)
    {w₀ : E} {ρ B : ℝ} (hρ : 0 < ρ) (hB : 0 ≤ B) (hsub : ball w₀ (2 * ρ) ⊆ U)
    (hbd : ∀ z ∈ ball w₀ (2 * ρ), ‖f z‖ ≤ B) {w w' : E}
    (hw : w ∈ ball w₀ (ρ / 2)) (hw' : w' ∈ ball w₀ (ρ / 2)) :
    ‖fderiv ℂ f w - fderiv ℂ f w'‖ ≤ 2 * B * (ρ ^ 2)⁻¹ * ‖w - w'‖ := by
  have hV : IsOpen (ball w₀ (2 * ρ)) := isOpen_ball
  have hfV : DifferentiableOn ℂ f (ball w₀ (2 * ρ)) := hf.mono hsub
  have hlip := lipschitz_of_margin hρ hB hV hfV hbd (convex_ball w₀ ρ)
    (fun z hz => by
      intro y hy
      rw [mem_ball, dist_eq_norm] at hy
      rw [mem_ball, dist_eq_norm] at hz
      rw [mem_ball, dist_eq_norm]
      have := norm_add_le (y - z) (z - w₀)
      simp only [sub_add_sub_cancel] at this
      linarith)
  have dU : ∀ x ∈ ball w₀ (ρ / 2), DifferentiableAt ℂ f x := fun x hx =>
    hf.differentiableAt (hU.mem_nhds (hsub (ball_subset_ball (by linarith) hx)))
  have hR : 0 < ρ / 2 := by positivity
  have hnn : 0 ≤ 2 * B * (ρ ^ 2)⁻¹ * ‖w - w'‖ := by positivity
  apply ContinuousLinearMap.opNorm_le_of_unit_norm hnn
  intro u hu
  have hline : ∀ x : E, ∀ ζ : ℂ, HasDerivAt (fun ζ : ℂ => x + ζ • u) u ζ := fun x ζ => by
    simpa using ((hasDerivAt_id ζ).smul_const u).const_add x
  have hmem : ∀ x ∈ ball w₀ (ρ / 2), ∀ ζ ∈ closedBall (0 : ℂ) (ρ / 2),
      x + ζ • u ∈ ball w₀ ρ := by
    intro x hx ζ hζ
    rw [mem_ball_iff_norm] at hx ⊢
    rw [mem_closedBall_zero_iff] at hζ
    have : ‖x + ζ • u - w₀‖ ≤ ‖x - w₀‖ + ‖ζ • u‖ := by
      simpa [add_sub_right_comm] using norm_add_le (x - w₀) (ζ • u)
    rw [norm_smul, hu, mul_one] at this
    linarith
  have hdiffline : ∀ x ∈ ball w₀ (ρ / 2), DifferentiableOn ℂ (fun ζ : ℂ => f (x + ζ • u))
      (closedBall 0 (ρ / 2)) := fun x hx =>
    hf.comp (fun ζ _ => (hline x ζ).differentiableAt.differentiableWithinAt)
      (fun ζ hζ => hsub (ball_subset_ball (by linarith) (hmem x hx ζ hζ)))
  have hd : DiffContOnCl ℂ (fun ζ : ℂ => f (w + ζ • u) - f (w' + ζ • u)) (ball 0 (ρ / 2)) :=
    ((hdiffline w hw).sub (hdiffline w' hw')).diffContOnCl_ball (Subset.refl _)
  have hsph : ∀ ζ ∈ sphere (0 : ℂ) (ρ / 2),
      ‖f (w + ζ • u) - f (w' + ζ • u)‖ ≤ B / ρ * ‖w - w'‖ := by
    intro ζ hζ
    have h1 := hlip (w + ζ • u) (hmem w hw ζ (sphere_subset_closedBall hζ))
      (w' + ζ • u) (hmem w' hw' ζ (sphere_subset_closedBall hζ))
    simpa using h1
  have hb := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hR hd hsph
  have hder : ∀ x ∈ ball w₀ (ρ / 2),
      HasDerivAt (fun ζ : ℂ => f (x + ζ • u)) (fderiv ℂ f x u) 0 := fun x hx => by
    have hdf : HasFDerivAt f (fderiv ℂ f x) (x + (0 : ℂ) • u) := by
      simpa using (dU x hx).hasFDerivAt
    exact hdf.comp_hasDerivAt 0 (hline x 0)
  have hderiv : deriv (fun ζ : ℂ => f (w + ζ • u) - f (w' + ζ • u)) 0 =
      fderiv ℂ f w u - fderiv ℂ f w' u := ((hder w hw).sub (hder w' hw')).deriv
  rw [hderiv] at hb
  calc ‖(fderiv ℂ f w - fderiv ℂ f w') u‖ = ‖fderiv ℂ f w u - fderiv ℂ f w' u‖ := rfl
    _ ≤ B / ρ * ‖w - w'‖ / (ρ / 2) := hb
    _ = 2 * B * (ρ ^ 2)⁻¹ * ‖w - w'‖ := by field_simp

/-- Derivatives of holomorphic maps are continuous (blueprint `bpW:w1:deriv-continuous`). -/
theorem continuousOn_fderiv_of_holomorphic {f : E → F} {U : Set E} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) : ContinuousOn (fderiv ℂ f) U := by
  intro w₀ hw₀
  have hc : ContinuousAt f w₀ := (hf.differentiableAt (hU.mem_nhds hw₀)).continuousAt
  have hev : ∀ᶠ z in nhds w₀, z ∈ U ∧ ‖f z‖ ≤ ‖f w₀‖ + 1 := by
    have h1 : ∀ᶠ z in nhds w₀, z ∈ U := hU.mem_nhds hw₀
    exact h1.and (hc.norm.eventually (eventually_le_nhds (lt_add_one ‖f w₀‖)))
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hev
  set ρ := ε / 2 with hρdef
  have hρ : 0 < ρ := by positivity
  have hB : 0 ≤ ‖f w₀‖ + 1 := by positivity
  have h2ρ : ball w₀ (2 * ρ) ⊆ ball w₀ ε := ball_subset_ball (le_of_eq (by rw [hρdef]; ring))
  have hsub : ball w₀ (2 * ρ) ⊆ U := fun z hz => (hball (h2ρ hz)).1
  have hbd : ∀ z ∈ ball w₀ (2 * ρ), ‖f z‖ ≤ ‖f w₀‖ + 1 := fun z hz => (hball (h2ρ hz)).2
  refine ContinuousAt.continuousWithinAt ?_
  rw [Metric.continuousAt_iff]
  intro η hη
  set K := 2 * (‖f w₀‖ + 1) * (ρ ^ 2)⁻¹ with hK
  have hK0 : 0 ≤ K := by positivity
  refine ⟨min (ρ / 2) (η / (K + 1)), by positivity, fun {w} hw => ?_⟩
  rw [dist_eq_norm] at hw ⊢
  have hw1 : w ∈ ball w₀ (ρ / 2) := by
    rw [mem_ball, dist_eq_norm]; exact lt_of_lt_of_le hw (min_le_left _ _)
  have hw0 : w₀ ∈ ball w₀ (ρ / 2) := mem_ball_self (by positivity)
  have := norm_fderiv_sub_le_holoMargin hU hf hρ hB hsub hbd hw1 hw0
  refine this.trans_lt ?_
  have hw2 : ‖w - w₀‖ < η / (K + 1) := lt_of_lt_of_le hw (min_le_right _ _)
  rw [lt_div_iff₀ (by positivity)] at hw2
  calc K * ‖w - w₀‖ ≤ (K + 1) * ‖w - w₀‖ := by gcongr; linarith
    _ < η := by linarith

end KAM.Wave
