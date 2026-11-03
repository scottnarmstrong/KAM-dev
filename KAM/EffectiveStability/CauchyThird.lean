/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.Cauchy
public import KAM.Strip.AnalyticTaylor
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars

/-!
# Third-derivative Cauchy estimate on a ball (track B, package B5-ROUTE)

* `norm_fderiv_ball_le`: one Cauchy step. A map holomorphic on `ball z₀ r₁` and bounded by `M`
  there has `‖fderiv ℂ f w e‖ ≤ M ‖e‖ / (r₁ - r₂)` on the smaller ball `ball z₀ r₂`.
* `norm_fderiv3_ball_le`: iterating three times with radii `r, 2r/3, r/3`, a holomorphic `f` with
  `‖f - a‖ ≤ M` on `ball z₀ r` has `‖D³f(z₀)(h₁, h₂, h₃)‖ ≤ 64 M / r³ · ‖h₁‖ ‖h₂‖ ‖h₃‖`.
* `abs_fderiv3_realPart_le`: the same bound for the real slice `y ↦ Re f (ι₂ y)`.
-/

@[expose] public noncomputable section

namespace KAM.EffectiveStability

open KAM Metric Set

section Ball

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

omit [FiniteDimensional ℂ E] in
/-- One Cauchy step on nested balls. -/
theorem norm_fderiv_ball_le {f : E → ℂ} {z₀ : E} {r₁ r₂ M : ℝ}
    (hf : DifferentiableOn ℂ f (ball z₀ r₁)) (hM : ∀ w ∈ ball z₀ r₁, ‖f w‖ ≤ M)
    (hr : r₂ < r₁) {w : E} (hw : w ∈ ball z₀ r₂) (e : E) :
    ‖fderiv ℂ f w e‖ ≤ M * ‖e‖ / (r₁ - r₂) := by
  have hd : 0 < r₁ - r₂ := sub_pos.2 hr
  rcases eq_or_ne e 0 with rfl | he
  · simp
  have hte : 0 < ‖e‖ := norm_pos_iff.mpr he
  have hmem : ∀ ζ : ℂ, ‖ζ‖ ≤ (r₁ - r₂) / ‖e‖ → w + ζ • e ∈ ball z₀ r₁ := by
    intro ζ hζ
    have h1 : ‖ζ‖ * ‖e‖ ≤ r₁ - r₂ := by
      calc ‖ζ‖ * ‖e‖ ≤ (r₁ - r₂) / ‖e‖ * ‖e‖ := by gcongr
        _ = r₁ - r₂ := by field_simp
    have h2 : dist w z₀ < r₂ := mem_ball.mp hw
    rw [dist_eq_norm] at h2
    rw [mem_ball, dist_eq_norm]
    calc ‖w + ζ • e - z₀‖ = ‖(w - z₀) + ζ • e‖ := by congr 1; abel
      _ ≤ ‖w - z₀‖ + ‖ζ • e‖ := norm_add_le _ _
      _ < r₂ + (r₁ - r₂) := by rw [norm_smul]; linarith
      _ = r₁ := by ring
  have := norm_fderiv_le_of_closedDisc (isOpen_ball (x := z₀) (ε := r₁)) hf e (z := w)
    (δ := (r₁ - r₂) / ‖e‖) (M := M) (by positivity) hmem (fun ζ hζ => hM _ (hmem ζ hζ))
  calc _ ≤ M / ((r₁ - r₂) / ‖e‖) := this
    _ = M * ‖e‖ / (r₁ - r₂) := by field_simp

/-- The directional derivative of a holomorphic map is holomorphic. -/
theorem differentiableOn_fderivApply_cx {f : E → ℂ} {U : Set E} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) (e : E) : DifferentiableOn ℂ (fun w => fderiv ℂ f w e) U := by
  have h1 : DifferentiableOn ℂ (fderiv ℂ f) U :=
    ((KAM.analyticOnNhd_of_differentiableOn hU hf).fderiv_of_isOpen hU).differentiableOn
  exact (ContinuousLinearMap.apply ℂ ℂ e).differentiable.comp_differentiableOn h1

theorem fderiv_fderiv_apply_eq {f : E → ℂ} {U : Set E} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) {w : E} (hw : w ∈ U) (e h : E) :
    fderiv ℂ (fun w => fderiv ℂ f w e) w h = fderiv ℂ (fderiv ℂ f) w h e := by
  have h1 : DifferentiableAt ℂ (fderiv ℂ f) w :=
    (((KAM.analyticOnNhd_of_differentiableOn hU hf).fderiv_of_isOpen hU).differentiableOn
      ).differentiableAt (hU.mem_nhds hw)
  have := (ContinuousLinearMap.apply ℂ ℂ e).hasFDerivAt.comp w h1.hasFDerivAt
  rw [show (fun w => fderiv ℂ f w e) = (ContinuousLinearMap.apply ℂ ℂ e) ∘ fderiv ℂ f from rfl,
    this.fderiv]
  rfl

omit [FiniteDimensional ℂ E] in
/-- Evaluating a differentiable operator-valued map on a fixed vector commutes with `fderiv`. -/
theorem fderiv_apply_fixed {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] {k : E → E →L[ℂ] F}
    {w : E} (hk : DifferentiableAt ℂ k w) (e h : E) :
    fderiv ℂ (fun w => k w e) w h = fderiv ℂ k w h e := by
  have := (ContinuousLinearMap.apply ℂ F e).hasFDerivAt.comp w hk.hasFDerivAt
  rw [show (fun w => k w e) = (ContinuousLinearMap.apply ℂ F e) ∘ k from rfl, this.fderiv]
  rfl

/-- Third-derivative Cauchy estimate on a ball, for a map within `M` of a constant `a`:
`‖D³f(z₀)(h₁,h₂,h₃)‖ ≤ 64 M / r³ · ‖h₁‖‖h₂‖‖h₃‖`. -/
theorem norm_fderiv3_ball_le {f : E → ℂ} {z₀ : E} {r M : ℝ} (a : ℂ) (hr : 0 < r)
    (hf : DifferentiableOn ℂ f (ball z₀ r)) (hM : ∀ w ∈ ball z₀ r, ‖f w - a‖ ≤ M)
    (h₁ h₂ h₃ : E) :
    ‖fderiv ℂ (fderiv ℂ (fderiv ℂ f)) z₀ h₁ h₂ h₃‖ ≤ 64 * M / r ^ 3 * (‖h₁‖ * ‖h₂‖ * ‖h₃‖) := by
  set g : E → ℂ := fun w => f w - a with hg
  have hgd : DifferentiableOn ℂ g (ball z₀ r) := hf.sub_const a
  have hgf : fderiv ℂ g = fderiv ℂ f := funext fun w => fderiv_sub_const a
  rw [← hgf]
  clear hgf hf
  set δ := r / 4 with hδ
  have hδ0 : 0 < δ := by positivity
  have hr4 : r = 4 * δ := by rw [hδ]; ring
  -- analytic facts
  have hA1 : AnalyticOnNhd ℂ (fderiv ℂ g) (ball z₀ r) := 
    (KAM.analyticOnNhd_of_differentiableOn isOpen_ball hgd).fderiv_of_isOpen isOpen_ball
  have hA2 : AnalyticOnNhd ℂ (fderiv ℂ (fderiv ℂ g)) (ball z₀ r) := 
    hA1.fderiv_of_isOpen isOpen_ball
  have hd1 : ∀ w ∈ ball z₀ r, DifferentiableAt ℂ (fderiv ℂ g) w := fun w hw =>
    hA1.differentiableOn.differentiableAt (isOpen_ball.mem_nhds hw)
  have hd2 : ∀ w ∈ ball z₀ r, DifferentiableAt ℂ (fderiv ℂ (fderiv ℂ g)) w := fun w hw =>
    hA2.differentiableOn.differentiableAt (isOpen_ball.mem_nhds hw)
  -- first level
  set g1 : E → ℂ := fun w => fderiv ℂ g w h₃ with hg1
  have hg1d : DifferentiableOn ℂ g1 (ball z₀ r) :=
    differentiableOn_fderivApply_cx isOpen_ball hgd h₃
  have hg1M : ∀ w ∈ ball z₀ (3 * δ), ‖g1 w‖ ≤ M * ‖h₃‖ / δ := fun w hw => by
    have := norm_fderiv_ball_le hgd (fun w hw => hM w hw) (r₂ := 3 * δ) (by linarith) hw h₃
    convert this using 2; rw [hr4]; ring
  have hsub1 : ball z₀ (3 * δ) ⊆ ball z₀ r := ball_subset_ball (by linarith)
  -- second level
  set g2 : E → ℂ := fun w => fderiv ℂ g1 w h₂ with hg2
  have hg2d : DifferentiableOn ℂ g2 (ball z₀ (3 * δ)) :=
    differentiableOn_fderivApply_cx isOpen_ball (hg1d.mono hsub1) h₂
  have hg2M : ∀ w ∈ ball z₀ (2 * δ), ‖g2 w‖ ≤ M * ‖h₃‖ / δ * ‖h₂‖ / δ := fun w hw => by
    have := norm_fderiv_ball_le (hg1d.mono hsub1) hg1M (r₂ := 2 * δ) (by linarith) hw h₂
    convert this using 2; ring
  have hsub2 : ball z₀ (2 * δ) ⊆ ball z₀ (3 * δ) := ball_subset_ball (by linarith)
  -- third level
  have hz : z₀ ∈ ball z₀ δ := mem_ball_self hδ0
  have h3 := norm_fderiv_ball_le (hg2d.mono hsub2) hg2M (r₂ := δ) (by linarith) hz h₁
  -- identify `fderiv g2 z₀ h₁`
  have e1 : ∀ w ∈ ball z₀ r, ∀ h, fderiv ℂ g1 w h = fderiv ℂ (fderiv ℂ g) w h h₃ := fun w hw h =>
    fderiv_apply_fixed (hd1 w hw) h₃ h
  have e2 : g2 =ᶠ[nhds z₀] fun w => fderiv ℂ (fderiv ℂ g) w h₂ h₃ := by
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hr)] with w hw using e1 w hw h₂
  have hz0 : z₀ ∈ ball z₀ r := mem_ball_self hr
  have hk' : DifferentiableAt ℂ (fun w => fderiv ℂ (fderiv ℂ g) w h₂) z₀ :=
    (hd2 z₀ hz0).clm_apply (differentiableAt_const h₂)
  have e3 : fderiv ℂ g2 z₀ h₁ = fderiv ℂ (fderiv ℂ (fderiv ℂ g)) z₀ h₁ h₂ h₃ := by
    rw [e2.fderiv_eq, fderiv_apply_fixed hk' h₃ h₁, fderiv_apply_fixed (hd2 z₀ hz0) h₂ h₁]
  rw [← e3]
  refine h3.trans (le_of_eq ?_)
  rw [hr4]
  field_simp
  ring

end Ball

section Real

/-- The third iterated derivative in `fderiv` form. -/
theorem iteratedFDeriv_three_eq {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F] (g : E → F) (y a b c : E) :
    iteratedFDeriv 𝕜 3 g y ![a, b, c] = fderiv 𝕜 (fderiv 𝕜 (fderiv 𝕜 g)) y a b c := by
  rw [iteratedFDeriv_succ_apply_right, iteratedFDeriv_two_apply]
  simp [Fin.init]

variable {n : ℕ} {f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {U : Set ((Fin n → ℂ) × (Fin n → ℂ))}

/-- The third derivative of the real slice `y ↦ Re f (ι₂ y)` is the real part of the complex one. -/
theorem fderiv3_realPart_eq (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    {y : (Fin n → ℝ) × (Fin n → ℝ)} (hy : realInclusion₂ n y ∈ U)
    (x₁ x₂ x₃ : (Fin n → ℝ) × (Fin n → ℝ)) :
    fderiv ℝ (fderiv ℝ (fderiv ℝ (fun y => (f (realInclusion₂ n y)).re))) y x₁ x₂ x₃ =
      (fderiv ℂ (fderiv ℂ (fderiv ℂ f)) (realInclusion₂ n y) (realInclusion₂ n x₁)
        (realInclusion₂ n x₂) (realInclusion₂ n x₃)).re := by
  have hAn := KAM.analyticOnNhd_of_differentiableOn hU hf
  have hcC : ContDiffOn ℂ 3 f U := hAn.contDiffOn hU.uniqueDiffOn
  have hcR : ContDiffOn ℝ 3 f U := hcC.restrict_scalars ℝ
  set ι := realInclusion₂ n with hι
  have hU' : IsOpen (ι ⁻¹' U) := hU.preimage ι.continuous
  have hcR' : ContDiffOn ℝ 3 (f ∘ ι) (ι ⁻¹' U) := hcR.comp ι.contDiff.contDiffOn (fun _ h => h)
  have h1 : iteratedFDeriv ℝ 3 (fun y => (f (ι y)).re) y =
      Complex.reCLM.compContinuousMultilinearMap
        ((iteratedFDeriv ℝ 3 f (ι y)).compContinuousLinearMap fun _ => ι) := by
    have e1 := Complex.reCLM.iteratedFDeriv_comp_left (f := f ∘ ι) (x := y)
      (hcR'.contDiffAt (hU'.mem_nhds hy)) (i := 3) le_rfl
    have e2 := ι.iteratedFDerivWithin_comp_right (f := f) (s := U) hcR hU.uniqueDiffOn
      hU'.uniqueDiffOn (x := y) hy (i := 3) le_rfl
    rw [iteratedFDerivWithin_of_isOpen 3 hU' hy, iteratedFDerivWithin_of_isOpen 3 hU hy] at e2
    exact e1.trans (by rw [e2])
  have h2 : iteratedFDeriv ℝ 3 f (ι y) =
      ContinuousMultilinearMap.restrictScalars ℝ (iteratedFDeriv ℂ 3 f (ι y)) :=
    ((hcC.contDiffAt (hU.mem_nhds hy)).restrictScalars_iteratedFDeriv (𝕜 := ℝ)).symm
  have h3 := congrArg (fun L => L ![x₁, x₂, x₃]) h1
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply, h2,
    ContinuousMultilinearMap.coe_restrictScalars] at h3
  rw [iteratedFDeriv_three_eq] at h3
  rw [h3]
  have : (fun i : Fin 3 => ι (![x₁, x₂, x₃] i)) = ![ι x₁, ι x₂, ι x₃] := by
    ext i : 1; fin_cases i <;> rfl
  rw [this]
  have h4 := iteratedFDeriv_three_eq (𝕜 := ℂ) f (ι y) (ι x₁) (ι x₂) (ι x₃)
  rw [← h4]
  rfl

/-- **Third-derivative Cauchy bound on the real slice.** If `f` is holomorphic on the open `U`,
within `M` of the constant `a` on `ball (ι₂ y) r ⊆ U`, then
`|D³(Re f ∘ ι₂)(y)(x₁,x₂,x₃)| ≤ 64 M / r³ · ‖x₁‖‖x₂‖‖x₃‖`. -/
theorem abs_fderiv3_realPart_le (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    {y : (Fin n → ℝ) × (Fin n → ℝ)} {r M : ℝ} (a : ℂ) (hr : 0 < r)
    (hball : Metric.ball (realInclusion₂ n y) r ⊆ U)
    (hM : ∀ w ∈ Metric.ball (realInclusion₂ n y) r, ‖f w - a‖ ≤ M)
    (x₁ x₂ x₃ : (Fin n → ℝ) × (Fin n → ℝ)) :
    |fderiv ℝ (fderiv ℝ (fderiv ℝ (fun y => (f (realInclusion₂ n y)).re))) y x₁ x₂ x₃| ≤
      64 * M / r ^ 3 * (‖x₁‖ * ‖x₂‖ * ‖x₃‖) := by
  rw [fderiv3_realPart_eq hU hf (hball (Metric.mem_ball_self hr))]
  refine (Complex.abs_re_le_norm _).trans ?_
  have := norm_fderiv3_ball_le a hr (hf.mono hball) hM (realInclusion₂ n x₁)
    (realInclusion₂ n x₂) (realInclusion₂ n x₃)
  simpa only [norm_realInclusion₂] using this

end Real

end KAM.EffectiveStability

end
