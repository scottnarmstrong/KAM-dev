/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Strip.Regularity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The derivative of a holomorphic Banach-valued map is holomorphic, without separability

Track K proves `differentiableOn_fderiv_of_isOpen_pi` for targets with a second countable topology
(finite-dimensional spaces). The operator spaces `𝓛` of W4 are not separable. Here the statement is
extended to every complex Banach space `F`: near a point the image of a compact ball is compact,
hence separable, so the map takes values in a closed separable subspace `F₀`; its derivative takes
values in `F₀`; and the second countable result applies to the corestricted map.
-/

@[expose] public section

namespace KAM.Wave

open KAM Metric Set Filter
open scoped Topology

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- The closed subspace spanned by a set. -/
private noncomputable def spanClosure (K : Set F) : Submodule ℂ F :=
  (Submodule.span ℂ K).topologicalClosure

omit [CompleteSpace F] in
private theorem isClosed_spanClosure (K : Set F) : IsClosed (spanClosure K : Set F) :=
  Submodule.isClosed_topologicalClosure _

omit [CompleteSpace F] in
private theorem subset_spanClosure (K : Set F) : K ⊆ spanClosure K :=
  fun _ hx => Submodule.le_topologicalClosure _ (Submodule.subset_span hx)

omit [CompleteSpace F] in
private theorem isSeparable_spanClosure {K : Set F} (hK : TopologicalSpace.IsSeparable K) :
    TopologicalSpace.IsSeparable (spanClosure K : Set F) := by
  have := hK.span (R := ℂ)
  exact this.closure

/-- **The derivative of a holomorphic Banach-valued map on an open subset of `ℂⁿ` is holomorphic**
(no separability of the target is assumed). -/
theorem differentiableOn_fderiv_of_isOpen_pi_banach {n : ℕ} {U : Set (Fin n → ℂ)}
    (hU : IsOpen U) {f : (Fin n → ℂ) → F} (hf : DifferentiableOn ℂ f U) :
    DifferentiableOn ℂ (fderiv ℂ f) U := by
  classical
  intro z hz
  obtain ⟨R, hR, hRU⟩ := nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hz)
  have hK : IsCompact (f '' closedBall z R) :=
    (isCompact_closedBall z R).image_of_continuousOn (hf.continuousOn.mono hRU)
  set F₀ : Submodule ℂ F := spanClosure (f '' closedBall z R) with hF₀
  have : CompleteSpace F₀ := (isClosed_spanClosure _).completeSpace_coe
  have : SecondCountableTopology F₀ :=
    (isSeparable_spanClosure hK.isSeparable).secondCountableTopology
  have hmem : ∀ w ∈ closedBall z R, f w ∈ F₀ := fun w hw =>
    subset_spanClosure _ (mem_image_of_mem f hw)
  set g : (Fin n → ℂ) → F₀ := fun w => if h : f w ∈ F₀ then ⟨f w, h⟩ else 0 with hg
  have hgf : ∀ w ∈ closedBall z R, ((g w : F₀) : F) = f w := fun w hw => by
    simp [hg, hmem w hw]
  -- derivative values lie in `F₀`
  have hder : ∀ w ∈ ball z R, ∀ v : Fin n → ℂ, fderiv ℂ f w v ∈ F₀ := by
    intro w hw v
    have hwd : HasFDerivAt f (fderiv ℂ f w) w :=
      (hf.differentiableAt (hU.mem_nhds (hRU (ball_subset_closedBall hw)))).hasFDerivAt
    have hl : HasDerivAt (fun t : ℂ => w + t • v) v 0 := by
      simpa using ((hasDerivAt_id (0 : ℂ)).smul_const v).const_add w
    have h1 : HasDerivAt (fun t : ℂ => f (w + t • v)) (fderiv ℂ f w v) 0 := by
      have hwd' : HasFDerivAt f (fderiv ℂ f w) (w + (0 : ℂ) • v) := by simpa using hwd
      have := hwd'.comp_hasDerivAt (0 : ℂ) hl
      simpa [Function.comp_def] using this
    have h2 := h1.tendsto_slope_zero
    simp only [zero_add, zero_smul, add_zero] at h2
    refine (isClosed_spanClosure _).mem_of_tendsto h2 ?_
    have hev : ∀ᶠ t in 𝓝[≠] (0 : ℂ), w + t • v ∈ closedBall z R := by
      have hc : Continuous fun t : ℂ => w + t • v := by fun_prop
      have : ∀ᶠ t in 𝓝 (0 : ℂ), w + t • v ∈ closedBall z R :=
        hc.continuousAt.eventually_mem (by
          have hmn : closedBall z R ∈ 𝓝 w :=
            mem_nhds_iff.mpr ⟨ball z R, ball_subset_closedBall, isOpen_ball, hw⟩
          simpa using hmn)
      exact this.filter_mono nhdsWithin_le_nhds
    filter_upwards [hev] with t ht
    refine F₀.smul_mem _ (F₀.sub_mem (hmem _ ht) (hmem w (ball_subset_closedBall hw)))
  -- `g` is holomorphic on the ball
  let L : (w : Fin n → ℂ) → w ∈ ball z R → ((Fin n → ℂ) →L[ℂ] F₀) := fun w hw =>
    (fderiv ℂ f w).codRestrict F₀ (hder w hw)
  have hgd : ∀ w (hw : w ∈ ball z R), HasFDerivAt g (L w hw) w := by
    intro w hw
    have hwd : HasFDerivAt f (fderiv ℂ f w) w :=
      (hf.differentiableAt (hU.mem_nhds (hRU (ball_subset_closedBall hw)))).hasFDerivAt
    have hnb : ∀ᶠ x in 𝓝 w, x ∈ closedBall z R :=
      mem_nhds_iff.mpr ⟨ball z R, ball_subset_closedBall, isOpen_ball, hw⟩
    rw [hasFDerivAt_iff_tendsto] at hwd ⊢
    refine hwd.congr' ?_
    filter_upwards [hnb] with x hx
    have h1 : ((g x - g w - L w hw (x - w) : F₀) : F) = f x - f w - fderiv ℂ f w (x - w) := by
      have hw' : w ∈ closedBall z R := ball_subset_closedBall hw
      simp only [Submodule.coe_sub, hgf x hx, hgf w hw']
      rfl
    rw [← h1, Submodule.norm_coe]
  have hgdiff : DifferentiableOn ℂ g (ball z R) := fun w hw =>
    (hgd w hw).differentiableAt.differentiableWithinAt
  have hdg := differentiableOn_fderiv_of_isOpen_pi isOpen_ball hgdiff
  have hzb : z ∈ ball z R := mem_ball_self hR
  have heq : ∀ w ∈ ball z R, fderiv ℂ f w = F₀.subtypeL.comp (fderiv ℂ g w) := by
    intro w hw
    have hnb : ∀ᶠ x in 𝓝 w, x ∈ closedBall z R :=
      mem_nhds_iff.mpr ⟨ball z R, ball_subset_closedBall, isOpen_ball, hw⟩
    have hev : f =ᶠ[𝓝 w] fun x => F₀.subtypeL (g x) := by
      filter_upwards [hnb] with x hx
      exact (hgf x hx).symm
    rw [hev.fderiv_eq]
    have hgw : DifferentiableAt ℂ g w := (hgd w hw).differentiableAt
    have := fderiv_comp w (F₀.subtypeL.differentiableAt (x := g w)) hgw
    simpa only [Function.comp_def, ContinuousLinearMap.fderiv] using this
  have hz' : DifferentiableAt ℂ (fun w => F₀.subtypeL.comp (fderiv ℂ g w)) z :=
    (differentiableAt_const _).clm_comp
      ((hdg z hzb).differentiableAt (isOpen_ball.mem_nhds hzb))
  have hev : fderiv ℂ f =ᶠ[𝓝 z] fun w => F₀.subtypeL.comp (fderiv ℂ g w) :=
    Filter.eventually_of_mem (isOpen_ball.mem_nhds hzb) heq
  exact (hz'.congr_of_eventuallyEq hev).differentiableWithinAt

end KAM.Wave
