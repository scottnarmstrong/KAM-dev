/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Strip.Cauchy
public import Mathlib.Analysis.Calculus.ParametricCircleIntegral
public import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Tactic.FunProp

/-!
# Higher regularity of holomorphic functions on finite complex products

The Cauchy formula for a coordinate derivative is a parameter-dependent circle
integral. The first derivative bound supplies a uniform bound for differentiating
this integral, without assuming continuity of the first derivative in advance.
-/

public noncomputable section

open Metric Set Filter MeasureTheory
open scoped Topology Real Interval ContDiff

namespace KAM

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  [CompleteSpace F] [SecondCountableTopology F]

private theorem line_shift_closedBall_subset {U : Set (Fin n → ℂ)}
    {z v x : Fin n → ℂ} {r : ℝ} (hv : ‖v‖ = 1)
    (hz : closedBall z (3 * r) ⊆ U) (hx : x ∈ ball z r)
    {ζ : ℂ} (hζ : ζ ∈ closedBall 0 r) : closedBall (x + ζ • v) r ⊆ U := by
  intro w hw
  apply hz
  have hζv : dist (x + ζ • v) x ≤ r := by
    simpa [dist_eq_norm, norm_smul, hv] using hζ
  have htri := dist_triangle w (x + ζ • v) z
  have htri' := dist_triangle (x + ζ • v) x z
  rw [mem_closedBall] at hw ⊢
  rw [mem_ball] at hx
  linarith

/-- A directional first derivative is differentiable near the centre of a bounded
holomorphic domain. No higher regularity is assumed. -/
theorem differentiableAt_fderiv_apply_of_bounded {U : Set (Fin n → ℂ)}
    (hU : IsOpen U) {f : (Fin n → ℂ) → F} (hf : DifferentiableOn ℂ f U)
    {z v : Fin n → ℂ} {r A : ℝ} (hr : 0 < r) (hv : ‖v‖ = 1)
    (hz : closedBall z (3 * r) ⊆ U) (hA : ∀ w ∈ U, ‖f w‖ ≤ A) :
    DifferentiableAt ℂ (fun x => fderiv ℂ f x v) z := by
  let g := fun (x : Fin n → ℂ) (ζ : ℂ) => ζ⁻¹ ^ 2 • f (x + ζ • v)
  let g' := fun (x : Fin n → ℂ) (ζ : ℂ) => ζ⁻¹ ^ 2 • fderiv ℂ f (x + ζ • v)
  have hshift := fun x hx ζ hζ =>
    line_shift_closedBall_subset hv hz (x := x) hx (ζ := ζ) hζ
  have hmem : ∀ x ∈ ball z r, ∀ ζ : ℂ, ζ ∈ closedBall 0 r → x + ζ • v ∈ U := by
    intro x hx ζ hζ
    exact hshift x hx ζ hζ (mem_closedBall_self hr.le)
  have hcont : ∀ x ∈ ball z r, ContinuousOn (g x) (sphere 0 r) := by
    intro x hx
    apply ((continuousOn_id.inv₀ ?_).pow 2).smul
      (hf.continuousOn.comp (by fun_prop) (fun ζ hζ =>
        hmem x hx ζ (sphere_subset_closedBall hζ)))
    intro ζ hζ heq
    change ζ = 0 at heq
    have := mem_sphere_zero_iff_norm.mp hζ
    simp [heq] at this
    linarith
  have hmeas : ∀ᶠ x in 𝓝 z, AEStronglyMeasurable
      (fun θ : ℝ => g x (circleMap 0 r θ)) (volume.restrict (Ι 0 (2 * π))) := by
    filter_upwards [ball_mem_nhds z hr] with x hx
    exact ((hcont x hx).comp_continuous (continuous_circleMap 0 r)
      (fun θ => circleMap_mem_sphere 0 hr.le θ)).aestronglyMeasurable
  have hmeas' : AEStronglyMeasurable (fun θ : ℝ => g' z (circleMap 0 r θ))
      (volume.restrict (Ι 0 (2 * π))) := by
    apply Measurable.aestronglyMeasurable
    exact ((continuous_circleMap 0 r).measurable.inv.pow_const 2).smul
      ((measurable_fderiv ℂ f).comp (by fun_prop))
  have hdiff : ∀ ζ ∈ sphere 0 |r|, ∀ x ∈ ball z r,
      HasFDerivAt (fun x => g x ζ) (g' x ζ) x := by
    intro ζ hζ x hx
    rw [abs_of_pos hr] at hζ
    have hd := (hf.differentiableAt
      (hU.mem_nhds (hmem x hx ζ (sphere_subset_closedBall hζ)))).hasFDerivAt
    convert! (hd.comp x ((hasFDerivAt_id x).add_const (ζ • v))).const_smul (ζ⁻¹ ^ 2)
      using 1
  have hbound : ∀ ζ ∈ sphere 0 |r|, ∀ x ∈ ball z r,
      ‖g' x ζ‖ ≤ r⁻¹ ^ 2 * (A / r) := by
    intro ζ hζ x hx
    rw [abs_of_pos hr] at hζ
    dsimp [g']
    rw [norm_smul, norm_pow, norm_inv, mem_sphere_zero_iff_norm.mp hζ]
    exact mul_le_mul_of_nonneg_left
      (norm_fderiv_le_of_closedBall hU hf hr
        (hshift x hx ζ (sphere_subset_closedBall hζ)) hA) (sq_nonneg _)
  have hint := hasFDerivAt_circleIntegral_of_dominated_of_fderiv_le
    (𝕜 := ℂ) (bound := fun _ => r⁻¹ ^ 2 * (A / r)) (ball_mem_nhds z hr)
    hmeas ((hcont z (mem_ball_self hr)).circleIntegrable hr.le) hmeas' hbound
    (circleIntegrable_const _ _ _) hdiff
  have heq : (fun x => (2 * π * Complex.I)⁻¹ • ∮ ζ in C(0, r), g x ζ)
      =ᶠ[𝓝 z] (fun x => fderiv ℂ f x v) := by
    filter_upwards [ball_mem_nhds z hr] with x hx
    have hcomp : DifferentiableOn ℂ (fun ζ : ℂ => f (x + ζ • v)) (closedBall 0 r) :=
      hf.comp ((differentiable_id.smul_const v).const_add x).differentiableOn (hmem x hx)
    have hxU : x ∈ U := by simpa using hmem x hx 0 (mem_closedBall_self hr.le)
    have hd : HasFDerivAt f (fderiv ℂ f x) (x + (0 : ℂ) • v) := by
      simpa using (hf.differentiableAt (hU.mem_nhds hxU)).hasFDerivAt
    have hl : HasDerivAt (fun ζ : ℂ => x + ζ • v) v 0 := by
      simpa using ((hasDerivAt_id (0 : ℂ)).smul_const v).const_add x
    have hd' : deriv (fun ζ : ℂ => f (x + ζ • v)) 0 = fderiv ℂ f x v :=
      (hd.comp_hasDerivAt 0 hl).deriv
    have hc : (∮ ζ in C(0, r), g x ζ) = (2 * π * Complex.I) • fderiv ℂ f x v := by
      simpa only [g, sub_zero, one_div, inv_pow, hd'] using
        hcomp.deriv_eq_smul_circleIntegral hr
    rw [hc, inv_smul_smul₀ (by simp [Real.pi_ne_zero])]
  exact (hint.differentiableAt.const_smul (2 * π * Complex.I)⁻¹).congr_of_eventuallyEq heq.symm

/-- The Fréchet derivative of a holomorphic function on an open subset of `ℂⁿ`
is itself holomorphic. Local boundedness follows from continuity and compact balls. -/
theorem differentiableOn_fderiv_of_isOpen_pi {U : Set (Fin n → ℂ)} (hU : IsOpen U)
    {f : (Fin n → ℂ) → F} (hf : DifferentiableOn ℂ f U) :
    DifferentiableOn ℂ (fderiv ℂ f) U := by
  intro z hz
  obtain ⟨R, hR, hRU⟩ := nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hz)
  obtain ⟨A, hA⟩ := ((isCompact_closedBall z R).image_of_continuousOn
    (hf.continuousOn.mono hRU)).isBounded.exists_norm_le
  have hsmall : closedBall z (3 * (R / 4)) ⊆ ball z R :=
    closedBall_subset_ball (by linarith)
  have hcoord : ∀ i : Fin n,
      DifferentiableAt ℂ (fun x => fderiv ℂ f x (Pi.single i 1)) z := by
    intro i
    exact differentiableAt_fderiv_apply_of_bounded isOpen_ball
      (hf.mono (ball_subset_closedBall.trans hRU)) (by positivity)
      (by simp only [Pi.norm_single, norm_one]) hsmall
      (fun w hw => hA _ (mem_image_of_mem f (ball_subset_closedBall hw)))
  let e := ContinuousLinearEquiv.piRing (𝕜 := ℂ) (E := F) (Fin n)
  have hpi : DifferentiableAt ℂ (fun x => e (fderiv ℂ f x)) z :=
    differentiableAt_pi.mpr hcoord
  have h := e.symm.differentiableAt.comp z hpi
  simpa only [Function.comp_def, ContinuousLinearEquiv.symm_apply_apply]
    using h.differentiableWithinAt

/-- Holomorphic functions on finite complex products have every finite order of
continuous differentiability, including mixed derivatives. -/
theorem contDiffOn_nat_of_differentiableOn_pi {U : Set (Fin n → ℂ)} (hU : IsOpen U)
    {f : (Fin n → ℂ) → F} (hf : DifferentiableOn ℂ f U) (j : ℕ) :
    ContDiffOn ℂ j f U := by
  induction j generalizing F with
  | zero => exact contDiffOn_zero.mpr hf.continuousOn
  | succ j ih =>
    rw [Nat.cast_add, Nat.cast_one, contDiffOn_succ_iff_fderiv_of_isOpen hU]
    exact ⟨hf, by simp, ih (differentiableOn_fderiv_of_isOpen_pi hU hf)⟩

/-- Holomorphy on an open subset of `ℂⁿ` implies complex smoothness. -/
theorem contDiffOn_infty_of_differentiableOn_pi {U : Set (Fin n → ℂ)} (hU : IsOpen U)
    {f : (Fin n → ℂ) → F} (hf : DifferentiableOn ℂ f U) : ContDiffOn ℂ ∞ f U :=
  contDiffOn_infty.mpr (contDiffOn_nat_of_differentiableOn_pi hU hf)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

/-- Holomorphy implies smoothness on every finite-dimensional complex normed space,
including the angle/action product space of the frozen Hamiltonian hypotheses. -/
theorem contDiffOn_infty_of_differentiableOn {U : Set E} (hU : IsOpen U)
    {f : E → F} (hf : DifferentiableOn ℂ f U) : ContDiffOn ℂ ∞ f U := by
  let e := (Module.finBasis ℂ E).equivFunL
  have hg : DifferentiableOn ℂ (f ∘ e.symm) (e.symm ⁻¹' U) :=
    hf.comp e.symm.differentiable.differentiableOn (fun _ hx => hx)
  have hgs := contDiffOn_infty_of_differentiableOn_pi (hU.preimage e.symm.continuous) hg
  have h := hgs.comp e.contDiff.contDiffOn (fun x hx => by simpa using hx)
  simpa only [Function.comp_def, ContinuousLinearEquiv.symm_apply_apply] using h

/-- Finite-order smoothness from holomorphy on a finite-dimensional complex domain. -/
theorem contDiffOn_nat_of_differentiableOn {U : Set E} (hU : IsOpen U)
    {f : E → F} (hf : DifferentiableOn ℂ f U) (j : ℕ) : ContDiffOn ℂ j f U :=
  contDiffOn_infty.mp (contDiffOn_infty_of_differentiableOn hU hf) j

/-- The derivative remains holomorphic on a finite-dimensional complex domain. -/
theorem differentiableOn_fderiv_of_isOpen {U : Set E} (hU : IsOpen U)
    {f : E → F} (hf : DifferentiableOn ℂ f U) : DifferentiableOn ℂ (fderiv ℂ f) U := by
  have hs := contDiffOn_infty_of_differentiableOn hU hf
  exact ((contDiffOn_infty_iff_fderiv_of_isOpen hU).mp hs).2.differentiableOn (by simp)

end KAM

end
