/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Frozen.Defs.ComplexStrip
public import Mathlib.Analysis.Complex.Liouville
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Cauchy estimates on open sets and complex strips

Restricting a holomorphic function to complex lines gives the Cauchy bound for its
Fréchet derivative on any complex normed space. For the sup norm on `Fin n → ℂ`,
closed balls are closed polydiscs. The strip specialization uses the frozen
`KAM.complexStrip` and explicit pointwise bounds, as required by blueprint Part 1.
-/

public noncomputable section

open Metric Set

namespace KAM

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- A unit complex line maps its closed disc into the corresponding closed ball. -/
theorem mapsTo_closedBall_line {z v : E} {δ : ℝ} (hv : ‖v‖ = 1) :
    MapsTo (fun ζ : ℂ => z + ζ • v) (closedBall 0 δ) (closedBall z δ) := by
  intro ζ hζ
  simpa [mem_closedBall, dist_eq_norm, norm_smul, hv] using hζ

/-- Cauchy's estimate at every order for the restriction to a unit complex line.
This is a one-variable derivative; it does not assert multivariable higher regularity. -/
theorem norm_iteratedDeriv_line_le_of_closedBall [CompleteSpace F]
    {U : Set E} {f : E → F} (hf : DifferentiableOn ℂ f U)
    {z v : E} {δ A : ℝ} (hδ : 0 < δ) (hv : ‖v‖ = 1)
    (hz : closedBall z δ ⊆ U) (hA : ∀ w ∈ U, ‖f w‖ ≤ A) (j : ℕ) :
    ‖iteratedDeriv j (fun ζ : ℂ => f (z + ζ • v)) 0‖ ≤ j.factorial * A / δ ^ j := by
  have hmaps : MapsTo (fun ζ : ℂ => z + ζ • v) (closedBall 0 δ) U :=
    (mapsTo_closedBall_line hv).mono_right hz
  have hcomp : DifferentiableOn ℂ (fun ζ : ℂ => f (z + ζ • v)) (closedBall 0 δ) :=
    hf.comp ((differentiable_id.smul_const v).const_add z).differentiableOn hmaps
  exact Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le j hδ
    (hcomp.diffContOnCl_ball (Subset.refl _))
    (fun ζ hζ => hA _ (hmaps (sphere_subset_closedBall hζ)))

/-- Cauchy's operator-norm estimate, requiring a bound only on the closed ball. -/
theorem norm_fderiv_le_of_closedBall_bound {U : Set E} (hU : IsOpen U) {f : E → F}
    (hf : DifferentiableOn ℂ f U) {z : E} {δ A : ℝ} (hδ : 0 < δ)
    (hz : closedBall z δ ⊆ U) (hA : ∀ w ∈ closedBall z δ, ‖f w‖ ≤ A) :
    ‖fderiv ℂ f z‖ ≤ A / δ := by
  have hzU : z ∈ U := hz (mem_closedBall_self hδ.le)
  have hA0 : 0 ≤ A := (norm_nonneg (f z)).trans (hA z (mem_closedBall_self hδ.le))
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (div_nonneg hA0 hδ.le)
  intro v hv
  have hline : ∀ ζ : ℂ, HasDerivAt (fun ζ : ℂ => z + ζ • v) v ζ := by
    intro ζ
    simpa using ((hasDerivAt_id ζ).smul_const v).const_add z
  have hmaps : MapsTo (fun ζ : ℂ => z + ζ • v) (closedBall 0 δ) U :=
    (mapsTo_closedBall_line hv).mono_right hz
  have hcomp : DifferentiableOn ℂ (fun ζ : ℂ => f (z + ζ • v)) (closedBall 0 δ) :=
    hf.comp (fun ζ _ => (hline ζ).differentiableAt.differentiableWithinAt) hmaps
  have hbound := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hδ
    (hcomp.diffContOnCl_ball (Subset.refl _))
    (fun ζ hζ => hA _ (mapsTo_closedBall_line hv (sphere_subset_closedBall hζ)))
  have hdf : HasFDerivAt f (fderiv ℂ f z) (z + (0 : ℂ) • v) := by
    simpa using (hf.differentiableAt (hU.mem_nhds hzU)).hasFDerivAt
  have heq : deriv (fun ζ : ℂ => f (z + ζ • v)) 0 = fderiv ℂ f z v :=
    (hdf.comp_hasDerivAt 0 (hline 0)).deriv
  rw [heq] at hbound
  exact hbound

/-- Cauchy's estimate for the operator norm of the derivative on an open domain.
For finite products with the sup norm, the ball hypothesis is a polydisc hypothesis. -/
theorem norm_fderiv_le_of_closedBall {U : Set E} (hU : IsOpen U) {f : E → F}
    (hf : DifferentiableOn ℂ f U) {z : E} {δ A : ℝ} (hδ : 0 < δ)
    (hz : closedBall z δ ⊆ U) (hA : ∀ w ∈ U, ‖f w‖ ≤ A) :
    ‖fderiv ℂ f z‖ ≤ A / δ :=
  norm_fderiv_le_of_closedBall_bound hU hf hδ hz (fun w hw => hA w (hz hw))

/-- The coordinate form of the Cauchy estimate on an arbitrary open domain. -/
theorem norm_coordinate_fderiv_le_of_closedBall {n : ℕ} {U : Set (Fin n → ℂ)}
    (hU : IsOpen U) {f : (Fin n → ℂ) → F} (hf : DifferentiableOn ℂ f U)
    {z : Fin n → ℂ} {δ A : ℝ} (hδ : 0 < δ) (hz : closedBall z δ ⊆ U)
    (hA : ∀ w ∈ U, ‖f w‖ ≤ A) (i : Fin n) :
    ‖fderiv ℂ f z (Pi.single i 1)‖ ≤ A / δ := by
  have h := (fderiv ℂ f z).le_opNorm (Pi.single i 1)
  simp only [Pi.norm_single, norm_one, mul_one] at h
  exact h.trans (norm_fderiv_le_of_closedBall hU hf hδ hz hA)

/-- The frozen complex strip is open. -/
theorem isOpen_complexStrip (n : ℕ) (ρ : ℝ) : IsOpen (complexStrip n ρ) := by
  simp only [complexStrip, ofPred_forall]
  exact isOpen_iInter_of_finite fun i =>
    isOpen_lt (Complex.continuous_im.comp (continuous_apply i)).abs continuous_const

/-- Every closed polydisc of radius `δ` around a point of the narrower strip stays
inside the original strip. The strict inner-strip inequality retains the boundary. -/
theorem closedBall_subset_complexStrip {n : ℕ} {ρ δ : ℝ} {z : Fin n → ℂ}
    (hz : z ∈ complexStrip n (ρ - δ)) : closedBall z δ ⊆ complexStrip n ρ := by
  intro w hw i
  have hwδ : ‖w - z‖ ≤ δ := by simpa only [mem_closedBall, dist_eq_norm] using hw
  have hi : |(w i - z i).im| ≤ δ :=
    (Complex.abs_im_le_norm _).trans ((norm_le_pi_norm (w - z) i).trans hwδ)
  calc
    |(w i).im| = |(w i - z i).im + (z i).im| := by simp
    _ ≤ |(w i - z i).im| + |(z i).im| := abs_add_le _ _
    _ < ρ := by linarith [hz i]

/-- Sup-norm Cauchy estimate on a strip, with the operator norm on the derivative.
It applies to scalar, vector, and matrix targets with their chosen normed-space norms. -/
theorem norm_fderiv_le_of_mem_complexStrip {n : ℕ} {ρ δ A : ℝ}
    {f : (Fin n → ℂ) → F} (hf : DifferentiableOn ℂ f (complexStrip n ρ))
    (hA : ∀ w ∈ complexStrip n ρ, ‖f w‖ ≤ A) (hδ : 0 < δ)
    {z : Fin n → ℂ} (hz : z ∈ complexStrip n (ρ - δ)) :
    ‖fderiv ℂ f z‖ ≤ A / δ :=
  norm_fderiv_le_of_closedBall (isOpen_complexStrip n ρ) hf hδ
    (closedBall_subset_complexStrip hz) hA

/-- In particular, every coordinate derivative satisfies the sharp `A / δ` bound. -/
theorem norm_coordinate_fderiv_le_of_mem_complexStrip {n : ℕ} {ρ δ A : ℝ}
    {f : (Fin n → ℂ) → F} (hf : DifferentiableOn ℂ f (complexStrip n ρ))
    (hA : ∀ w ∈ complexStrip n ρ, ‖f w‖ ≤ A) (hδ : 0 < δ)
    {z : Fin n → ℂ} (hz : z ∈ complexStrip n (ρ - δ)) (i : Fin n) :
    ‖fderiv ℂ f z (Pi.single i 1)‖ ≤ A / δ := by
  have h := (fderiv ℂ f z).le_opNorm (Pi.single i 1)
  simp only [Pi.norm_single, norm_one, mul_one] at h
  exact h.trans (norm_fderiv_le_of_mem_complexStrip hf hA hδ hz)

/-- Pure directional derivatives of every order on a narrower strip. -/
theorem norm_iteratedDeriv_line_le_of_mem_complexStrip [CompleteSpace F]
    {n : ℕ} {ρ δ A : ℝ} {f : (Fin n → ℂ) → F}
    (hf : DifferentiableOn ℂ f (complexStrip n ρ))
    (hA : ∀ w ∈ complexStrip n ρ, ‖f w‖ ≤ A) (hδ : 0 < δ)
    {z v : Fin n → ℂ} (hz : z ∈ complexStrip n (ρ - δ)) (hv : ‖v‖ = 1) (j : ℕ) :
    ‖iteratedDeriv j (fun ζ : ℂ => f (z + ζ • v)) 0‖ ≤ j.factorial * A / δ ^ j :=
  norm_iteratedDeriv_line_le_of_closedBall hf hδ hv (closedBall_subset_complexStrip hz) hA j

/-- Repeated differentiation in a single coordinate has the factorial Cauchy bound. -/
theorem norm_iteratedDeriv_coordinate_le_of_mem_complexStrip [CompleteSpace F]
    {n : ℕ} {ρ δ A : ℝ} {f : (Fin n → ℂ) → F}
    (hf : DifferentiableOn ℂ f (complexStrip n ρ))
    (hA : ∀ w ∈ complexStrip n ρ, ‖f w‖ ≤ A) (hδ : 0 < δ)
    {z : Fin n → ℂ} (hz : z ∈ complexStrip n (ρ - δ)) (i : Fin n) (j : ℕ) :
    ‖iteratedDeriv j (fun ζ : ℂ => f (z + ζ • Pi.single i 1)) 0‖ ≤
      j.factorial * A / δ ^ j :=
  norm_iteratedDeriv_line_le_of_mem_complexStrip hf hA hδ hz
    (by simp only [Pi.norm_single, norm_one]) j

end KAM

end
