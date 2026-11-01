/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Exponential.ComplexTube

/-!
# Generic tube and Cauchy-estimate lemmas for the first-derivative bounds

Package LP-DOMX, `LP:MAIN L8 (253, 270)`, track LP, non-frozen.

* `complexTube_mono`, `complexTube_add_shift`, `closedBall_subset_complexTube`: elementary
  properties of `complexTube`.
* `exists_norm_le_halfTube`: a shift-periodic holomorphic function with values in a normed space is
  bounded on the half tube (compactness of one cell, as in `KAM.Planetary.perturbation`).
* `norm_fderiv_le_cauchyBall`: the multivariable Cauchy estimate
  `‖fderiv ℂ f z‖ ≤ M / ρ` from a bound `M` on `closedBall z ρ`.
-/

@[expose] public noncomputable section

namespace KAM.Planetary.StrongAMD

open KAM.Planetary Set Metric

section Cauchy

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F]
  [NormedSpace ℂ F]

/-- The multivariable Cauchy estimate: a bound `M` on `closedBall z ρ` bounds the Fréchet
derivative at the centre by `M / ρ` (restrict to complex lines, one-variable estimate). -/
theorem norm_fderiv_le_cauchyBall {f : E → F} {z : E} {ρ M : ℝ} (hρ : 0 < ρ)
    (hd : DifferentiableOn ℂ f (closedBall z ρ)) (hb : ∀ y ∈ closedBall z ρ, ‖f y‖ ≤ M) :
    ‖fderiv ℂ f z‖ ≤ M / ρ := by
  have hz : DifferentiableAt ℂ f z := hd.differentiableAt (closedBall_mem_nhds z hρ)
  have hM : 0 ≤ M := (norm_nonneg _).trans (hb z (mem_closedBall_self hρ.le))
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  by_cases hv : v = 0
  · simp [hv]
  have hvn : 0 < ‖v‖ := norm_pos_iff.2 hv
  set s : ℝ := ρ / ‖v‖ with hs
  have hs0 : 0 < s := by positivity
  have hmaps : ∀ t : ℂ, ‖t‖ ≤ s → z + t • v ∈ closedBall z ρ := fun t ht => by
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul]
    calc ‖t‖ * ‖v‖ ≤ s * ‖v‖ := by gcongr
      _ = ρ := by rw [hs]; field_simp
  have hinner : ∀ t : ℂ, HasDerivAt (fun t : ℂ => z + t • v) v t := fun t => by
    simpa using ((hasDerivAt_id t).smul_const v).const_add z
  have hφ : Differentiable ℂ (fun t : ℂ => z + t • v) := fun t => (hinner t).differentiableAt
  have hg : DifferentiableOn ℂ (fun t : ℂ => f (z + t • v)) (closedBall 0 s) :=
    hd.comp hφ.differentiableOn fun t ht => hmaps t (by simpa using ht)
  have hgc : DiffContOnCl ℂ (fun t : ℂ => f (z + t • v)) (ball 0 s) :=
    (hg.mono (by rw [closure_ball _ hs0.ne'])).diffContOnCl
  have hder : HasDerivAt (fun t : ℂ => f (z + t • v)) (fderiv ℂ f z v) 0 := by
    have h0 : HasFDerivAt f (fderiv ℂ f z) (z + (0 : ℂ) • v) := by
      simpa using hz.hasFDerivAt
    exact h0.comp_hasDerivAt 0 (hinner 0)
  have key := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hs0 hgc
    (C := M) (fun t ht => hb _ (hmaps t (by simpa using ht.le)))
  rw [hder.deriv] at key
  calc ‖fderiv ℂ f z v‖ ≤ M / s := key
    _ = M / ρ * ‖v‖ := by rw [hs]; field_simp

end Cauchy

end KAM.Planetary.StrongAMD

end
