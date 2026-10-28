/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Nekhoroshev.Averaging.PicardFamilies
public import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Parameter derivatives of Picard integrals

Blueprint N Part 12 (`bpN:p12:ext-dep#parameter-integral`, `#linear`).

* `KAM.Nekhoroshev.hasFDerivAt_intervalIntegral_comp`: differentiation under the integral sign
  for `x ↦ ∫₀ᵗ F (U τ x) dτ`, with derivative `∫₀ᵗ DF (U τ x) ∘ DU τ x`, by Mathlib's dominated
  derivative theorem.
* `KAM.Nekhoroshev.linear_family`: the continuous linear Volterra fixed family
  `Y t x = id + ∫₀ᵗ G τ x ∘ Y τ x`, obtained by contraction on bounded continuous families of
  continuous linear maps.
-/

@[expose] public noncomputable section

open Set Metric Function Filter
open scoped NNReal Topology BoundedContinuousFunction Interval Classical

namespace KAM.Nekhoroshev

section ParameterIntegral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `bpN:p12:ext-dep#parameter-integral`: differentiation of `x ↦ ∫₀ᵗ F (U τ x) dτ` at `x`.
`U τ` is differentiable with derivative `U' τ z` on a neighbourhood `B` of `x`, `F` has derivative
`F' w` at every value `U τ z`, both derivatives are bounded uniformly, and the integrands are
continuous in time. -/
theorem hasFDerivAt_intervalIntegral_comp {F : E → E} {F' : E → E →L[ℝ] E}
    {U : ℝ → E → E} {U' : ℝ → E → E →L[ℝ] E} {t : ℝ} {B : Set E} {x : E} {Λ M : ℝ}
    (hB : B ∈ 𝓝 x)
    (hU : ∀ τ ∈ [[0, t]], ∀ z ∈ B, HasFDerivAt (U τ) (U' τ z) z)
    (hF : ∀ τ ∈ [[0, t]], ∀ z ∈ B, HasFDerivAt F (F' (U τ z)) (U τ z))
    (hFb : ∀ τ ∈ [[0, t]], ∀ z ∈ B, ‖F' (U τ z)‖ ≤ Λ)
    (hUb : ∀ τ ∈ [[0, t]], ∀ z ∈ B, ‖U' τ z‖ ≤ M)
    (hFc : ∀ z ∈ B, ContinuousOn (fun τ => F (U τ z)) [[0, t]])
    (hDc : ContinuousOn (fun τ => (F' (U τ x)).comp (U' τ x)) [[0, t]]) :
    HasFDerivAt (fun z => ∫ τ in (0 : ℝ)..t, F (U τ z))
      (∫ τ in (0 : ℝ)..t, (F' (U τ x)).comp (U' τ x)) x := by
  have hx : x ∈ B := mem_of_mem_nhds hB
  have hsub : Ι (0 : ℝ) t ⊆ [[0, t]] := uIoc_subset_uIcc
  have hdiff : ∀ τ ∈ [[0, t]], ∀ z ∈ B,
      HasFDerivAt (fun w => F (U τ w)) ((F' (U τ z)).comp (U' τ z)) z := fun τ hτ z hz =>
    (hF τ hτ z hz).comp z (hU τ hτ z hz)
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le'' (H := E) (F := fun z τ => F (U τ z))
    (F' := fun z τ => (F' (U τ z)).comp (U' τ z)) (bound := fun _ => Λ * M) hB ?_ ?_ ?_ ?_ ?_ ?_
  · exact Filter.eventually_of_mem hB fun z hz =>
      ((hFc z hz).mono hsub).aestronglyMeasurable measurableSet_uIoc
  · exact (hFc x hx).intervalIntegrable
  · exact (hDc.mono hsub).aestronglyMeasurable measurableSet_uIoc
  · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_uIoc fun τ hτ z hz => ?_
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul (hFb τ (hsub hτ) z hz) (hUb τ (hsub hτ) z hz)
      (norm_nonneg _) ((norm_nonneg _).trans (hFb τ (hsub hτ) z hz)))
  · exact intervalIntegrable_const
  · exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_uIoc fun τ hτ z hz => hdiff τ (hsub hτ) z hz

end ParameterIntegral

end KAM.Nekhoroshev
