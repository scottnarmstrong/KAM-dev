/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.SecularForm.Quadratic.Uniform

/-!
# Quadratic part: the uniform constants

Blueprint P, Part 8, `stepP:p8:qf-assembly` (package S8-Q). On a compact neighbourhood of
`action D a` the constant term, the coefficient entries and the complex secular function are
bounded; the radius `r` is chosen so that `axis D Λ ∈ axes n` there.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter Real Function Metric
open scoped BigOperators Topology Matrix.Norms.Elementwise
namespace KAM.Planetary
open KAM KAM.Kepler
namespace SecularForm
variable {n : ℕ}

theorem exists_remainder_constants (D : Data n) {a : Vec n} (ha : a ∈ axes n) :
    ∃ r0 r M1 MT ME : ℝ, 0 < r ∧ r < r0 ∧ r0 < rho D a ∧
      DifferentiableOn ℂ (secularC D false) (polydisc D a r0) ∧
      (∀ x ∈ realDisc D a r0, secularC D false (inclusion x) = (secular D false x : ℂ)) ∧
      AnalyticOnNhd ℝ (secular D false) (realDisc D a r0) ∧
      (∀ z ∈ polydisc D a r, ‖secularC D false z‖ ≤ M1) ∧
      ∀ Λ : Vec n, dist Λ (action D a) < r → axis D Λ ∈ axes n ∧
        |constantTerm D (axis D Λ)| ≤ MT ∧ ∑ i, ∑ j, |coeffs D (axis D Λ) i j| ≤ ME := by
  obtain ⟨r0, hr0, hrho0, -, hall⟩ := perturbation_analytic D ha
  obtain ⟨-, -, hSD, hreal, hAn, -⟩ := hall false
  obtain ⟨δ, hδ, hδa⟩ := Metric.eventually_nhds_iff.1 (eventually_axis_mem_axes D ha)
  set r := min (r0 / 2) (δ / 2) with hr
  have hr0' : 0 < r := lt_min (by linarith) (by linarith)
  have hrr0 : r < r0 := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hrδ : r < δ := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  -- bound of the complex secular function
  have hcomp : IsCompact (closedBall (center D a) r) := isCompact_closedBall _ _
  have hsub : closedBall (center D a) r ⊆ polydisc D a r0 := by
    rw [polydisc_eq_ball D a hr0]
    exact closedBall_subset_ball hrr0
  obtain ⟨M1, hM1⟩ := hcomp.exists_bound_of_continuousOn (hSD.continuousOn.mono hsub)
  -- bounds of the constant term and the coefficients on `closedBall (action D a) r`
  have hK : IsCompact (closedBall (action D a) r) := isCompact_closedBall _ _
  have hKaxes : ∀ Λ ∈ closedBall (action D a) r, axis D Λ ∈ axes n := fun Λ hΛ =>
    hδa (lt_of_le_of_lt (mem_closedBall.1 hΛ) hrδ)
  have hTc : ContinuousOn (fun Λ : Vec n => constantTerm D (axis D Λ))
      (closedBall (action D a) r) := fun Λ hΛ =>
    (((analyticAt_constantTerm D (hKaxes Λ hΛ)).comp
      (analyticAt_axis D Λ)).continuousAt).continuousWithinAt
  have hEc : ContinuousOn (fun Λ : Vec n => ∑ i, ∑ j, |coeffs D (axis D Λ) i j|)
      (closedBall (action D a) r) := by
    refine continuousOn_finsetSum _ fun i _ => continuousOn_finsetSum _ fun j _ => ?_
    intro Λ hΛ
    refine ContinuousAt.continuousWithinAt ?_
    have hc : AnalyticAt ℝ (coeffs D) (axis D Λ) := coeffs_analytic D _ (hKaxes Λ hΛ)
    have h1 : AnalyticAt ℝ (fun Λ : Vec n => coeffs D (axis D Λ)) Λ :=
      hc.comp (analyticAt_axis D Λ)
    have h2 : ContinuousAt (fun Λ : Vec n => coeffs D (axis D Λ)) Λ := h1.continuousAt
    have h3 : ContinuousAt (fun M : Mat n => M i j) (coeffs D (axis D Λ)) :=
      ((continuous_apply j).comp (continuous_apply i)).continuousAt
    have h4 : ContinuousAt (fun Λ : Vec n => coeffs D (axis D Λ) i j) Λ :=
      ContinuousAt.comp (g := fun M : Mat n => M i j) (f := fun Λ => coeffs D (axis D Λ)) h3 h2
    exact h4.abs
  obtain ⟨MT, hMT⟩ := hK.exists_bound_of_continuousOn hTc
  obtain ⟨ME, hME⟩ := hK.exists_bound_of_continuousOn hEc
  refine ⟨r0, r, M1, MT, ME, hr0', hrr0, hrho0, hSD, hreal, hAn, fun z hz => ?_, fun Λ hΛ => ?_⟩
  · refine hM1 z ?_
    rw [polydisc_eq_ball D a hr0'] at hz
    exact ball_subset_closedBall hz
  · have hmem : Λ ∈ closedBall (action D a) r := mem_closedBall.2 hΛ.le
    exact ⟨hKaxes Λ hmem, by simpa using hMT Λ hmem,
      by simpa using (le_abs_self _).trans (by simpa using hME Λ hmem)⟩

end SecularForm
end KAM.Planetary
end
