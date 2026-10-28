/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PGAssembly.Jets
public import KAM.Strip.AnalyticTaylor

/-!
# P Part 5: the uniform fifth-order remainder (`bpP:p5:uniform-remainder`)

`schwarz_order_five` is the higher-order Schwarz lemma (`stepP:p5:ur-schwarz`): a holomorphic function
on a disc, bounded by `M` and vanishing to order five at the centre, satisfies
`‖g z‖ ≤ M / R ^ 5 * ‖z‖ ^ 5`. It is derived from the maximum principle for `g z / z ^ 5` on
circles of radius `R' < R`, then `R' ↑ R`.

`uniform_remainder` (`stepP:p5:ur-bound`, `stepP:p5:ur-schwarz`) bounds the average by the
extension bound `MP`, the jets by Cauchy estimates, and applies `schwarz_order_five` on the complex
line through `x` using the vanishing remainder jet of `birkhoff_ext`.
Design `docs/tracks/P/design/P45-LEAN-DESIGN.md`, package P5-REM.
-/

@[expose] public noncomputable section

open Set Metric Filter Topology MeasureTheory
open scoped BigOperators

namespace KAM.Planetary

variable {a b : ℕ}

/-- Order-five factorisation: a function holomorphic near `0` and with vanishing jet of order
`≤ 4` has a holomorphic quotient by `z ^ 5`, bounded on circles. -/
theorem schwarz_quotient_bound {R M : ℝ} {g : ℂ → ℂ} (hR : 0 < R)
    (hg : DifferentiableOn ℂ g (ball 0 R)) (hbound : ∀ z ∈ ball (0:ℂ) R, ‖g z‖ ≤ M)
    (hjet : ∀ k : ℕ, k ≤ 4 → iteratedDeriv k g 0 = 0) {R' : ℝ} (hR'0 : 0 < R') (hR' : R' < R) :
    ∀ z ∈ closedBall (0:ℂ) R', ‖g z‖ ≤ M / R' ^ 5 * ‖z‖ ^ 5 := by
  have hopen : IsOpen (ball (0:ℂ) R) := isOpen_ball
  have hg0 : AnalyticAt ℂ g 0 := hg.analyticAt (hopen.mem_nhds (by simpa using hR))
  have hord : ((5 : ℕ) : ℕ∞) ≤ analyticOrderAt g 0 :=
    (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hg0).2
      fun i hi => hjet i (by omega)
  obtain ⟨k, hk, hev⟩ := (natCast_le_analyticOrderAt hg0).1 hord
  set h : ℂ → ℂ := Function.update (fun z => (z ^ 5)⁻¹ * g z) 0 (k 0) with hh
  have hev' : ∀ᶠ z in 𝓝 (0:ℂ), h z = k z := by
    have hne : ∀ᶠ z in 𝓝[≠] (0:ℂ), h z = k z := by
      filter_upwards [(nhdsWithin_le_nhds hev), self_mem_nhdsWithin] with z hz hz0
      have hz0' : z ≠ 0 := hz0
      rw [hh, Function.update_of_ne hz0', hz]
      simp only [sub_zero, smul_eq_mul]
      field_simp
    have h0 : h 0 = k 0 := by simp [hh]
    rw [eventually_nhdsWithin_iff] at hne
    filter_upwards [hne] with z hz
    by_cases hz0 : z = 0
    · rw [hz0, h0]
    · exact hz hz0
  have hdiff : DifferentiableOn ℂ h (closedBall 0 R') := by
    intro z hz
    have hzR : z ∈ ball (0:ℂ) R := by
      rw [mem_ball_zero_iff]; rw [mem_closedBall_zero_iff] at hz; linarith
    by_cases hz0 : z = 0
    · subst hz0
      exact ((hk.differentiableAt).congr_of_eventuallyEq hev').differentiableWithinAt
    · have : DifferentiableAt ℂ h z := by
        have hgz : DifferentiableAt ℂ g z := hg.differentiableAt (hopen.mem_nhds hzR)
        have hq : DifferentiableAt ℂ (fun z => (z ^ 5)⁻¹ * g z) z :=
          ((differentiableAt_id.pow 5).inv (pow_ne_zero 5 hz0)).mul hgz
        refine hq.congr_of_eventuallyEq ?_
        filter_upwards [isOpen_ne.mem_nhds hz0] with w hw
        simp [hh, Function.update_of_ne hw]
      exact this.differentiableWithinAt
  have hdc : DiffContOnCl ℂ h (ball 0 R') := by
    refine ⟨hdiff.mono ball_subset_closedBall, ?_⟩
    rw [closure_ball _ hR'0.ne']
    exact hdiff.continuousOn
  have hfront : ∀ z ∈ frontier (ball (0:ℂ) R'), ‖h z‖ ≤ M / R' ^ 5 := by
    intro z hz
    rw [frontier_ball _ hR'0.ne', mem_sphere_zero_iff_norm] at hz
    have hz0 : z ≠ 0 := by
      intro h0; rw [h0, norm_zero] at hz; linarith
    have hzR : z ∈ ball (0:ℂ) R := by rw [mem_ball_zero_iff]; linarith
    rw [hh, Function.update_of_ne hz0, norm_mul, norm_inv, norm_pow, hz, ← div_eq_inv_mul]
    exact div_le_div_of_nonneg_right (hbound z hzR) (by positivity)
  intro z hz
  have hzcl : z ∈ closure (ball (0:ℂ) R') := by rwa [closure_ball _ hR'0.ne']
  have hbd := Complex.norm_le_of_forall_mem_frontier_norm_le (isBounded_ball) hdc hfront hzcl
  by_cases hz0 : z = 0
  · subst hz0
    have := hjet 0 (by omega)
    simp only [iteratedDeriv_zero] at this
    simp [this]
  · rw [hh, Function.update_of_ne hz0, norm_mul, norm_inv, norm_pow] at hbd
    have hzpos : 0 < ‖z‖ ^ 5 := by positivity
    rw [inv_mul_le_iff₀ hzpos] at hbd
    simpa [mul_comm] using hbd

/-- Higher-order Schwarz, used after restricting to a complex line. -/
theorem schwarz_order_five {R M : ℝ} (hR : 0 < R) (hM : 0 ≤ M) {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g (ball 0 R)) (hbound : ∀ z ∈ ball (0:ℂ) R, ‖g z‖ ≤ M)
    (hjet : ∀ k : ℕ, k ≤ 4 → iteratedDeriv k g 0 = 0) :
    ∀ z ∈ ball (0:ℂ) R, ‖g z‖ ≤ M/R^5*‖z‖^5 := by
  intro z hz
  have _ := hM
  rw [mem_ball_zero_iff] at hz
  have hlim : Tendsto (fun R' : ℝ => M / R' ^ 5 * ‖z‖ ^ 5) (𝓝[<] R) (𝓝 (M / R ^ 5 * ‖z‖ ^ 5)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds ?_
    have : ContinuousAt (fun R' : ℝ => M / R' ^ 5 * ‖z‖ ^ 5) R := by
      have : R ^ 5 ≠ 0 := by positivity
      fun_prop (disch := assumption)
    exact this.tendsto
  refine ge_of_tendsto hlim ?_
  have hev : ∀ᶠ R' in 𝓝[<] R, ‖z‖ < R' := by
    have : Ioo ‖z‖ R ∈ 𝓝[<] R := Ioo_mem_nhdsLT hz
    filter_upwards [this] with R' hR' using hR'.1
  filter_upwards [hev, self_mem_nhdsWithin] with R' hzR' hR'lt
  have hR'0 : 0 < R' := lt_of_le_of_lt (norm_nonneg z) hzR'
  exact schwarz_quotient_bound hR hg hbound hjet hR'0 hR'lt z
    (by rw [mem_closedBall_zero_iff]; exact hzR'.le)

end KAM.Planetary

end
