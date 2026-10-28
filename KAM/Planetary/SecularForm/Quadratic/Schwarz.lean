/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib

/-!
# Quadratic part: Schwarz lemma of order four and real versus complex derivatives

Blueprint P, Part 8, `stepP:p8:qf-assembly` (package S8-Q), uniform half.
`schwarz_order_four` is the
higher-order Schwarz lemma for a holomorphic function bounded by `M` on a disc of radius `R` and
vanishing to order four at the centre (the order-five version of `uniform_remainder`, with the
exponent lowered); `iteratedDeriv_ofReal` computes the derivatives of the restriction of a
holomorphic function to the real axis.
-/

@[expose] public noncomputable section
open Set Metric Filter
open scoped Topology
namespace KAM.Planetary
namespace SecularForm

/-- Order-four factorisation: a function holomorphic near `0` and with vanishing jet of order
`≤ 3` has a holomorphic quotient by `z ^ 4`, bounded on circles. -/
theorem schwarz_quotient_bound_four {R M : ℝ} {g : ℂ → ℂ} (hR : 0 < R)
    (hg : DifferentiableOn ℂ g (ball 0 R)) (hbound : ∀ z ∈ ball (0:ℂ) R, ‖g z‖ ≤ M)
    (hjet : ∀ k : ℕ, k ≤ 3 → iteratedDeriv k g 0 = 0) {R' : ℝ} (hR'0 : 0 < R') (hR' : R' < R) :
    ∀ z ∈ closedBall (0:ℂ) R', ‖g z‖ ≤ M / R' ^ 4 * ‖z‖ ^ 4 := by
  have hopen : IsOpen (ball (0:ℂ) R) := isOpen_ball
  have hg0 : AnalyticAt ℂ g 0 := hg.analyticAt (hopen.mem_nhds (by simpa using hR))
  have hord : ((4 : ℕ) : ℕ∞) ≤ analyticOrderAt g 0 :=
    (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hg0).2
      fun i hi => hjet i (by omega)
  obtain ⟨k, hk, hev⟩ := (natCast_le_analyticOrderAt hg0).1 hord
  set h : ℂ → ℂ := Function.update (fun z => (z ^ 4)⁻¹ * g z) 0 (k 0) with hh
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
        have hq : DifferentiableAt ℂ (fun z => (z ^ 4)⁻¹ * g z) z :=
          ((differentiableAt_id.pow 4).inv (pow_ne_zero 4 hz0)).mul hgz
        refine hq.congr_of_eventuallyEq ?_
        filter_upwards [isOpen_ne.mem_nhds hz0] with w hw
        simp [hh, Function.update_of_ne hw]
      exact this.differentiableWithinAt
  have hdc : DiffContOnCl ℂ h (ball 0 R') := by
    refine ⟨hdiff.mono ball_subset_closedBall, ?_⟩
    rw [closure_ball _ hR'0.ne']
    exact hdiff.continuousOn
  have hfront : ∀ z ∈ frontier (ball (0:ℂ) R'), ‖h z‖ ≤ M / R' ^ 4 := by
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
    have hzpos : 0 < ‖z‖ ^ 4 := by positivity
    rw [inv_mul_le_iff₀ hzpos] at hbd
    simpa [mul_comm] using hbd

/-- Higher-order Schwarz, used after restricting to a complex line. -/
theorem schwarz_order_four {R M : ℝ} (hR : 0 < R) (hM : 0 ≤ M) {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g (ball 0 R)) (hbound : ∀ z ∈ ball (0:ℂ) R, ‖g z‖ ≤ M)
    (hjet : ∀ k : ℕ, k ≤ 3 → iteratedDeriv k g 0 = 0) :
    ∀ z ∈ ball (0:ℂ) R, ‖g z‖ ≤ M/R^4*‖z‖^4 := by
  intro z hz
  have _ := hM
  rw [mem_ball_zero_iff] at hz
  have hlim : Tendsto (fun R' : ℝ => M / R' ^ 4 * ‖z‖ ^ 4) (𝓝[<] R) (𝓝 (M / R ^ 4 * ‖z‖ ^ 4)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds ?_
    have : ContinuousAt (fun R' : ℝ => M / R' ^ 4 * ‖z‖ ^ 4) R := by
      have : R ^ 4 ≠ 0 := by positivity
      fun_prop (disch := assumption)
    exact this.tendsto
  refine ge_of_tendsto hlim ?_
  have hev : ∀ᶠ R' in 𝓝[<] R, ‖z‖ < R' := by
    have : Ioo ‖z‖ R ∈ 𝓝[<] R := Ioo_mem_nhdsLT hz
    filter_upwards [this] with R' hR' using hR'.1
  filter_upwards [hev, self_mem_nhdsWithin] with R' hzR' hR'lt
  have hR'0 : 0 < R' := lt_of_le_of_lt (norm_nonneg z) hzR'
  exact schwarz_quotient_bound_four hR hg hbound hjet hR'0 hR'lt z
    (by rw [mem_closedBall_zero_iff]; exact hzR'.le)


/-- The derivatives of the restriction of a holomorphic function to the real axis. -/
theorem iteratedDeriv_ofReal {U : Set ℂ} (hU : IsOpen U) {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g U)
    (k : ℕ) {y : ℝ} (hy : (y : ℂ) ∈ U) :
    iteratedDeriv k (fun t : ℝ => g t) y = iteratedDeriv k g (y : ℂ) := by
  have hA : AnalyticOnNhd ℂ g U := hg.analyticOnNhd hU
  have hAk : ∀ k : ℕ, AnalyticOnNhd ℂ (iteratedDeriv k g) U := by
    intro k
    induction k with
    | zero => simpa using hA
    | succ k ih => simpa [iteratedDeriv_succ] using ih.deriv
  induction k generalizing y with
  | zero => simp
  | succ k ih =>
    have hopen : IsOpen ((fun t : ℝ => (t : ℂ)) ⁻¹' U) := hU.preimage Complex.continuous_ofReal
    have hev : iteratedDeriv k (fun t : ℝ => g t) =ᶠ[𝓝 y]
        fun t : ℝ => iteratedDeriv k g (t : ℂ) := by
      filter_upwards [hopen.mem_nhds hy] with t ht
      exact ih ht
    rw [iteratedDeriv_succ, hev.deriv_eq, iteratedDeriv_succ]
    have hd : DifferentiableAt ℂ (iteratedDeriv k g) (y : ℂ) :=
      ((hAk k) _ hy).differentiableAt
    exact (hd.hasDerivAt.comp_ofReal).deriv

/-- The derivatives of a real analytic function viewed as complex valued. -/
theorem iteratedDeriv_ofReal_comp {ψ : ℝ → ℝ} (hψ : AnalyticAt ℝ ψ 0) (k : ℕ) :
    iteratedDeriv k (fun s : ℝ => (ψ s : ℂ)) 0 = ((iteratedDeriv k ψ 0 : ℝ) : ℂ) := by
  have hAk : ∀ k : ℕ, ∀ᶠ y in 𝓝 (0 : ℝ), AnalyticAt ℝ (iteratedDeriv k ψ) y := by
    intro k
    induction k with
    | zero => simpa using hψ.eventually_analyticAt
    | succ k ih =>
      filter_upwards [ih.eventually_nhds] with y hy
      have : AnalyticAt ℝ (deriv (iteratedDeriv k ψ)) y :=
        (hy.self_of_nhds).deriv
      simpa [iteratedDeriv_succ] using this
  have key : ∀ k : ℕ, ∀ᶠ y in 𝓝 (0 : ℝ),
      iteratedDeriv k (fun s : ℝ => (ψ s : ℂ)) y = ((iteratedDeriv k ψ y : ℝ) : ℂ) := by
    intro k
    induction k with
    | zero => exact Filter.Eventually.of_forall fun y => by simp
    | succ k ih =>
      filter_upwards [ih.eventually_nhds, (hAk k).eventually_nhds] with y hy hA
      have hd : DifferentiableAt ℝ (iteratedDeriv k ψ) y := (hA.self_of_nhds).differentiableAt
      have hev : iteratedDeriv k (fun s : ℝ => (ψ s : ℂ)) =ᶠ[𝓝 y]
          fun s => ((iteratedDeriv k ψ s : ℝ) : ℂ) := hy
      rw [iteratedDeriv_succ, hev.deriv_eq, iteratedDeriv_succ]
      exact (hd.hasDerivAt.ofReal_comp).deriv
  exact (key k).self_of_nhds

/-- The uniform Schwarz bound along a ray: a holomorphic function on a disc, bounded by `M`, which
restricts on the real axis to an analytic function with vanishing jet of order `≤ 3`. -/
theorem uniform_ray_bound {r M : ℝ} (hr : 0 < r) (hM : 0 ≤ M) {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g (ball 0 r)) (hb : ∀ z ∈ ball (0 : ℂ) r, ‖g z‖ ≤ M) {ψ : ℝ → ℝ}
    (hψa : AnalyticAt ℝ ψ 0) (hψ : (fun s : ℝ => g s) =ᶠ[𝓝 0] fun s => (ψ s : ℂ))
    (hjet : ∀ k : ℕ, k ≤ 3 → iteratedDeriv k ψ 0 = 0) :
    ∀ z ∈ ball (0 : ℂ) r, ‖g z‖ ≤ M / r ^ 4 * ‖z‖ ^ 4 := by
  refine schwarz_order_four hr hM hg hb fun k hk => ?_
  have h0 : ((0 : ℝ) : ℂ) ∈ ball (0 : ℂ) r := by simpa using hr
  rw [← Complex.ofReal_zero, ← iteratedDeriv_ofReal isOpen_ball hg k h0,
    hψ.iteratedDeriv_eq k, iteratedDeriv_ofReal_comp hψa k, hjet k hk]

end SecularForm
end KAM.Planetary
end
