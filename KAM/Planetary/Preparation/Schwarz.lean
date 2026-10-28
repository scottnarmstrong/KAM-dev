/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Strip.AnalyticTaylor
public import KAM.Planetary.MaximalStep.Basic

/-!
# Higher-order Schwarz lemma on complex radial lines (P11A-P0, `stepP:p11:hc-mean`)

If `F` is holomorphic on the ball `B(0,r) ⊆ ℂⁿ`, bounded by `M` there and its jets of order `< k`
vanish at `0`, then `‖F z‖ ≤ M (‖z‖/r)^k`.

The one-variable statement `p11_schwarz_one` factors `g = ζ^k h` with `h` the `k`-fold `dslope`
(Mathlib `pow_sub_smul_iterate_dslope_of_zero`), bounds `h` by the maximum modulus principle on
circles of radius `ρ < R`, and lets `ρ → R`. The several-variable statement restricts to the line
`ζ ↦ F (ζ • z)` (`iteratedDeriv_line_eq_iteratedFDeriv`).
-/

@[expose] public noncomputable section
open Set Filter Metric
open scoped Topology Nat
namespace KAM.Planetary

/-- The first `k` iterated `dslope`s at `0` vanish when the first `k` derivatives do. -/
theorem p11_iterate_dslope_zero {g : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hg : DifferentiableOn ℂ g (ball 0 R)) {k : ℕ}
    (hj : ∀ j < k, iteratedDeriv j g 0 = 0) :
    ∀ j < k, (Function.swap dslope (0 : ℂ))^[j] g 0 = 0 := by
  intro j hjk
  obtain ⟨p, r, hp⟩ := hg.analyticOnNhd isOpen_ball 0 (mem_ball_self hR)
  have h1 := (HasFPowerSeriesAt.has_fpower_series_iterate_dslope_fslope j ⟨r, hp⟩).coeff_zero 1
  rw [← h1, ← FormalMultilinearSeries.coeff, FormalMultilinearSeries.coeff_iterate_fslope,
    zero_add]
  have h2 := hp.factorial_smul 1 j
  have h4 : iteratedFDeriv ℂ j g 0 (fun _ => (1 : ℂ)) = 0 := hj j hjk
  rw [h4] at h2
  have h5 : j ! • p.coeff j = 0 := h2
  exact (smul_eq_zero.mp h5).resolve_left (Nat.factorial_ne_zero j)

/-- One-variable Schwarz lemma of order `k`. -/
theorem p11_schwarz_one {g : ℂ → ℂ} {R M : ℝ} (hR : 0 < R)
    (hg : DifferentiableOn ℂ g (ball 0 R)) (hb : ∀ ζ ∈ ball (0 : ℂ) R, ‖g ζ‖ ≤ M) {k : ℕ}
    (hj : ∀ j < k, iteratedDeriv j g 0 = 0) {w : ℂ} (hw : ‖w‖ < R) :
    ‖g w‖ ≤ M * (‖w‖ / R) ^ k := by
  set h := (Function.swap dslope (0 : ℂ))^[k] g with hh_def
  have hfac : ∀ ζ, g ζ = ζ ^ k * h ζ := fun ζ => by
    simpa [hh_def] using
      (pow_sub_smul_iterate_dslope_of_zero k (p11_iterate_dslope_zero hR hg hj) ζ).symm
  have hh : DifferentiableOn ℂ h (ball 0 R) := by
    have : ∀ n, DifferentiableOn ℂ ((Function.swap dslope (0 : ℂ))^[n] g) (ball 0 R) := by
      intro n
      induction n with
      | zero => exact hg
      | succ n ih =>
        rw [Function.iterate_succ_apply']
        exact (Complex.differentiableOn_dslope (isOpen_ball.mem_nhds (mem_ball_self hR))).mpr ih
    exact this k
  have hρ : ∀ ρ, ‖w‖ < ρ → ρ < R → ‖g w‖ ≤ M * (‖w‖ / ρ) ^ k := by
    intro ρ hwρ hρR
    have hρ0 : 0 < ρ := lt_of_le_of_lt (norm_nonneg w) hwρ
    have hcl : closure (ball (0 : ℂ) ρ) ⊆ ball 0 R := by
      rw [closure_ball 0 hρ0.ne']
      exact closedBall_subset_ball hρR
    have hbd : ‖h w‖ ≤ M / ρ ^ k := by
      refine Complex.norm_le_of_forall_mem_frontier_norm_le (U := ball (0 : ℂ) ρ)
        isBounded_ball ((hh.mono hcl).diffContOnCl) (fun ζ hζ => ?_)
        (subset_closure (mem_ball_zero_iff.mpr hwρ))
      rw [frontier_ball 0 hρ0.ne'] at hζ
      have hζn : ‖ζ‖ = ρ := by simpa using hζ
      have hζR : ζ ∈ ball (0 : ℂ) R := mem_ball_zero_iff.mpr (hζn ▸ hρR)
      have := hb ζ hζR
      rw [hfac ζ, norm_mul, norm_pow, hζn] at this
      rw [le_div_iff₀ (pow_pos hρ0 k)]
      linarith [mul_comm (ρ ^ k) ‖h ζ‖]
    rw [hfac w, norm_mul, norm_pow, div_pow, ← mul_div_assoc, mul_comm M, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hbd (pow_nonneg (norm_nonneg w) k)
  have hcont : Tendsto (fun ρ : ℝ => M * (‖w‖ / ρ) ^ k) (𝓝[<] R) (𝓝 (M * (‖w‖ / R) ^ k)) :=
    ((continuousAt_const.mul ((continuousAt_const.div continuousAt_id hR.ne').pow k)).tendsto
      ).mono_left nhdsWithin_le_nhds
  exact ge_of_tendsto hcont (by
    filter_upwards [Ioo_mem_nhdsLT hw] with ρ hρm using hρ ρ hρm.1 hρm.2)

/-- hc-mean: higher order Schwarz on complex radial lines. -/
theorem p11_radial_schwarz {n k : ℕ} {r M : ℝ} (hr : 0 < r) (hM : 0 ≤ M)
    {F : P11CVec n → ℂ} (hF : DifferentiableOn ℂ F (Metric.ball 0 r))
    (hb : p11Bound (Metric.ball 0 r) F M)
    (hj : ∀ j < k, iteratedFDeriv ℂ j F 0 = 0) :
    ∀ z ∈ Metric.ball 0 r, ‖F z‖ ≤ M * (‖z‖ / r) ^ k := by
  intro z hz
  have hzr : ‖z‖ < r := mem_ball_zero_iff.mp hz
  by_cases hz0 : z = 0
  · subst hz0
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simpa using hb 0 hz
    · have h0 : F 0 = 0 := by
        have := hj 0 hk
        rw [← norm_eq_zero, ← norm_iteratedFDeriv_zero (𝕜 := ℂ) (f := F) (x := 0)]
        simp [this]
      simp [h0, zero_pow hk.ne']
  have hzn : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  set R : ℝ := r / ‖z‖ with hR
  have hR0 : 0 < R := div_pos hr hzn
  have hline : ∀ ζ ∈ ball (0 : ℂ) R, ζ • z ∈ Metric.ball (0 : P11CVec n) r := by
    intro ζ hζ
    rw [mem_ball_zero_iff, norm_smul]
    have := mem_ball_zero_iff.mp hζ
    rwa [hR, lt_div_iff₀ hzn] at this
  have hg : DifferentiableOn ℂ (fun ζ : ℂ => F (ζ • z)) (ball 0 R) :=
    hF.comp ((differentiable_id.smul_const z).differentiableOn) hline
  have hjg : ∀ j < k, iteratedDeriv j (fun ζ : ℂ => F (ζ • z)) 0 = 0 := by
    intro j hjk
    have := iteratedDeriv_line_eq_iteratedFDeriv (isOpen_ball (x := (0 : P11CVec n)) (ε := r))
      hF (mem_ball_self hr) z j
    simp only [zero_add] at this
    rw [this, hj j hjk]
    rfl
  have h1 : (1 : ℂ) ∈ ball (0 : ℂ) R := by
    rw [mem_ball_zero_iff, norm_one, hR, lt_div_iff₀ hzn]; linarith
  have key := p11_schwarz_one hR0 hg (fun ζ hζ => hb _ (hline ζ hζ)) hjg
    (w := 1) (mem_ball_zero_iff.mp h1)
  simpa [hR, div_div_eq_mul_div, mul_comm] using key

end KAM.Planetary
