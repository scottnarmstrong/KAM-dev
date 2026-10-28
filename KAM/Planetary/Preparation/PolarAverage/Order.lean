/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Strip.AnalyticTaylor
public import KAM.Planetary.Preparation.Schwarz

/-!
# Vanishing order from decay, and radial Schwarz on a product (P11A-P6 helper)

* `p11_vanish_of_decay`: a holomorphic `g` on a disc with `‖g t‖ ≤ C √t^k` for small `t > 0`
  has vanishing derivatives of order `j` with `2 j < k` at `0` (factor out the lowest power).
* `p11_radial_schwarz_gen`: the radial Schwarz lemma of `P11A-P0` (`p11_radial_schwarz`) on an
  arbitrary finite-dimensional complex normed space, used on the phase product `ℂⁿ × ℂⁿ`.
-/

@[expose] public noncomputable section

open Set Filter Metric
open scoped Topology Nat

namespace KAM.Planetary

/-- The `j`-fold `dslope` at `0` is the `j`-th Taylor coefficient. -/
theorem p11_iterate_dslope_coeff {g : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hg : DifferentiableOn ℂ g (ball 0 R)) (j : ℕ) :
    (j ! : ℂ) * (Function.swap dslope (0 : ℂ))^[j] g 0 = iteratedDeriv j g 0 := by
  obtain ⟨p, r, hp⟩ := hg.analyticOnNhd isOpen_ball 0 (mem_ball_self hR)
  have h1 := (HasFPowerSeriesAt.has_fpower_series_iterate_dslope_fslope j ⟨r, hp⟩).coeff_zero 1
  rw [← h1, ← FormalMultilinearSeries.coeff, FormalMultilinearSeries.coeff_iterate_fslope,
    zero_add]
  have h2 := hp.factorial_smul 1 j
  rw [iteratedDeriv_eq_iteratedFDeriv, ← h2, nsmul_eq_mul]
  rfl

theorem p11_differentiableOn_iterate_dslope {g : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hg : DifferentiableOn ℂ g (ball 0 R)) (j : ℕ) :
    DifferentiableOn ℂ ((Function.swap dslope (0 : ℂ))^[j] g) (ball 0 R) := by
  induction j with
  | zero => exact hg
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact (Complex.differentiableOn_dslope (isOpen_ball.mem_nhds (mem_ball_self hR))).mpr ih

/-- Decay `‖g t‖ ≤ C √t^k` along small positive reals forces vanishing of the derivatives of
order `j` with `2 j < k`. -/
theorem p11_vanish_of_decay {g : ℂ → ℂ} {R C : ℝ} (hR : 0 < R)
    (hg : DifferentiableOn ℂ g (ball 0 R)) {k : ℕ}
    (hdec : ∀ t : ℝ, 0 < t → t < R → ‖g t‖ ≤ C * Real.sqrt t ^ k) :
    ∀ j : ℕ, 2 * j < k → iteratedDeriv j g 0 = 0 := by
  by_contra hcon
  push Not at hcon
  classical
  have hex : ∃ j : ℕ, 2 * j < k ∧ iteratedDeriv j g 0 ≠ 0 := hcon
  set j0 := Nat.find hex with hj0
  obtain ⟨hj0k, hj0ne⟩ := Nat.find_spec hex
  have hlow : ∀ i < j0, iteratedDeriv i g 0 = 0 := by
    intro i hi
    by_contra hne
    exact Nat.find_min hex hi ⟨by omega, hne⟩
  have hzero := p11_iterate_dslope_zero hR hg hlow
  set h := (Function.swap dslope (0 : ℂ))^[j0] g with hh
  have hfac : ∀ ζ, g ζ = ζ ^ j0 * h ζ := fun ζ => by
    simpa [hh] using (pow_sub_smul_iterate_dslope_of_zero j0 hzero ζ).symm
  have hhd : DifferentiableOn ℂ h (ball 0 R) := p11_differentiableOn_iterate_dslope hR hg j0
  have hh0 : h 0 ≠ 0 := by
    intro h0
    have := p11_iterate_dslope_coeff hR hg j0
    rw [← hh, h0, mul_zero] at this
    exact hj0ne this.symm
  have hcont : Tendsto (fun t : ℝ => h (t : ℂ)) (𝓝[>] 0) (𝓝 (h 0)) := by
    have hc : ContinuousAt h 0 := hhd.continuousOn.continuousAt (isOpen_ball.mem_nhds (mem_ball_self hR))
    have := (hc.comp (f := fun t : ℝ => (t : ℂ)) (by simpa using Complex.continuous_ofReal.continuousAt)).tendsto
    exact this.mono_left nhdsWithin_le_nhds
  obtain ⟨e, he⟩ : ∃ e : ℕ, k = e + 1 + 2 * j0 := ⟨k - 2 * j0 - 1, by omega⟩
  have hbound : ∀ᶠ t : ℝ in 𝓝[>] 0, ‖h (t : ℂ)‖ ≤ C * Real.sqrt t ^ (e + 1) := by
    filter_upwards [Ioo_mem_nhdsGT hR] with t ht
    have ht0 : 0 < t := ht.1
    have h1 := hdec t ht0 ht.2
    rw [hfac, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg ht0.le, he, pow_add,
      pow_mul, Real.sq_sqrt ht0.le] at h1
    have h2 : t ^ j0 * ‖h (t : ℂ)‖ ≤ t ^ j0 * (C * Real.sqrt t ^ (e + 1)) := by
      calc t ^ j0 * ‖h (t : ℂ)‖ ≤ C * (Real.sqrt t ^ (e + 1) * t ^ j0) := h1
        _ = t ^ j0 * (C * Real.sqrt t ^ (e + 1)) := by ring
    exact le_of_mul_le_mul_left h2 (pow_pos ht0 j0)
  have hlim : Tendsto (fun t : ℝ => C * Real.sqrt t ^ (e + 1)) (𝓝[>] 0) (𝓝 0) := by
    have : Continuous fun t : ℝ => C * Real.sqrt t ^ (e + 1) := by fun_prop
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  have hn : ‖h 0‖ ≤ 0 :=
    le_of_tendsto_of_tendsto hcont.norm hlim hbound
  exact hh0 (norm_le_zero_iff.mp hn)

/-- Radial Schwarz on a finite-dimensional complex normed space. -/
theorem p11_radial_schwarz_gen {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] {k : ℕ} {r M : ℝ} (hr : 0 < r) {F : E → ℂ}
    (hF : DifferentiableOn ℂ F (Metric.ball 0 r)) (hb : ∀ z ∈ Metric.ball (0 : E) r, ‖F z‖ ≤ M)
    (hj : ∀ j < k, iteratedFDeriv ℂ j F 0 = 0) :
    ∀ z ∈ Metric.ball (0 : E) r, ‖F z‖ ≤ M * (‖z‖ / r) ^ k := by
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
  have hline : ∀ ζ ∈ ball (0 : ℂ) R, ζ • z ∈ Metric.ball (0 : E) r := by
    intro ζ hζ
    rw [mem_ball_zero_iff, norm_smul]
    have := mem_ball_zero_iff.mp hζ
    rwa [hR, lt_div_iff₀ hzn] at this
  have hg : DifferentiableOn ℂ (fun ζ : ℂ => F (ζ • z)) (ball 0 R) :=
    hF.comp ((differentiable_id.smul_const z).differentiableOn) hline
  have hjg : ∀ j < k, iteratedDeriv j (fun ζ : ℂ => F (ζ • z)) 0 = 0 := by
    intro j hjk
    have := KAM.iteratedDeriv_line_eq_iteratedFDeriv (isOpen_ball (x := (0 : E)) (ε := r))
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
