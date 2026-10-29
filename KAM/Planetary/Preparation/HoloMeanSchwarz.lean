/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Preparation.Schwarz

/-!
# Jets from real bounds and the diagonal Schwarz lemma (P11A-P2e, `stepP:p11:hc-mean`)

Helpers of the proof of `hc-mean` (jets of the fast mean vanish to order `3`, hence the Schwarz
bound `M (‖z‖/r)⁴`):

* `p11_iteratedDeriv_eq_factorial_dslope`: `g⁽ʲ⁾(0) = j! · (dslope⁽ʲ⁾ g)(0)`;
* `p11_jets_zero_of_real_bound`: a holomorphic `g : ℂ → ℂ` with `‖g t‖ ≤ C |t|^k` along the real
  axis has vanishing jets of order `< k` at `0`;
* `p11_radial_schwarz_diag`: the radial Schwarz lemma on an arbitrary complex normed space, with
  the hypothesis on the diagonal values `D^j F(0)(v, …, v)` only (the form produced by the
  identity theorem; the signed `p11_radial_schwarz` is the same statement on `Fin n → ℂ`).
-/

@[expose] public noncomputable section
open Set Filter Metric
open scoped Topology Nat
namespace KAM.Planetary

/-- The `j`-th derivative at `0` is `j!` times the `j`-fold `dslope` value. -/
theorem p11_iteratedDeriv_eq_factorial_dslope {g : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hg : DifferentiableOn ℂ g (ball 0 R)) (j : ℕ) :
    iteratedDeriv j g 0 = (j ! : ℂ) * ((Function.swap dslope (0 : ℂ))^[j] g) 0 := by
  obtain ⟨p, r, hp⟩ := hg.analyticOnNhd isOpen_ball 0 (mem_ball_self hR)
  have h1 := (HasFPowerSeriesAt.has_fpower_series_iterate_dslope_fslope j ⟨r, hp⟩).coeff_zero 1
  rw [← h1, ← FormalMultilinearSeries.coeff, FormalMultilinearSeries.coeff_iterate_fslope,
    zero_add]
  have h2 := hp.factorial_smul 1 j
  rw [iteratedDeriv_eq_iteratedFDeriv, ← h2]
  simp [nsmul_eq_mul]

/-- A holomorphic function that is `O(|t|^k)` along the real axis has vanishing jets of order
`< k` at `0`. -/
theorem p11_jets_zero_of_real_bound {g : ℂ → ℂ} {R C δ : ℝ} (hR : 0 < R)
    (hg : DifferentiableOn ℂ g (ball 0 R)) (hδ : 0 < δ) {k : ℕ}
    (hb : ∀ t : ℝ, |t| < δ → ‖g (t : ℂ)‖ ≤ C * |t| ^ k) :
    ∀ j < k, iteratedDeriv j g 0 = 0 := by
  have hdiff : ∀ m, DifferentiableOn ℂ ((Function.swap dslope (0 : ℂ))^[m] g) (ball 0 R) := by
    intro m
    induction m with
    | zero => exact hg
    | succ m ih =>
      rw [Function.iterate_succ_apply']
      exact (Complex.differentiableOn_dslope (isOpen_ball.mem_nhds (mem_ball_self hR))).mpr ih
  have key : ∀ m, m ≤ k → ∀ j < m, ((Function.swap dslope (0 : ℂ))^[j] g) 0 = 0 := by
    intro m
    induction m with
    | zero => intro _ j hj; omega
    | succ m ih =>
      intro hmk j hj
      have ih' := ih (by omega)
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hjm | hjm
      · exact ih' j hjm
      rw [hjm]
      set hm := (Function.swap dslope (0 : ℂ))^[m] g with hhm
      have hfac : ∀ ζ, g ζ = ζ ^ m * hm ζ := fun ζ => by
        simpa [hhm] using
          (pow_sub_smul_iterate_dslope_of_zero m (p11_iterate_dslope_zero hR hg
            (fun j hj => by
              rw [p11_iteratedDeriv_eq_factorial_dslope hR hg j, ih' j hj, mul_zero])) ζ).symm
      have hcont : ContinuousAt hm 0 :=
        ((hdiff m).differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hR))).continuousAt
      have hlim : Filter.Tendsto (fun t : ℝ => ‖hm (t : ℂ)‖) (𝓝[≠] 0) (𝓝 ‖hm 0‖) := by
        have h1 : Filter.Tendsto (fun t : ℝ => (t : ℂ)) (𝓝[≠] 0) (𝓝 0) :=
          (Complex.continuous_ofReal.tendsto' 0 0 (by simp)).mono_left nhdsWithin_le_nhds
        exact (hcont.tendsto.comp h1).norm
      have hlim0 : Filter.Tendsto (fun t : ℝ => C * |t| ^ (k - m)) (𝓝[≠] 0) (𝓝 0) := by
        have : Filter.Tendsto (fun t : ℝ => C * |t| ^ (k - m)) (𝓝 0) (𝓝 (C * |0| ^ (k - m))) :=
          (continuous_const.mul (continuous_abs.pow _)).tendsto 0
        rw [abs_zero, zero_pow (by omega), mul_zero] at this
        exact this.mono_left nhdsWithin_le_nhds
      have hev : ∀ᶠ t : ℝ in 𝓝[≠] 0, ‖hm (t : ℂ)‖ ≤ C * |t| ^ (k - m) := by
        have h1 : ∀ᶠ t : ℝ in 𝓝 0, |t| < min δ R := by
          have : (0 : ℝ) ∈ {t : ℝ | |t| < min δ R} :=
            by simpa using lt_min hδ hR
          exact (isOpen_lt continuous_abs continuous_const).mem_nhds this
        filter_upwards [nhdsWithin_le_nhds h1, self_mem_nhdsWithin] with t ht ht0
        have ht0' : t ≠ 0 := ht0
        have hpos : 0 < |t| := abs_pos.2 ht0'
        have hgt := hb t (lt_of_lt_of_le ht (min_le_left _ _))
        rw [hfac (t : ℂ), norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs] at hgt
        have hpm : 0 < |t| ^ m := pow_pos hpos m
        have : |t| ^ m * ‖hm (t : ℂ)‖ ≤ |t| ^ m * (C * |t| ^ (k - m)) := by
          calc |t| ^ m * ‖hm (t : ℂ)‖ ≤ C * |t| ^ k := hgt
            _ = |t| ^ m * (C * |t| ^ (k - m)) := by
              rw [show k = m + (k - m) by omega, pow_add]
              simp only [Nat.add_sub_cancel_left]
              ring
        exact le_of_mul_le_mul_left this hpm
      have hle : ‖hm 0‖ ≤ 0 := le_of_tendsto_of_tendsto hlim hlim0 hev
      exact norm_le_zero_iff.1 hle
  intro j hj
  rw [p11_iteratedDeriv_eq_factorial_dslope hR hg j, key k le_rfl j hj, mul_zero]

/-- The radial Schwarz lemma of order `k` on a complex normed space, with the jet hypothesis on
the diagonal values (`hc-mean`; the statement of `p11_radial_schwarz`). -/
theorem p11_radial_schwarz_diag {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] {r M : ℝ} (hr : 0 < r) {F : E → ℂ}
    (hF : DifferentiableOn ℂ F (Metric.ball 0 r)) (hb : ∀ z ∈ Metric.ball (0 : E) r, ‖F z‖ ≤ M)
    {k : ℕ}
    (hj : ∀ j < k, ∀ v ∈ Metric.ball (0 : E) r, iteratedFDeriv ℂ j F 0 (fun _ => v) = 0) :
    ∀ z ∈ Metric.ball (0 : E) r, ‖F z‖ ≤ M * (‖z‖ / r) ^ k := by
  intro z hz
  have hzr : ‖z‖ < r := mem_ball_zero_iff.mp hz
  by_cases hz0 : z = 0
  · subst hz0
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simpa using hb 0 hz
    · have h0 : F 0 = 0 := by
        have := hj 0 hk 0 (mem_ball_self hr)
        simpa using this
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
    have := iteratedDeriv_line_eq_iteratedFDeriv (isOpen_ball (x := (0 : E)) (ε := r))
      hF (mem_ball_self hr) z j
    simp only [zero_add] at this
    rw [this, hj j hjk z hz]
  have h1 : (1 : ℂ) ∈ ball (0 : ℂ) R := by
    rw [mem_ball_zero_iff, norm_one, hR, lt_div_iff₀ hzn]; linarith
  have key := p11_schwarz_one hR0 hg (fun ζ hζ => hb _ (hline ζ hζ)) hjg
    (w := 1) (mem_ball_zero_iff.mp h1)
  simpa [hR, div_div_eq_mul_div, mul_comm] using key

end KAM.Planetary

end
