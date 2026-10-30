/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import KAM.Wave.Normal.Analysis.PdeBase
public import KAM.Wave.Normal.Analysis.SineSeries

/-!
# Classical solutions give the coefficient system (blueprint `bpW:w0n:pde-equiv`, part (ii))

Infrastructure used by several nodes; this is off the frontier: the dependency graph is still
being built.

* `KAM.Wave.waveParam_hasDerivAt`: differentiation (and continuity) of `t ↦ ∫₀^π F(t,x) dx` under
  the integral sign, for `F` jointly continuous on `I × [0,π]` with continuous `∂_t F`;
* `KAM.Wave.wave_pde_to_coeff` (blueprint `bpW:w0n:pde-equiv`, (ii), `stepW:w0n:converse`): if
  `u(t,x) = U_m(q(t))(x)` is a classical solution on the open set `I` with `u_t = V_m(p(t))`, then
  every `q_j, p_j` is `C¹` on `I` and `q̇_j = λ_j p_j`, `ṗ_j = -λ_j q_j - 𝒢(q)_j`.
-/

@[expose] public noncomputable section

open Real MeasureTheory Set
open scoped Topology Interval

namespace KAM.Wave

lemma waveParam_hasDerivAt {I : Set ℝ} (hI : IsOpen I) {F F' : ℝ → ℝ → ℝ}
    (hF : ContinuousOn (Function.uncurry F) (I ×ˢ Icc 0 π))
    (hF' : ContinuousOn (Function.uncurry F') (I ×ˢ Icc 0 π))
    (hd : ∀ t ∈ I, ∀ x ∈ Icc 0 π, HasDerivAt (fun s => F s x) (F' t x) t) {t₀ : ℝ} (ht₀ : t₀ ∈ I) :
    HasDerivAt (fun s => ∫ x in (0 : ℝ)..π, F s x) (∫ x in (0 : ℝ)..π, F' t₀ x) t₀ ∧
      ContinuousAt (fun s => ∫ x in (0 : ℝ)..π, F' s x) t₀ := by
  have hpi := Real.pi_pos
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hI t₀ ht₀
  set r := ε / 2 with hr
  have hrpos : 0 < r := by positivity
  have hK : IsCompact (Metric.closedBall t₀ r ×ˢ Icc (0 : ℝ) π) :=
    (isCompact_closedBall _ _).prod isCompact_Icc
  have hKsub : Metric.closedBall t₀ r ×ˢ Icc (0 : ℝ) π ⊆ I ×ˢ Icc 0 π := fun p hp =>
    ⟨hball (Metric.closedBall_subset_ball (by rw [hr]; linarith) hp.1), hp.2⟩
  obtain ⟨C', hC'⟩ := hK.exists_bound_of_continuousOn (hF'.mono hKsub)
  have hballI : Metric.ball t₀ r ⊆ I := fun s hs =>
    hball (Metric.ball_subset_ball (by rw [hr]; linarith) hs)
  have hmeas : ∀ (G : ℝ → ℝ → ℝ), ContinuousOn (Function.uncurry G) (I ×ˢ Icc 0 π) →
      ∀ s ∈ I, AEStronglyMeasurable (G s) (volume.restrict (Ι (0 : ℝ) π)) := by
    intro G hG s hs
    have hc : ContinuousOn (G s) (Icc 0 π) := by
      have := hG.comp (continuousOn_const.prodMk continuousOn_id)
        (fun x hx => (⟨hs, hx⟩ : (s, x) ∈ I ×ˢ Icc 0 π))
      exact this
    rw [Set.uIoc_of_le hpi.le]
    exact (hc.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  have hint : ∀ (G : ℝ → ℝ → ℝ), ContinuousOn (Function.uncurry G) (I ×ˢ Icc 0 π) →
      ∀ s ∈ I, IntervalIntegrable (G s) volume 0 π := by
    intro G hG s hs
    have hc : ContinuousOn (G s) (Icc 0 π) :=
      hG.comp (continuousOn_const.prodMk continuousOn_id)
        (fun x hx => (⟨hs, hx⟩ : (s, x) ∈ I ×ˢ Icc 0 π))
    exact hc.intervalIntegrable_of_Icc hpi.le
  have hbound : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ Ι (0 : ℝ) π → ∀ s ∈ Metric.ball t₀ r, ‖F' s x‖ ≤
      C' := by
    refine Filter.Eventually.of_forall fun x hx s hs => ?_
    rw [Set.uIoc_of_le hpi.le] at hx
    exact hC' (s, x) ⟨Metric.ball_subset_closedBall hs, Ioc_subset_Icc_self hx⟩
  have hev : ∀ᶠ s in 𝓝 t₀, s ∈ I := hI.mem_nhds ht₀
  refine ⟨?_, ?_⟩
  · exact (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (Metric.ball_mem_nhds t₀ hrpos)
      (hev.mono fun s hs => hmeas F hF s hs) (hint F hF t₀ ht₀) (hmeas F' hF' t₀ ht₀) hbound
      intervalIntegrable_const (Filter.Eventually.of_forall fun x hx s hs => by
        rw [Set.uIoc_of_le hpi.le] at hx
        exact hd s (hballI hs) x (Ioc_subset_Icc_self hx))).2
  · refine intervalIntegral.continuousAt_of_dominated_interval (bound := fun _ => C')
      (hev.mono fun s hs => hmeas F' hF' s hs) ?_ intervalIntegrable_const ?_
    · filter_upwards [Metric.ball_mem_nhds t₀ hrpos] with s hs
      exact Filter.Eventually.of_forall fun x hx => by
        rw [Set.uIoc_of_le hpi.le] at hx
        exact hC' (s, x) ⟨Metric.ball_subset_closedBall hs, Ioc_subset_Icc_self hx⟩
    · refine Filter.Eventually.of_forall fun x hx => ?_
      rw [Set.uIoc_of_le hpi.le] at hx
      have : ContinuousOn (fun s => F' s x) I :=
        hF'.comp (continuousOn_id.prodMk continuousOn_const)
          (fun s hs => (⟨hs, Ioc_subset_Icc_self hx⟩ : (s, x) ∈ I ×ˢ Icc 0 π))
      exact this.continuousAt (hI.mem_nhds ht₀)

lemma waveHasDerivAt_sineMode (l : ℕ+) (x : ℝ) :
    HasDerivAt (sineMode l) (Real.sqrt (2 / π) * ((l : ℝ) * Real.cos ((l : ℝ) * x))) x := by
  have h1 : HasDerivAt (fun y : ℝ => (l : ℝ) * y) (l : ℝ) x := by
    simpa using (hasDerivAt_id x).const_mul (l : ℝ)
  have h3 := (h1.sin).const_mul (Real.sqrt (2 / π))
  unfold sineMode
  refine h3.congr_deriv ?_
  ring

lemma waveHasDerivAt_sineMode_deriv (l : ℕ+) (x : ℝ) :
    HasDerivAt (fun y => Real.sqrt (2 / π) * ((l : ℝ) * Real.cos ((l : ℝ) * y)))
      (-((l : ℝ) ^ 2) * sineMode l x) x := by
  have h1 : HasDerivAt (fun y : ℝ => (l : ℝ) * y) (l : ℝ) x := by
    simpa using (hasDerivAt_id x).const_mul (l : ℝ)
  have h3 := ((h1.cos).const_mul (l : ℝ)).const_mul (Real.sqrt (2 / π))
  refine h3.congr_deriv ?_
  unfold sineMode
  ring

lemma waveSineMode_zero (l : ℕ+) : sineMode l 0 = 0 := by simp [sineMode]

lemma waveSineMode_pi (l : ℕ+) : sineMode l π = 0 := by
  have := Real.sin_nat_mul_pi (l : ℕ)
  simp [sineMode, this]

/-- Two integrations by parts: `∫₀^π f'' φ_l = -l² ∫₀^π f φ_l` for `f(0) = f(π) = 0`. -/
lemma wave_integral_second_deriv_mul {f f' f'' : ℝ → ℝ} (l : ℕ+)
    (hf0 : f 0 = 0) (hfπ : f π = 0)
    (hd1 : ∀ x ∈ Icc (0 : ℝ) π, HasDerivWithinAt f (f' x) (Icc 0 π) x)
    (hd2 : ∀ x ∈ Icc (0 : ℝ) π, HasDerivWithinAt f' (f'' x) (Icc 0 π) x)
    (hc1 : ContinuousOn f' (Icc 0 π)) (hc2 : ContinuousOn f'' (Icc 0 π)) :
    ∫ x in (0 : ℝ)..π, f'' x * sineMode l x
      = -((l : ℝ) ^ 2) * ∫ x in (0 : ℝ)..π, f x * sineMode l x := by
  have hpi := Real.pi_pos
  have hc0 : ContinuousOn f (Icc 0 π) := fun x hx => (hd1 x hx).continuousWithinAt
  have hφ : Continuous (sineMode l) := wave_continuous_sineMode l
  have hψ : Continuous fun y : ℝ => Real.sqrt (2 / π) * ((l : ℝ) * Real.cos ((l : ℝ) * y)) := by
    fun_prop
  set ψ : ℝ → ℝ := fun y => Real.sqrt (2 / π) * ((l : ℝ) * Real.cos ((l : ℝ) * y)) with hψd
  have hI : ∀ g : ℝ → ℝ, ContinuousOn g (Icc 0 π) → IntervalIntegrable g volume 0 π :=
    fun g hg => hg.intervalIntegrable_of_Icc hpi.le
  have hU : uIcc (0 : ℝ) π = Icc 0 π := Set.uIcc_of_le hpi.le
  have hint : ∀ x ∈ Ioo (min (0 : ℝ) π) (max 0 π), x ∈ Icc (0 : ℝ) π := fun x hx => by
    rw [min_eq_left hpi.le, max_eq_right hpi.le] at hx; exact Ioo_subset_Icc_self hx
  have hnhds : ∀ x ∈ Ioo (min (0 : ℝ) π) (max 0 π), Icc (0 : ℝ) π ∈ 𝓝 x := fun x hx => by
    rw [min_eq_left hpi.le, max_eq_right hpi.le] at hx; exact Icc_mem_nhds hx.1 hx.2
  have hA := intervalIntegral.integral_deriv_mul_eq_sub_of_hasDeriv_right
    (u := f') (u' := f'') (v := sineMode l) (v' := ψ) (a := 0) (b := π)
    (by rw [hU]; exact hc1) (by rw [hU]; exact hφ.continuousOn)
    (fun x hx => ((hd2 x (hint x hx)).hasDerivAt (hnhds x hx)).hasDerivWithinAt)
    (fun x hx => (waveHasDerivAt_sineMode l x).hasDerivWithinAt)
    (hI _ hc2) (hI _ hψ.continuousOn)
  have hB := intervalIntegral.integral_deriv_mul_eq_sub_of_hasDeriv_right
    (u := f) (u' := f') (v := ψ) (v' := fun y => -((l : ℝ) ^ 2) * sineMode l y) (a := 0) (b := π)
    (by rw [hU]; exact hc0) (by rw [hU]; exact hψ.continuousOn)
    (fun x hx => ((hd1 x (hint x hx)).hasDerivAt (hnhds x hx)).hasDerivWithinAt)
    (fun x hx => (waveHasDerivAt_sineMode_deriv l x).hasDerivWithinAt)
    (hI _ hc1) (hI _ (continuous_const.mul hφ).continuousOn)
  rw [waveSineMode_zero, waveSineMode_pi] at hA
  rw [hf0, hfπ] at hB
  simp only [mul_zero, sub_zero] at hA hB
  have e1 : ∫ x in (0 : ℝ)..π, (f'' x * sineMode l x + f' x * ψ x) =
      (∫ x in (0 : ℝ)..π, f'' x * sineMode l x) + ∫ x in (0 : ℝ)..π, f' x * ψ x :=
    intervalIntegral.integral_add (hI _ (hc2.mul hφ.continuousOn))
      (hI _ (hc1.mul hψ.continuousOn))
  have e2 : ∫ x in (0 : ℝ)..π, (f' x * ψ x + f x * (-((l : ℝ) ^ 2) * sineMode l x)) =
      (∫ x in (0 : ℝ)..π, f' x * ψ x) +
        -((l : ℝ) ^ 2) * ∫ x in (0 : ℝ)..π, f x * sineMode l x := by
    rw [intervalIntegral.integral_add (hI (fun x => f' x * ψ x) (hc1.mul hψ.continuousOn))
      (hI (fun x => f x * (-((l : ℝ) ^ 2) * sineMode l x))
        (hc0.mul (continuous_const.mul hφ).continuousOn)), ← intervalIntegral.integral_const_mul]
    congr 1
    exact intervalIntegral.integral_congr fun x _ => by ring
  linarith

lemma wave_summable_abs_sqrtLam_mul (m : ℝ) (hm : 0 < m) {c : ℕ+ → ℝ} (hc : WaveEll 1 1 c) :
    Summable fun j : ℕ+ => |Real.sqrt (lam m hm j) * c j| := by
  obtain ⟨hB, hν, h⟩ := polyBounded_betaV m hm
  have := (waveEll_mul_poly hB h hc).1
  have h2 := waveEll_summable_pow_mul one_pos this 0
  simpa [betaV] using h2

lemma wave_coeff_integral_u (m : ℝ) (hm : 0 < m) {c : ℕ+ → ℝ} (hc : WaveEll 1 1 c) (l : ℕ+) :
    ∫ x in (0 : ℝ)..π, waveU m hm c x * sineMode l x = waveHat m hm c l := by
  rw [waveU_eq_series]
  exact integral_waveSineSeries_mul_sineMode (summable_abs_waveHat m hm one_pos hc) l

lemma wave_coeff_integral_v (m : ℝ) (hm : 0 < m) {c : ℕ+ → ℝ} (hc : WaveEll 1 1 c) (l : ℕ+) :
    ∫ x in (0 : ℝ)..π, waveV m hm c x * sineMode l x = Real.sqrt (lam m hm l) * c l := by
  have : waveV m hm c = waveSineSeries 0 (fun j => Real.sqrt (lam m hm j) * c j) := by
    funext x
    rw [waveSineSeries_zero_eq]
    rfl
  rw [this]
  exact integral_waveSineSeries_mul_sineMode (wave_summable_abs_sqrtLam_mul m hm hc) l

/-- The pointwise content of `bpW:w0n:pde-equiv` (ii) for one coordinate `l` and one time `t₀`. -/
lemma wave_converse_pointwise (m : ℝ) (hm : 0 < m) {I : Set ℝ} (hI : IsOpen I)
    {q p : ℝ → ℕ+ → ℝ}
    (hq : ∀ t ∈ I, WaveEll 1 1 (q t)) (hp : ∀ t ∈ I, WaveEll 1 1 (p t))
    {ut ux utt uxx : ℝ → ℝ → ℝ}
    (hsol : IsClassicalSolutionWith m (fun t x => waveU m hm (q t) x) ut ux utt uxx I)
    (hut : ∀ t ∈ I, ∀ x ∈ Icc 0 π, ut t x = waveV m hm (p t) x) (l : ℕ+) {t₀ : ℝ} (ht₀ : t₀ ∈ I) :
    HasDerivAt (fun s => q s l) (lam m hm l * p t₀ l) t₀ ∧
      HasDerivAt (fun s => p s l)
        ((Real.sqrt (lam m hm l))⁻¹ * ∫ x in (0 : ℝ)..π, utt t₀ x * sineMode l x) t₀ ∧
      (Real.sqrt (lam m hm l))⁻¹ * ∫ x in (0 : ℝ)..π, utt t₀ x * sineMode l x
        = -(lam m hm l * q t₀ l) - waveCubic m hm (q t₀) l ∧
      ContinuousAt (fun s => (Real.sqrt (lam m hm l))⁻¹ *
        ∫ x in (0 : ℝ)..π, utt s x * sineMode l x) t₀ := by
  have hpi := Real.pi_pos
  obtain ⟨hcont, hder, hbd⟩ := hsol
  have hu_c := hcont (Function.uncurry fun t x => waveU m hm (q t) x) (by simp)
  have hut_c := hcont (Function.uncurry ut) (by simp)
  have hux_c := hcont (Function.uncurry ux) (by simp)
  have hutt_c := hcont (Function.uncurry utt) (by simp)
  have huxx_c := hcont (Function.uncurry uxx) (by simp)
  have hφc : ContinuousOn (fun z : ℝ × ℝ => sineMode l z.2) (I ×ˢ Icc 0 π) :=
    ((wave_continuous_sineMode l).comp continuous_snd).continuousOn
  have hslice : ∀ F : ℝ → ℝ → ℝ, ContinuousOn (Function.uncurry F) (I ×ˢ Icc 0 π) →
      ∀ t ∈ I, ContinuousOn (F t) (Icc 0 π) := fun F hF t ht =>
    hF.comp (continuousOn_const.prodMk continuousOn_id)
      (fun x hx => (⟨ht, hx⟩ : (t, x) ∈ I ×ˢ Icc 0 π))
  have hs0 : 0 < Real.sqrt (lam m hm l) := wave_sqrt_lam_pos m hm l
  have hss : Real.sqrt (lam m hm l) * Real.sqrt (lam m hm l) = lam m hm l :=
    Real.mul_self_sqrt (by have := one_le_lam m hm l; linarith)
  have hev : ∀ᶠ s in 𝓝 t₀, s ∈ I := hI.mem_nhds ht₀
  -- first application: `u → u_t`
  have P1 := (waveParam_hasDerivAt hI (F := fun s x => waveU m hm (q s) x * sineMode l x)
    (F' := fun s x => ut s x * sineMode l x) (hu_c.mul hφc) (hut_c.mul hφc)
    (fun t ht x hx => (hder t ht x hx).1.mul_const _) ht₀).1
  have hA : HasDerivAt (fun s => waveHat m hm (q s) l) (Real.sqrt (lam m hm l) * p t₀ l) t₀ := by
    have hv : ∫ x in (0 : ℝ)..π, ut t₀ x * sineMode l x
        = Real.sqrt (lam m hm l) * p t₀ l := by
      rw [← wave_coeff_integral_v m hm (hp t₀ ht₀) l]
      refine intervalIntegral.integral_congr fun x hx => ?_
      rw [Set.uIcc_of_le hpi.le] at hx
      simp only [hut t₀ ht₀ x hx]
    rw [← hv]
    refine P1.congr_of_eventuallyEq ?_
    filter_upwards [hev] with s hs
    exact (wave_coeff_integral_u m hm (hq s hs) l).symm
  have hq' : HasDerivAt (fun s => q s l) (lam m hm l * p t₀ l) t₀ := by
    have := hA.const_mul (Real.sqrt (lam m hm l))
    refine (this.congr_deriv (by rw [← mul_assoc, hss])).congr_of_eventuallyEq ?_
    refine Filter.Eventually.of_forall fun s => ?_
    simp only [waveHat]
    field_simp
  -- second application: `u_t → u_tt`
  obtain ⟨P2, P2c⟩ := waveParam_hasDerivAt hI (F := fun s x => ut s x * sineMode l x)
    (F' := fun s x => utt s x * sineMode l x) (hut_c.mul hφc) (hutt_c.mul hφc)
    (fun t ht x hx => (hder t ht x hx).2.1.mul_const _) ht₀
  have hB : HasDerivAt (fun s => p s l)
      ((Real.sqrt (lam m hm l))⁻¹ * ∫ x in (0 : ℝ)..π, utt t₀ x * sineMode l x) t₀ := by
    have h1 := P2.const_mul (Real.sqrt (lam m hm l))⁻¹
    refine h1.congr_of_eventuallyEq ?_
    filter_upwards [hev] with s hs
    have : ∫ x in (0 : ℝ)..π, ut s x * sineMode l x = Real.sqrt (lam m hm l) * p s l := by
      rw [← wave_coeff_integral_v m hm (hp s hs) l]
      refine intervalIntegral.integral_congr fun x hx => ?_
      rw [Set.uIcc_of_le hpi.le] at hx
      simp only [hut s hs x hx]
    simp only [this]
    field_simp
  -- the value of the second derivative
  have hval : (Real.sqrt (lam m hm l))⁻¹ * ∫ x in (0 : ℝ)..π, utt t₀ x * sineMode l x
      = -(lam m hm l * q t₀ l) - waveCubic m hm (q t₀) l := by
    have hc_u := hslice _ hu_c t₀ ht₀
    have hc_ux := hslice _ hux_c t₀ ht₀
    have hc_uxx := hslice _ huxx_c t₀ ht₀
    have hb := hbd t₀ ht₀
    have hxx := wave_integral_second_deriv_mul (f := fun x => waveU m hm (q t₀) x)
      (f' := ux t₀) (f'' := uxx t₀) l hb.1 hb.2
      (fun x hx => (hder t₀ ht₀ x hx).2.2.1) (fun x hx => (hder t₀ ht₀ x hx).2.2.2.1)
      hc_ux hc_uxx
    have hI' : ∀ g : ℝ → ℝ, ContinuousOn g (Icc 0 π) → IntervalIntegrable g volume 0 π :=
      fun g hg => hg.intervalIntegrable_of_Icc hpi.le
    have hφ0 : ContinuousOn (sineMode l) (Icc 0 π) := (wave_continuous_sineMode l).continuousOn
    have hu3 : ContinuousOn (fun x => waveU m hm (q t₀) x ^ 3) (Icc 0 π) := hc_u.pow 3
    have e1 : ∫ x in (0 : ℝ)..π, utt t₀ x * sineMode l x =
        ∫ x in (0 : ℝ)..π, (uxx t₀ x * sineMode l x - m * (waveU m hm (q t₀) x * sineMode l x)
          - waveU m hm (q t₀) x ^ 3 * sineMode l x) := by
      refine intervalIntegral.integral_congr fun x hx => ?_
      rw [Set.uIcc_of_le hpi.le] at hx
      have := (hder t₀ ht₀ x hx).2.2.2.2
      simp only at this
      rw [this]; ring
    have i1 : IntervalIntegrable (fun x => uxx t₀ x * sineMode l x) volume 0 π :=
      hI' _ (hc_uxx.mul hφ0)
    have i2 : IntervalIntegrable (fun x => m * (waveU m hm (q t₀) x * sineMode l x)) volume 0 π :=
      hI' _ (continuousOn_const.mul (hc_u.mul hφ0))
    have i3 : IntervalIntegrable (fun x => waveU m hm (q t₀) x ^ 3 * sineMode l x) volume 0 π :=
      hI' _ (hu3.mul hφ0)
    rw [e1, intervalIntegral.integral_sub (i1.sub i2) i3, intervalIntegral.integral_sub i1 i2,
      intervalIntegral.integral_const_mul, hxx, wave_coeff_integral_u m hm (hq t₀ ht₀) l,
      integral_waveU_cube_mul_sineMode hm (q t₀) l]
    have hl2 : (l : ℝ) ^ 2 = lam m hm l * lam m hm l - m := by
      unfold lam
      rw [Real.mul_self_sqrt (by positivity)]
      ring
    simp only [waveHat]
    rw [hl2]
    generalize Real.sqrt (lam m hm l) = s at hss hs0 ⊢
    rw [← hss]
    field_simp
    ring
  refine ⟨hq', hB, hval, ?_⟩
  exact continuousAt_const.mul P2c

lemma wave_contDiffOn_one {I : Set ℝ} (hI : IsOpen I) {f : ℝ → ℝ}
    (hd : ∀ t ∈ I, DifferentiableAt ℝ f t) (hc : ContinuousOn (deriv f) I) :
    ContDiffOn ℝ 1 f I := by
  rw [show (1 : WithTop ℕ∞) = 0 + 1 from rfl, contDiffOn_succ_iff_deriv_of_isOpen hI]
  exact ⟨fun t ht => (hd t ht).differentiableWithinAt, by simp, contDiffOn_zero.2 hc⟩

/-- `bpW:w0n:pde-equiv` (ii) (`stepW:w0n:converse`): if `u(t,x) = U_m(q(t))(x)` is a classical
solution on the open set `I` with `u_t(t,·) = V_m(p(t))`, then every `q_j, p_j` is `C¹` on `I`,
`q̇_j = λ_j p_j` and `ṗ_j = -λ_j q_j - 𝒢(q)_j`. -/
theorem wave_pde_to_coeff (m : ℝ) (hm : 0 < m) {I : Set ℝ} (hI : IsOpen I) {q p : ℝ → ℕ+ → ℝ}
    (hq : ∀ t ∈ I, WaveEll 1 1 (q t)) (hp : ∀ t ∈ I, WaveEll 1 1 (p t))
    {ut ux utt uxx : ℝ → ℝ → ℝ}
    (hsol : IsClassicalSolutionWith m (fun t x => waveU m hm (q t) x) ut ux utt uxx I)
    (hut : ∀ t ∈ I, ∀ x ∈ Set.Icc 0 π, ut t x = waveV m hm (p t) x) (j : ℕ+) :
    ContDiffOn ℝ 1 (fun t => q t j) I ∧ ContDiffOn ℝ 1 (fun t => p t j) I ∧
      ∀ t ∈ I, deriv (fun s => q s j) t = lam m hm j * p t j ∧
        deriv (fun s => p s j) t = -(lam m hm j * q t j) - waveCubic m hm (q t) j := by
  have H := fun t (ht : t ∈ I) => wave_converse_pointwise m hm hI hq hp hsol hut j ht
  have hdq : ∀ t ∈ I, deriv (fun s => q s j) t = lam m hm j * p t j :=
    fun t ht => (H t ht).1.deriv
  have hdp : ∀ t ∈ I, deriv (fun s => p s j) t = -(lam m hm j * q t j) - waveCubic m hm (q t) j :=
    fun t ht => by rw [(H t ht).2.1.deriv]; exact (H t ht).2.2.1
  refine ⟨?_, ?_, fun t ht => ⟨hdq t ht, hdp t ht⟩⟩
  · refine wave_contDiffOn_one hI (fun t ht => (H t ht).1.differentiableAt) ?_
    have hpc : ContinuousOn (fun s => p s j) I := fun t ht =>
      (H t ht).2.1.continuousAt.continuousWithinAt
    exact (continuousOn_const.mul hpc).congr hdq
  · refine wave_contDiffOn_one hI (fun t ht => (H t ht).2.1.differentiableAt) ?_
    refine ContinuousOn.congr (f := fun s => (Real.sqrt (lam m hm j))⁻¹ *
      ∫ x in (0 : ℝ)..π, utt s x * sineMode j x) (fun t ht => (H t ht).2.2.2.continuousWithinAt)
      fun t ht => by rw [(H t ht).2.1.deriv]

end KAM.Wave

end
