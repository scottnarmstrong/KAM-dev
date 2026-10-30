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
  have hbound : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ Ι (0 : ℝ) π → ∀ s ∈ Metric.ball t₀ r, ‖F' s x‖ ≤ C' := by
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
  have hφ : Continuous (sineMode l) := continuous_sineMode l
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

end KAM.Wave

end
