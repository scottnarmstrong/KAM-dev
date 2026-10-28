/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Strip.Analytic
public import KAM.Planetary.MaximalStep.Basic

/-!
# Complexification of real analytic maps and the real-slice identity theorem (P11A-P0)

`p11_real_slice_identity` (`stepP:p11:hc-rot`): a holomorphic `F` on a max-norm ball around a real
point that vanishes on the real slice vanishes on the whole ball. The proof frees one coordinate
at a time with the one-variable identity theorem.

`p11_complexification`: a real analytic map `f : ℝᵃ → ℝᵇ` at `x` extends to a holomorphic map on a
max-norm ball around `x`. Each real multilinear coefficient `pₙ` is complexified coordinatewise
(`p11_cmap`), with `‖qₙ‖ ≤ aⁿ ‖pₙ‖`, which shrinks the radius of convergence by the factor `a`.
-/

@[expose] public noncomputable section
open Set Filter Metric
open scoped Topology NNReal ENNReal
namespace KAM.Planetary

/-- Real-slice identity theorem. -/
theorem p11_real_slice_identity {n : ℕ} {x : P11Vec n} {r : ℝ} (hr : 0 < r)
    {F : P11CVec n → ℂ} (hF : DifferentiableOn ℂ F (Metric.ball (KAM.realInclusion n x) r))
    (hzero : ∀ y, ‖y-x‖ < r → F (KAM.realInclusion n y)=0) :
    ∀ z ∈ Metric.ball (KAM.realInclusion n x) r, F z=0 := by
  have hstep : ∀ k : ℕ, ∀ z ∈ Metric.ball (KAM.realInclusion n x) r,
      (∀ i : Fin n, k ≤ (i : ℕ) → (z i).im = 0) → F z = 0 := by
    intro k
    induction k with
    | zero =>
      intro z hz hre
      have hzy : z = KAM.realInclusion n (KAM.realPartCLM n z) := by
        ext i
        simp only [KAM.realInclusion_apply, KAM.realPartCLM_apply]
        exact (Complex.ext (by simp) (by simpa using hre i (Nat.zero_le _)))
      rw [hzy]
      refine hzero _ ?_
      have h : ‖KAM.realInclusion n (KAM.realPartCLM n z - x)‖ < r := by
        rw [map_sub, ← hzy]
        exact mem_ball_iff_norm.mp hz
      rwa [KAM.norm_realInclusion] at h
    | succ k ih =>
      intro z hz hre
      by_cases hk : k < n
      · set i0 : Fin n := ⟨k, hk⟩ with hi0
        set c : ℂ := KAM.realInclusion n x i0 with hc
        have hdisc : ∀ ζ ∈ ball c r, Function.update z i0 ζ ∈
            Metric.ball (KAM.realInclusion n x) r := by
          intro ζ hζ
          rw [mem_ball_iff_norm, pi_norm_lt_iff hr]
          intro i
          by_cases hi : i = i0
          · subst hi
            simpa [hc, dist_eq_norm] using hζ
          · simp only [Pi.sub_apply, Function.update_of_ne hi]
            have := (pi_norm_lt_iff hr).mp (mem_ball_iff_norm.mp hz) i
            simpa using this
        set g : ℂ → ℂ := fun ζ => F (Function.update z i0 ζ) with hg
        have hgd : DifferentiableOn ℂ g (ball c r) := by
          refine hF.comp ?_ hdisc
          exact (differentiable_pi.mpr fun i => by
            by_cases hi : i = i0
            · subst hi; simp
            · simp [Function.update_of_ne hi]).differentiableOn
        have hga : AnalyticOnNhd ℂ g (ball c r) := hgd.analyticOnNhd isOpen_ball
        have hfreq : ∃ᶠ ζ in 𝓝[≠] c, g ζ = 0 := by
          have h1 : ∀ᶠ t : ℝ in 𝓝[≠] (x i0), g (t : ℂ) = 0 := by
            have hev : ∀ᶠ t : ℝ in 𝓝 (x i0), |t - x i0| < r := by
              filter_upwards [Metric.ball_mem_nhds (x i0) hr] with t ht
              simpa [Real.dist_eq] using ht
            filter_upwards [nhdsWithin_le_nhds hev] with t ht
            refine ih _ (hdisc _ ?_) ?_
            · simpa [hc, dist_eq_norm, ← Complex.ofReal_sub] using ht
            · intro i hi
              by_cases hii : i = i0
              · subst hii; simp
              · have hi' : k + 1 ≤ (i : ℕ) := by
                  have : (i : ℕ) ≠ k := fun h => hii (Fin.ext h)
                  omega
                simpa [Function.update_of_ne hii] using hre i hi'
          have h2 : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝[≠] (x i0)) (𝓝[≠] c) := by
            refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
              ((Complex.continuous_ofReal.tendsto _).mono_left nhdsWithin_le_nhds) ?_
            filter_upwards [self_mem_nhdsWithin] with t ht
            simpa [hc] using ht
          exact h2.frequently_map _ (fun _ h => h) h1.frequently
        have hzero_disc := hga.eqOn_zero_of_preconnected_of_frequently_eq_zero
          (convex_ball c r).isPreconnected (mem_ball_self hr) hfreq
        have hzi : z i0 ∈ ball c r := by
          have := (pi_norm_lt_iff hr).mp (mem_ball_iff_norm.mp hz) i0
          simpa [hc, dist_eq_norm] using this
        have := hzero_disc hzi
        simpa [hg] using this
      · refine ih z hz fun i hi => hre i ?_
        have := i.2
        omega
  exact fun z hz => hstep n z hz fun i hi => absurd i.2 (by omega)

/-- Coordinatewise complexification of a real continuous multilinear map
`(ℝᵃ)ⁿ → ℝᵇ`: `Σ_j (Π_m w_m(j_m)) • ι (P (e_{j_1}, …, e_{j_n}))`. -/
def p11CMap {a b n : ℕ} (P : ContinuousMultilinearMap ℝ (fun _ : Fin n => P11Vec a) (P11Vec b)) :
    ContinuousMultilinearMap ℂ (fun _ : Fin n => P11CVec a) (P11CVec b) :=
  ∑ j : Fin n → Fin a,
    ((ContinuousMultilinearMap.mkPiAlgebra ℂ (Fin n) ℂ).compContinuousLinearMap
      (fun m => ContinuousLinearMap.proj (j m))).smulRight
        (KAM.realInclusion b (P (fun m => Pi.single (j m) 1)))

theorem p11CMap_apply {a b n : ℕ}
    (P : ContinuousMultilinearMap ℝ (fun _ : Fin n => P11Vec a) (P11Vec b))
    (w : Fin n → P11CVec a) :
    p11CMap P w = ∑ j : Fin n → Fin a,
      (∏ m, w m (j m)) • KAM.realInclusion b (P (fun m => Pi.single (j m) 1)) := by
  simp [p11CMap]

/-- On real vectors the complexification agrees with `P`. -/
theorem p11CMap_real {a b n : ℕ}
    (P : ContinuousMultilinearMap ℝ (fun _ : Fin n => P11Vec a) (P11Vec b)) (h : P11Vec a) :
    p11CMap P (fun _ => KAM.realInclusion a h) = KAM.realInclusion b (P (fun _ => h)) := by
  have hh : (fun _ : Fin n => h) =
      fun m => ∑ i : Fin a, h i • (Pi.single i (1 : ℝ) : P11Vec a) := by
    ext m i
    simp [Finset.sum_apply, Pi.single_apply]
  rw [hh, P.map_sum (fun _ i => h i • (Pi.single i (1 : ℝ) : P11Vec a)), map_sum,
    p11CMap_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [P.map_smul_univ, map_smul]
  simp only [KAM.realInclusion_apply, ← Complex.ofReal_prod]
  exact Complex.coe_smul _ _

/-- `‖p11CMap P‖ ≤ aⁿ ‖P‖`. -/
theorem norm_p11CMap_le {a b n : ℕ}
    (P : ContinuousMultilinearMap ℝ (fun _ : Fin n => P11Vec a) (P11Vec b)) :
    ‖p11CMap P‖ ≤ (a : ℝ) ^ n * ‖P‖ := by
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun w => ?_
  rw [p11CMap_apply]
  have hj : ∀ j : Fin n → Fin a,
      ‖(∏ m, w m (j m)) • KAM.realInclusion b (P (fun m => Pi.single (j m) 1))‖ ≤
        ‖P‖ * ∏ m, ‖w m‖ := by
    intro j
    rw [norm_smul, KAM.norm_realInclusion, norm_prod]
    have h1 : ∏ m, ‖w m (j m)‖ ≤ ∏ m, ‖w m‖ :=
      Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun m _ => norm_le_pi_norm (w m) (j m)
    have h2 : ‖P (fun m => Pi.single (j m) (1 : ℝ))‖ ≤ ‖P‖ := by
      refine (P.le_opNorm _).trans ?_
      simp [Pi.norm_single]
    calc _ ≤ (∏ m, ‖w m‖) * ‖P‖ :=
          mul_le_mul h1 h2 (norm_nonneg _) (Finset.prod_nonneg fun _ _ => norm_nonneg _)
      _ = _ := mul_comm _ _
  calc _ ≤ ∑ j : Fin n → Fin a, ‖P‖ * ∏ m, ‖w m‖ := (norm_sum_le _ _).trans
          (Finset.sum_le_sum fun j _ => hj j)
    _ = _ := by simp [Finset.sum_const, mul_comm, mul_left_comm]

/-- hc-rot: complexification is a new proof obligation, not supplied by holomorphic-to-real
restriction. -/
theorem p11_complexification {a b : ℕ} {f : P11Vec a → P11Vec b} {x : P11Vec a}
    (hf : AnalyticAt ℝ f x) :
    ∃ r : ℝ, 0 < r ∧ ∃ F : P11CVec a → P11CVec b,
      DifferentiableOn ℂ F (Metric.ball (KAM.realInclusion a x) r) ∧
      ∀ y, ‖y-x‖ < r → F (KAM.realInclusion a y)=KAM.realInclusion b (f y) := by
  obtain ⟨p, ρ, hp⟩ := hf
  obtain ⟨r', hr'0, hr'ρ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hp.r_pos
  let q : FormalMultilinearSeries ℂ (P11CVec a) (P11CVec b) := fun n => p11CMap (p n)
  set A : ℝ≥0 := ((max a 1 : ℕ) : ℝ≥0) with hA
  have hA1 : (1 : ℝ≥0) ≤ A := by simp [hA]
  have hApos : 0 < A := lt_of_lt_of_le one_pos hA1
  have haA : (a : ℝ) ≤ A := by simp [hA]
  have hr'pos : 0 < r' := ENNReal.coe_pos.mp hr'0
  set s : ℝ≥0 := r' / A with hs
  have hs0 : 0 < s := div_pos hr'pos hApos
  have hAs : A * s = r' := mul_div_cancel₀ _ hApos.ne'
  have hsr : (s : ℝ) ≤ r' := by
    exact_mod_cast (div_le_self zero_le hA1 : r' / A ≤ r')
  obtain ⟨C, hC⟩ := p.norm_mul_pow_le_of_lt_radius (r := r') (hr'ρ.trans_le hp.r_le)
  have hqrad : (s : ℝ≥0∞) ≤ q.radius := by
    refine q.le_radius_of_bound C fun n => ?_
    have hAs' : (A : ℝ) * s = r' := by exact_mod_cast hAs
    calc ‖q n‖ * (s : ℝ) ^ n ≤ ((a : ℝ) ^ n * ‖p n‖) * (s : ℝ) ^ n := by
          gcongr; exact norm_p11CMap_le _
      _ ≤ ((A : ℝ) ^ n * ‖p n‖) * (s : ℝ) ^ n := by gcongr
      _ = ‖p n‖ * (r' : ℝ) ^ n := by rw [← hAs', mul_pow]; ring
      _ ≤ C := hC.2 n
  have hqb : HasFPowerSeriesOnBall q.sum q 0 q.radius :=
    q.hasFPowerSeriesOnBall (lt_of_lt_of_le (by exact_mod_cast hs0) hqrad)
  have hmem : ∀ {E : Type} [NormedAddCommGroup E] (v : E) (t : ℝ≥0), ‖v‖ < t →
      v ∈ Metric.eball (0 : E) (t : ℝ≥0∞) := fun v t hv => by
    rw [Metric.mem_eball, edist_zero_right]
    exact enorm_lt_coe.mpr (by exact_mod_cast hv)
  refine ⟨s, hs0, fun z => q.sum (z - KAM.realInclusion a x), ?_, ?_⟩
  · refine hqb.differentiableOn.comp (differentiable_id.sub_const _).differentiableOn
      fun z hz => ?_
    refine Metric.eball_subset_eball hqrad (hmem _ s ?_)
    simpa [dist_eq_norm] using hz
  · intro y hy
    have hy' : ‖KAM.realInclusion a (y - x)‖ < s := by rwa [KAM.norm_realInclusion]
    have h1 := hqb.hasSum (Metric.eball_subset_eball hqrad (hmem _ s hy'))
    have hyρ : y - x ∈ Metric.eball (0 : P11Vec a) ρ :=
      Metric.eball_subset_eball hr'ρ.le (hmem _ r' (lt_of_lt_of_le hy hsr))
    have h2 := (KAM.realInclusion b).hasSum (hp.hasSum hyρ)
    have h3 : HasSum (fun n => q n fun _ => KAM.realInclusion a (y - x))
        (KAM.realInclusion b (f (x + (y - x)))) := by
      convert h2 using 2 with n
      exact p11CMap_real (p n) (y - x)
    have := h1.unique h3
    simpa [map_sub] using this

end KAM.Planetary
