/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Strip.Analytic

/-!
# P Parts 4-5: local complexification of a real-analytic function (`bpP:p5:ext-loc`, helper)

`local_real_complexification`: a real-analytic `f : ℝᴺ → ℝ` at `x` is the restriction to the real
points of a function `F` holomorphic and bounded on a complex ball around `ι x`.

The complexified series is built coordinatewise: for the real power series `p` of `f`, the
`n`-th complex multilinear map is `q n m = ∑_{i : Fin n → Fin N} c n i ∏_j m j (i j)` with
`c n i = p n (e_{i 0}, …, e_{i (n-1)})`. Then `‖q n‖ ≤ Nⁿ ‖p n‖` and `q n (ι v) = p n v`.
Design `docs/tracks/P/design/P45-LEAN-DESIGN.md`, package P5-CL.
-/

@[expose] public noncomputable section

open Set Metric
open scoped BigOperators NNReal ENNReal

namespace KAM.Planetary.PGAssembly

variable {N : ℕ}

/-- Real coefficient of the complexified `n`-th multilinear map at the multi-index `i`. -/
def complexCoeff (p : FormalMultilinearSeries ℝ (Fin N → ℝ) ℝ) (n : ℕ) (i : Fin n → Fin N) : ℝ :=
  p n fun j => Pi.single (i j) 1

/-- The complexified `n`-th multilinear map. -/
def complexSeriesTerm (p : FormalMultilinearSeries ℝ (Fin N → ℝ) ℝ) (n : ℕ) :
    ContinuousMultilinearMap ℂ (fun _ : Fin n => Fin N → ℂ) ℂ :=
  ∑ i : Fin n → Fin N, (complexCoeff p n i : ℂ) •
    (ContinuousMultilinearMap.mkPiAlgebra ℂ (Fin n) ℂ).compContinuousLinearMap
      fun j => ContinuousLinearMap.proj (i j)

/-- The complexified formal series. -/
def complexSeries (p : FormalMultilinearSeries ℝ (Fin N → ℝ) ℝ) :
    FormalMultilinearSeries ℂ (Fin N → ℂ) ℂ := complexSeriesTerm p

theorem complexSeries_apply (p : FormalMultilinearSeries ℝ (Fin N → ℝ) ℝ) (n : ℕ)
    (m : Fin n → Fin N → ℂ) :
    complexSeries p n m = ∑ i : Fin n → Fin N, (complexCoeff p n i : ℂ) * ∏ j, m j (i j) := by
  simp [complexSeries, complexSeriesTerm]

theorem abs_complexCoeff_le (p : FormalMultilinearSeries ℝ (Fin N → ℝ) ℝ) (n : ℕ)
    (i : Fin n → Fin N) : |complexCoeff p n i| ≤ ‖p n‖ := by
  have h := (p n).le_opNorm fun j => (Pi.single (i j) (1 : ℝ) : Fin N → ℝ)
  have h1 : ∀ j, ‖(Pi.single (i j) (1 : ℝ) : Fin N → ℝ)‖ ≤ 1 := fun j => by
    simp [Pi.norm_def, Pi.single_apply]
    intro b; split_ifs <;> simp
  have h2 : ∏ j, ‖(Pi.single (i j) (1 : ℝ) : Fin N → ℝ)‖ ≤ 1 :=
    Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun j _ => h1 j
  calc |complexCoeff p n i| = ‖p n fun j => (Pi.single (i j) (1 : ℝ) : Fin N → ℝ)‖ := by
        simp [complexCoeff]
    _ ≤ ‖p n‖ * ∏ j, ‖(Pi.single (i j) (1 : ℝ) : Fin N → ℝ)‖ := h
    _ ≤ ‖p n‖ * 1 := by gcongr
    _ = ‖p n‖ := mul_one _

theorem norm_complexSeries_le (p : FormalMultilinearSeries ℝ (Fin N → ℝ) ℝ) (n : ℕ) :
    ‖complexSeries p n‖ ≤ (N : ℝ) ^ n * ‖p n‖ := by
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun m => ?_
  rw [complexSeries_apply]
  have hm : ∀ j, ‖m j‖ ≤ ‖m j‖ := fun _ => le_rfl
  calc ‖∑ i : Fin n → Fin N, (complexCoeff p n i : ℂ) * ∏ j, m j (i j)‖
      ≤ ∑ i : Fin n → Fin N, ‖(complexCoeff p n i : ℂ) * ∏ j, m j (i j)‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin n → Fin N, ‖p n‖ * ∏ j, ‖m j‖ := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_prod]
        gcongr with j
        · exact abs_complexCoeff_le p n i
        · exact norm_le_pi_norm (m j) (i j)
    _ = (N : ℝ) ^ n * ‖p n‖ * ∏ j, ‖m j‖ := by
        simp [Finset.sum_const, Finset.card_univ, mul_assoc]

theorem complexSeries_realInclusion (p : FormalMultilinearSeries ℝ (Fin N → ℝ) ℝ) (n : ℕ)
    (v : Fin n → Fin N → ℝ) :
    complexSeries p n (fun j => realInclusion N (v j)) = (p n v : ℂ) := by
  classical
  rw [complexSeries_apply]
  have hv : v = fun j => ∑ k, v j k • (Pi.single k (1 : ℝ) : Fin N → ℝ) := by
    funext j; ext l; simp [Pi.single_apply]
  have : p n v = ∑ i : Fin n → Fin N, (∏ j, v j (i j)) * complexCoeff p n i := by
    conv_lhs => rw [hv]
    rw [(p n).map_sum (fun j k => v j k • (Pi.single k (1 : ℝ) : Fin N → ℝ))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [(p n).map_smul_univ]
    simp [complexCoeff]
  rw [this]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_comm]; simp

theorem le_radius_complexSeries (p : FormalMultilinearSeries ℝ (Fin N → ℝ) ℝ) {t : ℝ≥0}
    {C : ℝ} (hC : ∀ n, ‖p n‖ * (t : ℝ) ^ n ≤ C) :
    ((t / (N + 1) : ℝ≥0) : ℝ≥0∞) ≤ (complexSeries p).radius := by
  refine (complexSeries p).le_radius_of_bound C fun n => ?_
  have hs : (((t / (N + 1) : ℝ≥0)) : ℝ) = t / (N + 1) := by simp
  have hN : (N : ℝ) * (t / (N + 1)) ≤ t := by
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith [(t.2 : (0 : ℝ) ≤ t)]
  calc ‖complexSeries p n‖ * (((t / (N + 1) : ℝ≥0)) : ℝ) ^ n
      ≤ (N : ℝ) ^ n * ‖p n‖ * (t / (N + 1)) ^ n := by
        rw [hs]; gcongr; exact norm_complexSeries_le p n
    _ = ‖p n‖ * ((N : ℝ) * (t / (N + 1))) ^ n := by rw [mul_pow]; ring
    _ ≤ ‖p n‖ * (t : ℝ) ^ n := by gcongr
    _ ≤ C := hC n

end KAM.Planetary.PGAssembly

namespace KAM.Planetary

open KAM.Planetary.PGAssembly

theorem local_real_complexification {N : ℕ} {f : (Fin N → ℝ) → ℝ} {x : Fin N → ℝ}
    (hf : AnalyticAt ℝ f x) : ∃ (rho M : ℝ) (F : (Fin N → ℂ) → ℂ),
      0 < rho ∧ 0 < M ∧ DifferentiableOn ℂ F (ball (KAM.realInclusion N x) rho) ∧
      (∀ y ∈ ball x rho, F (KAM.realInclusion N y) = (f y : ℂ)) ∧
      (∀ z ∈ ball (KAM.realInclusion N x) rho, ‖F z‖ ≤ M) := by
  obtain ⟨p, r, hp⟩ := hf
  obtain ⟨t, ht0, htr⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hp.r_pos
  obtain ⟨C, -, hC⟩ := p.norm_mul_pow_le_of_lt_radius (htr.trans_le hp.r_le)
  set q := complexSeries p with hqdef
  set s : ℝ≥0 := t / (N + 1) with hsdef
  have ht : (0 : ℝ≥0) < t := by exact_mod_cast ht0
  have hs0 : (0 : ℝ≥0) < s := by positivity
  have hsq : (s : ℝ≥0∞) ≤ q.radius := le_radius_complexSeries p hC
  have hqpos : 0 < q.radius := lt_of_lt_of_le (by exact_mod_cast hs0) hsq
  have hq := q.hasFPowerSeriesOnBall hqpos
  have hst : (s : ℝ) ≤ t := by
    rw [hsdef]; push_cast
    rw [div_le_iff₀ (by positivity)]; nlinarith [(ht : (0 : ℝ) < t), (N.cast_nonneg : (0 : ℝ) ≤ N)]
  set F : (Fin N → ℂ) → ℂ := fun z => q.sum (z - KAM.realInclusion N x) with hF
  have hdiff : DifferentiableOn ℂ F (ball (KAM.realInclusion N x) s) := by
    intro z hz
    have hz' : z - KAM.realInclusion N x ∈ Metric.eball (0 : Fin N → ℂ) q.radius := by
      rw [Metric.mem_eball, edist_zero_right]
      refine lt_of_lt_of_le ?_ hsq
      rw [enorm_lt_coe]
      have : ‖z - KAM.realInclusion N x‖ < s := by simpa [dist_eq_norm] using hz
      exact_mod_cast this
    have := (hq.analyticAt_of_mem hz').differentiableAt
    exact ((this.comp z (differentiableAt_id.sub_const _))).differentiableWithinAt
  have hcont : ContinuousOn F (closedBall (KAM.realInclusion N x) (s / 2)) :=
    hdiff.continuousOn.mono (closedBall_subset_ball (by have : (0:ℝ) < s := hs0; linarith))
  obtain ⟨B, hB⟩ := (isCompact_closedBall _ _).exists_bound_of_continuousOn hcont
  have hs2 : (0 : ℝ) < s / 2 := by have : (0:ℝ) < s := hs0; linarith
  refine ⟨s / 2, max B 0 + 1, F, hs2, by positivity, hdiff.mono (ball_subset_ball (by
    have : (0:ℝ) < s := hs0; linarith)), ?_, ?_⟩
  · intro y hy
    have hy1 : ‖y - x‖ < s / 2 := by simpa [dist_eq_norm] using hy
    have hy2 : y - x ∈ Metric.eball (0 : Fin N → ℝ) r := by
      rw [Metric.mem_eball, edist_zero_right]
      refine lt_trans ?_ htr
      rw [enorm_lt_coe]
      have : ‖y - x‖ < t := by have : (0:ℝ) < s := hs0; linarith
      exact_mod_cast this
    have h1 := hp.hasSum hy2
    rw [add_sub_cancel] at h1
    have hy3 : KAM.realInclusion N y - KAM.realInclusion N x ∈
        Metric.eball (0 : Fin N → ℂ) q.radius := by
      rw [← map_sub, Metric.mem_eball, edist_zero_right]
      refine lt_of_lt_of_le ?_ hsq
      rw [enorm_lt_coe, ← NNReal.coe_lt_coe, coe_nnnorm, KAM.norm_realInclusion]
      have : (0:ℝ) < s := hs0
      linarith
    have h2 := hq.hasSum hy3
    simp only [zero_add] at h2
    have h3 : HasSum (fun n => q n fun _ => KAM.realInclusion N y - KAM.realInclusion N x)
        (F (KAM.realInclusion N y)) := h2
    have h4 : HasSum (fun n => ((p n fun _ => y - x : ℝ) : ℂ)) ((f y : ℝ) : ℂ) :=
      Complex.hasSum_ofReal.mpr h1
    have h5 : (fun n => q n fun _ => KAM.realInclusion N y - KAM.realInclusion N x) =
        fun n => ((p n fun _ => y - x : ℝ) : ℂ) := by
      funext n
      rw [← map_sub]
      exact complexSeries_realInclusion p n fun _ => y - x
    rw [h5] at h3
    exact h3.unique h4
  · intro z hz
    have := hB z (ball_subset_closedBall hz)
    linarith [le_max_left B 0]

end KAM.Planetary
