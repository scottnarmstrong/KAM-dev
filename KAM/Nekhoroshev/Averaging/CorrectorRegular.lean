/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Nekhoroshev.Averaging.Corrector
public import Mathlib.Analysis.Calculus.SmoothSeries

/-!
# Part N12: regularity of the corrector (`bpN:p12:wreg`, `bpN:p12:envelope_regular`)

`wreg` proves that `avgW` is `C¹` on the whole real domain `avgDomain n R`, that its real
directional derivatives are the termwise sums of the derivatives of the summands (differentiation
under the sum by `hasFDerivAt_tsum_of_isPreconnected` on the open convex domain, with a global
dominating series `C (1 + |k|₁)³ β_k`), that it is `1`-periodic in the angles, and the quantitative
envelope bounds and the exact residual series on the inner action ball.
`envelope_regular` records measurability of the ENNReal envelopes and their finiteness.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory
open scoped ENNReal ContDiff

namespace KAM.Nekhoroshev

variable {n : ℕ} {R s : ℝ} {h : (Fin n → ℂ) → ℂ} {f : AvgComplexPhase n → ℂ}

private theorem contDiffOn_freq' (d : AveragingData n R s h f) :
    ContDiffOn ℝ 2 (KAM.frequencyMap h) (realActionDomain n R s) := by
  have hg : ContDiffOn ℝ 3 (realPart h) (realActionDomain n R s) := d.hh.2.2.2.2
  have hU := isOpen_realActionDomain (n := n) d.hR d.hs
  have hd : ContDiffOn ℝ 2 (fderiv ℝ (realPart h)) (realActionDomain n R s) :=
    hg.fderiv_of_isOpen hU (by norm_num)
  refine contDiffOn_pi.2 fun i => ?_
  exact ContDiffOn.clm_apply hd (contDiffOn_const (c := (Pi.single i (1 : ℝ) : Fin n → ℝ)))

/-- The integer index as a complex vector. -/
private def kvec (k : Fin n → ℤ) : Fin n → ℂ := fun j => (k j : ℂ)

private theorem norm_kvec (k : Fin n → ℤ) : ‖kvec k‖ = ‖fun j => (k j : ℝ)‖ := by
  have : kvec k = KAM.realInclusion n (fun j => (k j : ℝ)) := by
    ext j; simp [kvec]
  rw [this, KAM.norm_realInclusion]

private theorem norm_k_le (k : Fin n → ℤ) : ‖fun j => (k j : ℝ)‖ ≤ KAM.Fourier.modeSize k :=
  (pi_norm_le_iff_of_nonneg (KAM.Fourier.modeSize_nonneg k)).2 fun j => by
    simpa using KAM.Fourier.abs_coord_le_modeSize k j

/-- The scalar factor of the corrector coefficient. -/
private def aScal (h : (Fin n → ℂ) → ℂ) (f : AvgComplexPhase n → ℂ) (κ : ℝ) (k : Fin n → ℤ)
    (I : Fin n → ℝ) : ℂ :=
  avgCoeff f (KAM.realInclusion n I) k * (avgPsi κ (avgQ h k I) : ℂ)

private theorem avgU_eq (κ : ℝ) (k : Fin n → ℤ) :
    avgU h f κ k = fun I => aScal h f κ k I • kvec k := by
  ext I j
  simp [avgU, aScal, kvec]

private theorem real_mem (d : AveragingData n R s h f) {I : Fin n → ℝ} (hI : I ∈ actionBall n R) :
    KAM.realInclusion n I ∈ KAM.actionNbhd (actionBall n R) s :=
  ball_subset_realActionDomain d.hR d.hs hI

private theorem hasFDerivAt_Q (d : AveragingData n R s h f) (k : Fin n → ℤ) {I : Fin n → ℝ}
    (hI : I ∈ actionBall n R) :
    HasFDerivAt (avgQ h k) (∑ i, (k i : ℝ) •
      (ContinuousLinearMap.proj i).comp (fderiv ℝ (KAM.frequencyMap h) I)) I := by
  have hU := isOpen_realActionDomain (n := n) d.hR d.hs
  have hω : HasFDerivAt (KAM.frequencyMap h) (fderiv ℝ (KAM.frequencyMap h) I) I :=
    ((contDiffOn_freq' d).differentiableOn (by norm_num)
      I (ball_subset_realActionDomain d.hR d.hs hI)).differentiableAt
      (hU.mem_nhds (ball_subset_realActionDomain d.hR d.hs hI)) |>.hasFDerivAt
  have := HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
    (hasFDerivAt_pi'.1 hω i).const_mul (k i : ℝ))
  convert this using 1
  ext J; simp [avgQ]

/-- Bound on the derivative of the divisor `k · ω(I)`. -/
private theorem abs_dQ_le (k : Fin n → ℤ) {I : Fin n → ℝ} {M₂ : ℝ}
    (hM : ∀ i, ∑ j, |avgM h I i j| ≤ M₂) (v : Fin n → ℝ) :
    |(∑ i, (k i : ℝ) • (ContinuousLinearMap.proj i).comp (fderiv ℝ (KAM.frequencyMap h) I)) v|
      ≤ KAM.Fourier.modeSize k * M₂ * ‖v‖ := by
  have hcomp : ∀ i, |fderiv ℝ (KAM.frequencyMap h) I v i| ≤ M₂ * ‖v‖ := by
    intro i
    have hv : v = ∑ j, v j • (Pi.single j (1 : ℝ) : Fin n → ℝ) := by
      ext l; simp [Finset.sum_apply, Pi.single_apply]
    have e : fderiv ℝ (KAM.frequencyMap h) I v i = ∑ j, v j * avgM h I i j := by
      conv_lhs => rw [hv]
      simp [avgM, map_sum, Finset.sum_apply]
    rw [e]
    calc |∑ j, v j * avgM h I i j| ≤ ∑ j, |v j * avgM h I i j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, ‖v‖ * |avgM h I i j| := Finset.sum_le_sum fun j _ => by
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_right (by simpa using norm_le_pi_norm v j) (abs_nonneg _)
      _ = ‖v‖ * ∑ j, |avgM h I i j| := by rw [Finset.mul_sum]
      _ ≤ ‖v‖ * M₂ := mul_le_mul_of_nonneg_left (hM i) (norm_nonneg _)
      _ = M₂ * ‖v‖ := mul_comm _ _
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
  calc |∑ i, (k i : ℝ) * fderiv ℝ (KAM.frequencyMap h) I v i|
      ≤ ∑ i, |(k i : ℝ) * fderiv ℝ (KAM.frequencyMap h) I v i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |(k i : ℝ)| * (M₂ * ‖v‖) := Finset.sum_le_sum fun i _ => by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hcomp i) (abs_nonneg _)
    _ = KAM.Fourier.modeSize k * M₂ * ‖v‖ := by
        rw [← Finset.sum_mul, mul_assoc]; rfl

private theorem avgBeta_nonneg (s : ℝ) (k : Fin n → ℤ) : 0 ≤ avgBeta s k :=
  (Real.exp_pos _).le

/-- Derivative of the real-slice coefficient with its Cauchy bound. -/
private theorem hasFDerivAt_coeffR (d : AveragingData n R s h f) (k : Fin n → ℤ)
    {I : Fin n → ℝ} (hI : I ∈ actionBall n R) :
    ∃ c' : (Fin n → ℝ) →L[ℝ] ℂ,
      HasFDerivAt (fun J => avgCoeff f (KAM.realInclusion n J) k) c' I ∧
      ∀ v, ‖c' v‖ ≤ n * (2 / s * avgBeta s k) * ‖v‖ := by
  have hopen := isOpen_actionNbhd_ball (n := n) R s
  have hdiff : DifferentiableAt ℂ (fun J => avgCoeff f J k) (KAM.realInclusion n I) :=
    ((coef d).1 k).differentiableAt (hopen.mem_nhds (real_mem d hI))
  have hc := (hdiff.hasFDerivAt.restrictScalars ℝ).comp I (KAM.realInclusion n).hasFDerivAt
  refine ⟨_, hc, fun v => ?_⟩
  have hv : KAM.realInclusion n v = ∑ j, (v j : ℂ) • (Pi.single j (1 : ℂ) : Fin n → ℂ) := by
    ext l; simp [Finset.sum_apply, Pi.single_apply]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars']
  rw [hv, map_sum]
  calc ‖∑ j, (fderiv ℂ (fun J => avgCoeff f J k) (KAM.realInclusion n I))
        ((v j : ℂ) • (Pi.single j (1 : ℂ) : Fin n → ℂ))‖
      ≤ ∑ j, ‖(fderiv ℂ (fun J => avgCoeff f J k) (KAM.realInclusion n I))
        ((v j : ℂ) • (Pi.single j (1 : ℂ) : Fin n → ℂ))‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin n, ‖v‖ * (2 / s * avgBeta s k) := Finset.sum_le_sum fun j _ => by
        rw [map_smul, norm_smul, Complex.norm_real]
        exact mul_le_mul (norm_le_pi_norm v j) (by simpa using (coef d).2.2.1 I hI k j)
          (norm_nonneg _) (norm_nonneg _)
    _ = n * (2 / s * avgBeta s k) * ‖v‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

/-- The scalar factor: value bound and derivative with its bound. -/
private theorem hasFDerivAt_aScal (d : AveragingData n R s h f) {κ M₂ : ℝ} (hκ : 0 < κ)
    (k : Fin n → ℤ) {I : Fin n → ℝ} (hI : I ∈ actionBall n R)
    (hM : ∀ i, ∑ j, |avgM h I i j| ≤ M₂) :
    HasFDerivAt (aScal h f κ k) (fderiv ℝ (aScal h f κ k) I) I ∧
    ‖aScal h f κ k I‖ ≤ avgBeta s k * |avgPsi κ (avgQ h k I)| ∧
    ∀ v, ‖fderiv ℝ (aScal h f κ k) I v‖ ≤ avgBeta s k *
      (2 * n / s * |avgPsi κ (avgQ h k I)| +
        M₂ * KAM.Fourier.modeSize k * |avgPsiD κ (avgQ h k I)|) * ‖v‖ := by
  obtain ⟨c', hc', hcb⟩ := hasFDerivAt_coeffR d k hI
  have hQ := hasFDerivAt_Q d k hI
  have hψ := ((corrector hκ).2 (avgQ h k I)).1.comp_hasFDerivAt I hQ
  have hψc := Complex.ofRealCLM.hasFDerivAt.comp I hψ
  have hprod := hc'.mul hψc
  have hA : HasFDerivAt (aScal h f κ k) _ I := hprod
  have hfd := hA.fderiv
  refine ⟨hA.differentiableAt.hasFDerivAt, ?_, fun v => ?_⟩
  · simp only [aScal, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right ((coef d).2.1 _ (real_mem d hI) k) (abs_nonneg _)
  · rw [hfd]
    have hβ := avgBeta_nonneg s k
    have hdQ := abs_dQ_le k hM v
    have hcv := hcb v
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hc0 : ‖avgCoeff f (KAM.realInclusion n I) k‖ ≤ avgBeta s k :=
      (coef d).2.1 _ (real_mem d hI) k
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.comp_apply, Complex.coe_smul, smul_eq_mul]
    refine (norm_add_le _ _).trans ?_
    have e1 : ‖avgCoeff f (KAM.realInclusion n I) k * Complex.ofRealCLM
        (avgPsiD κ (avgQ h k I) * (∑ i, (k i : ℝ) •
          (ContinuousLinearMap.proj i).comp (fderiv ℝ (KAM.frequencyMap h) I)) v)‖ =
        ‖avgCoeff f (KAM.realInclusion n I) k‖ * (|avgPsiD κ (avgQ h k I)| *
          |(∑ i, (k i : ℝ) • (ContinuousLinearMap.proj i).comp
            (fderiv ℝ (KAM.frequencyMap h) I)) v|) := by
      rw [norm_mul, Complex.ofRealCLM_apply, Complex.norm_real, Real.norm_eq_abs, abs_mul]
    have e2 : ‖(⇑Complex.ofRealCLM ∘ avgPsi κ ∘ avgQ h k) I * c' v‖ =
        |avgPsi κ (avgQ h k I)| * ‖c' v‖ := by
      simp [norm_mul]
    rw [e1, e2]
    have t1 : ‖avgCoeff f (KAM.realInclusion n I) k‖ * (|avgPsiD κ (avgQ h k I)| *
          |(∑ i, (k i : ℝ) • (ContinuousLinearMap.proj i).comp
            (fderiv ℝ (KAM.frequencyMap h) I)) v|) ≤
        avgBeta s k * (|avgPsiD κ (avgQ h k I)| * (KAM.Fourier.modeSize k * M₂ * ‖v‖)) :=
      mul_le_mul hc0 (mul_le_mul_of_nonneg_left hdQ (abs_nonneg _)) (by positivity) hβ
    have t2 : |avgPsi κ (avgQ h k I)| * ‖c' v‖ ≤
        |avgPsi κ (avgQ h k I)| * (n * (2 / s * avgBeta s k) * ‖v‖) :=
      mul_le_mul_of_nonneg_left hcv (abs_nonneg _)
    refine (add_le_add t1 t2).trans (le_of_eq ?_)
    ring

private theorem norm_aScal_le (d : AveragingData n R s h f) (κ : ℝ) (k : Fin n → ℤ)
    {I : Fin n → ℝ} (hI : I ∈ actionBall n R) :
    ‖aScal h f κ k I‖ ≤ avgBeta s k * |avgPsi κ (avgQ h k I)| := by
  simp only [aScal, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right ((coef d).2.1 _ (real_mem d hI) k) (abs_nonneg _)

private theorem norm_avgU_le (d : AveragingData n R s h f) (κ : ℝ) (k : Fin n → ℤ)
    {I : Fin n → ℝ} (hI : I ∈ actionBall n R) :
    ‖avgU h f κ k I‖ ≤ ‖fun j => (k j : ℝ)‖ * avgBeta s k * |avgPsi κ (avgQ h k I)| := by
  rw [avgU_eq, norm_smul, norm_kvec]
  calc ‖aScal h f κ k I‖ * ‖fun j => (k j : ℝ)‖
      ≤ (avgBeta s k * |avgPsi κ (avgQ h k I)|) * ‖fun j => (k j : ℝ)‖ :=
        mul_le_mul_of_nonneg_right (norm_aScal_le d κ k hI) (norm_nonneg _)
    _ = _ := by ring

/-- The summand of `avgW` (the sign included). -/
private def gk (h : (Fin n → ℂ) → ℂ) (f : AvgComplexPhase n → ℂ) (κ : ℝ) (k : Fin n → ℤ)
    (y : AvgPhase n) : Fin n → ℂ :=
  (-KAM.character k (KAM.realInclusion n y.1)) • avgU h f κ k y.2

/-- The real-linear form `θ ↦ 2πi k·θ`. -/
private def linK (k : Fin n → ℤ) : (Fin n → ℝ) →L[ℝ] ℂ :=
  ∑ j, (2 * Real.pi * Complex.I * (k j : ℂ)) • Complex.ofRealCLM.comp (ContinuousLinearMap.proj j)

private theorem linK_apply (k : Fin n → ℤ) (v : Fin n → ℝ) :
    linK k v = 2 * Real.pi * Complex.I * ∑ j, (k j : ℂ) * (v j : ℂ) := by
  simp [linK, Finset.mul_sum, mul_assoc]

private theorem character_real (k : Fin n → ℤ) (θ : Fin n → ℝ) :
    KAM.character k (KAM.realInclusion n θ) = Complex.exp (linK k θ) := by
  rw [linK_apply]; simp [KAM.character]

private theorem norm_character_real (k : Fin n → ℤ) (θ : Fin n → ℝ) :
    ‖KAM.character k (KAM.realInclusion n θ)‖ = 1 := by
  rw [KAM.norm_character]; simp

private theorem norm_linK_le (k : Fin n → ℤ) (v : Fin n → ℝ) :
    ‖linK k v‖ ≤ 2 * Real.pi * KAM.Fourier.modeSize k * ‖v‖ := by
  rw [linK_apply, norm_mul]
  have h1 : ‖2 * (Real.pi : ℂ) * Complex.I‖ = 2 * Real.pi := by
    simp [abs_of_pos Real.pi_pos]
  rw [h1]
  have key : ‖∑ j, (k j : ℂ) * (v j : ℂ)‖ ≤ KAM.Fourier.modeSize k * ‖v‖ := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ j, ‖(k j : ℂ) * (v j : ℂ)‖ ≤ ∑ j, |(k j : ℝ)| * ‖v‖ := Finset.sum_le_sum fun j _ => by
          rw [norm_mul]
          simp only [Complex.norm_intCast, Complex.norm_real, Int.cast_abs]
          exact mul_le_mul_of_nonneg_left (norm_le_pi_norm v j) (abs_nonneg _)
      _ = KAM.Fourier.modeSize k * ‖v‖ := by rw [← Finset.sum_mul]; rfl
  calc 2 * Real.pi * ‖∑ j, (k j : ℂ) * (v j : ℂ)‖
      ≤ 2 * Real.pi * (KAM.Fourier.modeSize k * ‖v‖) :=
        mul_le_mul_of_nonneg_left key (by positivity)
    _ = _ := by ring

private theorem hasFDerivAt_chi (k : Fin n → ℤ) (θ : Fin n → ℝ) :
    HasFDerivAt (fun θ : Fin n → ℝ => KAM.character k (KAM.realInclusion n θ))
      (KAM.character k (KAM.realInclusion n θ) • linK k) θ := by
  have := (Complex.hasDerivAt_exp (linK k θ)).comp_hasFDerivAt θ (linK k).hasFDerivAt
  rw [← character_real] at this
  convert this using 1
  · ext θ'; exact character_real k θ'

private theorem hasFDerivAt_gk (d : AveragingData n R s h f) {κ M₂ : ℝ} (hκ : 0 < κ)
    (k : Fin n → ℤ) {z : AvgPhase n} (hz : z ∈ avgDomain n R)
    (hM : ∀ i, ∑ j, |avgM h z.2 i j| ≤ M₂) :
    HasFDerivAt (gk h f κ k) (fderiv ℝ (gk h f κ k) z) z ∧
    (∀ v, fderiv ℝ (gk h f κ k) z v =
      (-KAM.character k (KAM.realInclusion n z.1)) •
        (fderiv ℝ (aScal h f κ k) z.2 v.2 • kvec k) +
      (-(KAM.character k (KAM.realInclusion n z.1) * linK k v.1)) • avgU h f κ k z.2) ∧
    ∀ v, ‖fderiv ℝ (gk h f κ k) z v‖ ≤
      (avgBterm h s M₂ κ k z.2 + 2 * Real.pi * KAM.Fourier.modeSize k *
        (‖fun j => (k j : ℝ)‖ * avgBeta s k * |avgPsi κ (avgQ h k z.2)|)) * ‖v‖ := by
  obtain ⟨hA, hAv, hAd⟩ := hasFDerivAt_aScal d hκ k hz.2 hM
  have hM0 : 0 ≤ M₂ := (Finset.sum_nonneg fun j _ => abs_nonneg _).trans (hM ⟨0, d.hn⟩)
  have hU : HasFDerivAt (fun I => avgU h f κ k I)
      ((fderiv ℝ (aScal h f κ k) z.2).smulRight (kvec k)) z.2 := by
    rw [avgU_eq]; exact hA.smul_const _
  have hUz := hU.comp z hasFDerivAt_snd
  have hχ := ((hasFDerivAt_chi k z.1).comp z hasFDerivAt_fst).neg
  have hg : HasFDerivAt (gk h f κ k) _ z := hχ.smul hUz
  have hform : ∀ v, fderiv ℝ (gk h f κ k) z v =
      (-KAM.character k (KAM.realInclusion n z.1)) •
        (fderiv ℝ (aScal h f κ k) z.2 v.2 • kvec k) +
      (-(KAM.character k (KAM.realInclusion n z.1) * linK k v.1)) • avgU h f κ k z.2 := by
    intro v
    rw [hg.fderiv]
    simp
  refine ⟨hg.differentiableAt.hasFDerivAt, hform, fun v => ?_⟩
  rw [hform v]
  refine (norm_add_le _ _).trans ?_
  have hβ := avgBeta_nonneg s k
  have h1 : ‖(-KAM.character k (KAM.realInclusion n z.1)) •
        (fderiv ℝ (aScal h f κ k) z.2 v.2 • kvec k)‖ ≤ avgBterm h s M₂ κ k z.2 * ‖v‖ := by
    rw [norm_smul, norm_neg, norm_character_real, one_mul, norm_smul, norm_kvec]
    calc ‖fderiv ℝ (aScal h f κ k) z.2 v.2‖ * ‖fun j => (k j : ℝ)‖
        ≤ (avgBeta s k * (2 * n / s * |avgPsi κ (avgQ h k z.2)| +
          M₂ * KAM.Fourier.modeSize k * |avgPsiD κ (avgQ h k z.2)|) * ‖v.2‖) *
            ‖fun j => (k j : ℝ)‖ := mul_le_mul_of_nonneg_right (hAd v.2) (norm_nonneg _)
      _ ≤ (avgBeta s k * (2 * n / s * |avgPsi κ (avgQ h k z.2)| +
          M₂ * KAM.Fourier.modeSize k * |avgPsiD κ (avgQ h k z.2)|) * ‖v‖) *
            ‖fun j => (k j : ℝ)‖ := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (norm_snd_le v) ?_)
            (norm_nonneg _)
          have h0 : 0 ≤ 2 * (n : ℝ) / s := by have := d.hs; positivity
          exact mul_nonneg hβ (add_nonneg (mul_nonneg h0 (abs_nonneg _))
            (mul_nonneg (mul_nonneg hM0 (KAM.Fourier.modeSize_nonneg k)) (abs_nonneg _)))
      _ = avgBterm h s M₂ κ k z.2 * ‖v‖ := by unfold avgBterm; ring
  have h2 : ‖(-(KAM.character k (KAM.realInclusion n z.1) * linK k v.1)) •
        avgU h f κ k z.2‖ ≤ 2 * Real.pi * KAM.Fourier.modeSize k *
        (‖fun j => (k j : ℝ)‖ * avgBeta s k * |avgPsi κ (avgQ h k z.2)|) * ‖v‖ := by
    rw [norm_smul, norm_neg, norm_mul, norm_character_real, one_mul]
    have hu := norm_avgU_le d κ k hz.2
    have hl := norm_linK_le k v.1
    have hm := KAM.Fourier.modeSize_nonneg k
    calc ‖linK k v.1‖ * ‖avgU h f κ k z.2‖
        ≤ (2 * Real.pi * KAM.Fourier.modeSize k * ‖v.1‖) *
          (‖fun j => (k j : ℝ)‖ * avgBeta s k * |avgPsi κ (avgQ h k z.2)|) :=
          mul_le_mul hl hu (norm_nonneg _) (by positivity)
      _ ≤ (2 * Real.pi * KAM.Fourier.modeSize k * ‖v‖) *
          (‖fun j => (k j : ℝ)‖ * avgBeta s k * |avgPsi κ (avgQ h k z.2)|) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (norm_fst_le v) (by positivity))
            (by positivity)
      _ = _ := by ring
  calc _ ≤ avgBterm h s M₂ κ k z.2 * ‖v‖ + 2 * Real.pi * KAM.Fourier.modeSize k *
        (‖fun j => (k j : ℝ)‖ * avgBeta s k * |avgPsi κ (avgQ h k z.2)|) * ‖v‖ := add_le_add h1 h2
    _ = _ := by ring

/-- The domination constant of the summands and their derivatives. -/
private def domC (n : ℕ) (s κ M₂ : ℝ) : ℝ := n / (s * κ) + M₂ / κ ^ 2 + Real.pi / κ + 1 / (2 * κ)

private theorem core_ineq {N s κ M₂ β a b p m : ℝ} (hκ : 0 < κ) (hs : 0 < s) (hN : 0 ≤ N)
    (hM : 0 ≤ M₂) (hβ : 0 ≤ β) (ha0 : 0 ≤ a) (ha : a ≤ 1 / (2 * κ)) (hb0 : 0 ≤ b)
    (hb : b ≤ κ⁻¹ ^ 2) (hp : 0 ≤ p) (hpm : p ≤ m) :
    p * β * (2 * N / s * a + M₂ * m * b) + 2 * Real.pi * m * (p * β * a) ≤
      (N / (s * κ) + M₂ / κ ^ 2 + Real.pi / κ + 1 / (2 * κ)) * ((1 + m) ^ 3 * β) ∧
    p * β * a ≤ (N / (s * κ) + M₂ / κ ^ 2 + Real.pi / κ + 1 / (2 * κ)) * ((1 + m) ^ 3 * β) := by
  have hm : 0 ≤ m := hp.trans hpm
  have hw : 1 ≤ 1 + m := by linarith
  have hw0 : 0 ≤ 1 + m := by linarith
  have h1 : 1 + m ≤ (1 + m) ^ 2 := by nlinarith
  have h2 : (1 + m) ^ 2 ≤ (1 + m) ^ 3 := by nlinarith [sq_nonneg (1 + m)]
  have hpw : p ≤ 1 + m := by linarith
  have hc : 0 ≤ N / (s * κ) + M₂ / κ ^ 2 + Real.pi / κ + 1 / (2 * κ) := by positivity
  have hQ : 0 ≤ 2 * N / s := by positivity
  have hpi := Real.pi_pos
  constructor
  · calc p * β * (2 * N / s * a + M₂ * m * b) + 2 * Real.pi * m * (p * β * a)
        ≤ (1 + m) * β * (2 * N / s * (1 / (2 * κ)) + M₂ * (1 + m) * κ⁻¹ ^ 2) +
          2 * Real.pi * (1 + m) * ((1 + m) * β * (1 / (2 * κ))) := by
          gcongr <;> linarith
      _ = β * (N / (s * κ) * (1 + m) + M₂ / κ ^ 2 * (1 + m) ^ 2 +
          Real.pi / κ * (1 + m) ^ 2) := by field_simp
      _ ≤ β * (N / (s * κ) * (1 + m) ^ 3 + M₂ / κ ^ 2 * (1 + m) ^ 3 +
          Real.pi / κ * (1 + m) ^ 3) := by gcongr <;> linarith
      _ ≤ _ := by
          have : 0 ≤ 1 / (2 * κ) := by positivity
          nlinarith [mul_nonneg this (mul_nonneg (pow_nonneg hw0 3) hβ)]
  · calc p * β * a ≤ (1 + m) * β * (1 / (2 * κ)) := by
          gcongr
      _ ≤ (1 / (2 * κ)) * ((1 + m) ^ 3 * β) := by
          have : 0 ≤ 1 / (2 * κ) := by positivity
          nlinarith [mul_nonneg this hβ]
      _ ≤ _ := by
          have : 0 ≤ N / (s * κ) + M₂ / κ ^ 2 + Real.pi / κ := by positivity
          nlinarith [mul_nonneg this (mul_nonneg (pow_nonneg hw0 3) hβ),
            mul_nonneg (by positivity : (0:ℝ) ≤ 1 / (2 * κ)) (mul_nonneg (pow_nonneg hw0 3) hβ)]

private theorem avgBterm_nonneg (d : AveragingData n R s h f) {M₂ κ : ℝ} (hM0 : 0 ≤ M₂)
    (k : Fin n → ℤ) (I : Fin n → ℝ) : 0 ≤ avgBterm h s M₂ κ k I := by
  have h0 : 0 ≤ 2 * (n : ℝ) / s := by have := d.hs; positivity
  exact mul_nonneg (mul_nonneg (norm_nonneg _) (avgBeta_nonneg s k))
    (add_nonneg (mul_nonneg h0 (abs_nonneg _))
      (mul_nonneg (mul_nonneg hM0 (KAM.Fourier.modeSize_nonneg k)) (abs_nonneg _)))

private theorem psi_bounds {κ : ℝ} (hκ : 0 < κ) (y : ℝ) :
    |avgPsi κ y| ≤ 1 / (2 * κ) ∧ |avgPsiD κ y| ≤ κ⁻¹ ^ 2 :=
  ⟨((corrector hκ).2 y).2.1, ((corrector hκ).2 y).2.2.1⟩

/-- Pointwise domination of the summand and of its derivative on `avgDomain`. -/
private theorem gk_dom (d : AveragingData n R s h f) {M₂ κ : ℝ} (hκ : 0 < κ) (hM0 : 0 ≤ M₂)
    {z : AvgPhase n} (hz : z ∈ avgDomain n R) (k : Fin n → ℤ)
    (hM : ∀ i, ∑ j, |avgM h z.2 i j| ≤ M₂) :
    ‖gk h f κ k z‖ ≤ domC n s κ M₂ * ((1 + KAM.Fourier.modeSize k) ^ 3 * avgBeta s k) ∧
    ‖fderiv ℝ (gk h f κ k) z‖ ≤
      domC n s κ M₂ * ((1 + KAM.Fourier.modeSize k) ^ 3 * avgBeta s k) := by
  have hb := psi_bounds hκ (avgQ h k z.2)
  have hc := core_ineq (N := n) (β := avgBeta s k) (p := ‖fun j => (k j : ℝ)‖)
    (m := KAM.Fourier.modeSize k) (M₂ := M₂) (κ := κ) (s := s) hκ d.hs (Nat.cast_nonneg n) hM0
    (avgBeta_nonneg s k) (abs_nonneg _) hb.1 (abs_nonneg _) hb.2 (norm_nonneg _) (norm_k_le k)
  refine ⟨?_, ?_⟩
  · calc ‖gk h f κ k z‖ = ‖avgU h f κ k z.2‖ := by
          simp [gk, norm_smul, norm_character_real]
      _ ≤ _ := (norm_avgU_le d κ k hz.2).trans hc.2
  · refine ContinuousLinearMap.opNorm_le_bound _ ?_ fun v => ?_
    · have : 0 ≤ domC n s κ M₂ := by unfold domC; have := d.hs; positivity
      exact mul_nonneg this (mul_nonneg (by have := KAM.Fourier.modeSize_nonneg k; positivity)
        (avgBeta_nonneg s k))
    · exact (hasFDerivAt_gk d hκ k hz hM).2.2 v |>.trans
        (mul_le_mul_of_nonneg_right hc.1 (norm_nonneg v))

private theorem avgW_eq (κ : ℝ) : avgW h f κ = fun y => ∑' k, gk h f κ k y := by
  funext y; simp [avgW, gk, neg_smul, tsum_neg]

private theorem mem_closedBall_of_dom {z : AvgPhase n} (hz : z ∈ avgDomain n R) :
    z.2 ∈ closedBall (0 : Fin n → ℝ) R := ball_subset_closedBall hz.2

private theorem isOpen_avgDomain (n : ℕ) (R : ℝ) : IsOpen (avgDomain n R) :=
  isOpen_univ.prod isOpen_ball

private theorem isPreconnected_avgDomain (n : ℕ) (R : ℝ) : IsPreconnected (avgDomain n R) :=
  (convex_univ.prod (convex_ball _ _)).isPreconnected

private theorem summable_dom (d : AveragingData n R s h f) (C : ℝ) :
    Summable fun k : Fin n → ℤ => C * ((1 + KAM.Fourier.modeSize k) ^ 3 * avgBeta s k) :=
  (coef d).2.2.2.2.2.mul_left C

/-- Termwise differentiation of the corrector series at every point of the domain. -/
private theorem hasFDerivAt_avgW (d : AveragingData n R s h f) {M₂ κ : ℝ} (hκ : 0 < κ)
    (hM : ∀ I ∈ closedBall (0 : Fin n → ℝ) R, ∀ i, ∑ j, |avgM h I i j| ≤ M₂) {z : AvgPhase n}
    (hz : z ∈ avgDomain n R) :
    HasFDerivAt (avgW h f κ) (∑' k, fderiv ℝ (gk h f κ k) z) z ∧
    HasSum (fun k => fderiv ℝ (gk h f κ k) z) (∑' k, fderiv ℝ (gk h f κ k) z) := by
  have hM0 : 0 ≤ M₂ := (Finset.sum_nonneg fun j _ => abs_nonneg _).trans
    (hM 0 (by simpa using d.hR.le) ⟨0, d.hn⟩)
  have hdom : ∀ k, ∀ x ∈ avgDomain n R, ‖gk h f κ k x‖ ≤
      domC n s κ M₂ * ((1 + KAM.Fourier.modeSize k) ^ 3 * avgBeta s k) ∧
      ‖fderiv ℝ (gk h f κ k) x‖ ≤
      domC n s κ M₂ * ((1 + KAM.Fourier.modeSize k) ^ 3 * avgBeta s k) :=
    fun k x hx => gk_dom d hκ hM0 hx k (hM x.2 (mem_closedBall_of_dom hx))
  have hsum := summable_dom d (domC n s κ M₂)
  refine ⟨?_, (Summable.of_norm_bounded hsum fun k => (hdom k z hz).2).hasSum⟩
  rw [avgW_eq]
  exact hasFDerivAt_tsum_of_isPreconnected hsum (isOpen_avgDomain n R) (isPreconnected_avgDomain n R)
    (fun k x hx => (hasFDerivAt_gk d hκ k hx (hM x.2 (mem_closedBall_of_dom hx))).1)
    (fun k x hx => (hdom k x hx).2) hz
    (Summable.of_norm_bounded hsum fun k => (hdom k z hz).1) hz

end KAM.Nekhoroshev

end
