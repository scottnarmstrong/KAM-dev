/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Strip.Regularity
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Averages of periodic functions

Torus averages use Lebesgue measure on the closed unit cube, matching the frozen
torsion average. Fubini and the fundamental theorem of calculus show that a periodic
coordinate derivative has zero average. All finite products carry their usual sup norm.
-/

public noncomputable section

open Set MeasureTheory
open scoped ContDiff

namespace KAM

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- The normalized torus average, written on the closed unit cube. -/
@[expose] def torusAverage (f : (Fin n → ℝ) → F) : F :=
  ∫ x in Set.pi Set.univ (fun _ : Fin n => Icc (0 : ℝ) 1), f x

/-- The unit cube has volume one, including in dimension zero. -/
theorem volume_unitCube (n : ℕ) :
    volume (Set.pi Set.univ (fun _ : Fin n => Icc (0 : ℝ) 1)) = 1 := by
  rw [volume_pi_pi]
  simp

omit [CompleteSpace F] in
/-- Averaging does not increase a uniform norm bound. -/
theorem norm_torusAverage_le {f : (Fin n → ℝ) → F} {A : ℝ}
    (hA : ∀ x ∈ Set.pi Set.univ (fun _ : Fin n => Icc (0 : ℝ) 1), ‖f x‖ ≤ A) :
    ‖torusAverage f‖ ≤ A := by
  have h := norm_setIntegral_le_of_norm_le_const
    (show volume (Set.pi Set.univ (fun _ : Fin n => Icc (0 : ℝ) 1)) < ⊤ by
      rw [volume_unitCube]; exact ENNReal.one_lt_top) hA
  rw [measureReal_def, volume_unitCube, ENNReal.toReal_one, mul_one] at h
  exact h

private theorem hasDerivAt_insertNth (i : Fin (n + 1)) (y : Fin n → ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => i.insertNth (α := fun _ => ℝ) s y)
      (Pi.single i 1) t := by
  apply hasDerivAt_pi.mpr
  intro j
  refine i.succAboveCases ?_ (fun k => ?_) j
  · simpa using! hasDerivAt_id t
  · simpa [Pi.single_apply, Fin.succAbove_ne] using hasDerivAt_const t (y k)

private theorem insertNth_one (i : Fin (n + 1)) (y : Fin n → ℝ) :
    i.insertNth (α := fun _ => ℝ) 1 y = i.insertNth 0 y + Pi.single i 1 := by
  ext j
  refine i.succAboveCases ?_ (fun k => ?_) j
  · simp
  · simp [Fin.succAbove_ne]

private theorem torusAverage_coordinate_succ_eq_zero
    {f : (Fin (n + 1) → ℝ) → F}
    {f' : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) →L[ℝ] F}
    (hd : ∀ x, HasFDerivAt f (f' x) x) (hc : Continuous f') (i : Fin (n + 1))
    (hp : ∀ x, f (x + Pi.single i 1) = f x) :
    torusAverage (fun x => f' x (Pi.single i 1)) = 0 := by
  let μ : Measure ℝ := volume.restrict (Icc 0 1)
  let g := fun x => f' x (Pi.single i 1)
  have hg : Continuous g := hc.clm_apply continuous_const
  have hgi : Integrable g (Measure.pi (fun _ : Fin (n + 1) => μ)) := by
    rw [← Measure.restrict_pi_pi]
    apply hg.continuousOn.integrableOn_compact
    rw [pi_univ_Icc]
    exact isCompact_Icc
  have hpres := (measurePreserving_piFinSuccAbove
    (fun _ : Fin (n + 1) => μ) i).symm
  have hcomp := (hpres.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).mpr hgi
  dsimp only [Function.comp_def] at hcomp
  change (∫ x, g x ∂volume.restrict (Set.pi Set.univ (fun _ => Icc 0 1))) = 0
  change (∫ x, g x ∂(Measure.pi (fun _ => volume)).restrict
    (Set.pi Set.univ (fun _ => Icc 0 1))) = 0
  rw [Measure.restrict_pi_pi, ← hpres.integral_comp' g,
    integral_prod_symm _ hcomp]
  have hline : ∀ y : Fin n → ℝ, ∫ t, g (i.insertNth t y) ∂μ = 0 := by
    intro y
    have hdline : ∀ t : ℝ, HasDerivAt (fun s => f (i.insertNth s y))
        (g (i.insertNth t y)) t := fun t =>
      (hd _).comp_hasDerivAt t (hasDerivAt_insertNth i y t)
    have hcline : Continuous (fun t : ℝ => g (i.insertNth t y)) :=
      hg.comp (continuous_iff_continuousAt.mpr fun t =>
        (hasDerivAt_insertNth i y t).continuousAt)
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => hdline t) (hcline.intervalIntegrable 0 1)
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
      ← integral_Icc_eq_integral_Ioc, insertNth_one, hp, sub_self] at hFTC
    exact hFTC
  change (∫ y, ∫ t, g (i.insertNth t y) ∂μ ∂Measure.pi (fun _ : Fin n => μ)) = 0
  simp only [hline, integral_zero]

/-- A continuously differentiable periodic function has mean-zero coordinate derivatives. -/
theorem torusAverage_coordinate_eq_zero {f : (Fin n → ℝ) → F}
    {f' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] F}
    (hd : ∀ x, HasFDerivAt f (f' x) x) (hc : Continuous f') (i : Fin n)
    (hp : ∀ x, f (x + Pi.single i 1) = f x) :
    torusAverage (fun x => f' x (Pi.single i 1)) = 0 := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n => exact torusAverage_coordinate_succ_eq_zero hd hc i hp

omit [NormedSpace ℝ F] [CompleteSpace F] in
/-- A continuous function is integrable on the averaging cube. -/
theorem integrableOn_unitCube_of_continuous {f : (Fin n → ℝ) → F} (hf : Continuous f) :
    IntegrableOn f (Set.pi Set.univ (fun _ : Fin n => Icc (0 : ℝ) 1)) := by
  apply hf.continuousOn.integrableOn_compact
  rw [pi_univ_Icc]
  exact isCompact_Icc

/-- Every constant real direction also has a mean-zero derivative. -/
theorem torusAverage_direction_eq_zero {f : (Fin n → ℝ) → F}
    {f' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] F}
    (hd : ∀ x, HasFDerivAt f (f' x) x) (hc : Continuous f')
    (hp : ∀ (i : Fin n) x, f (x + Pi.single i 1) = f x) (omega : Fin n → ℝ) :
    torusAverage (fun x => f' x omega) = 0 := by
  have hi := integrableOn_unitCube_of_continuous hc
  have heval : ∀ v, torusAverage (fun x => f' x v) = torusAverage f' v := fun v =>
    (ContinuousLinearMap.integral_apply hi v).symm
  have hcoord : ∀ i : Fin n, torusAverage f' (Pi.single i 1) = 0 := by
    intro i
    rw [← heval]
    exact torusAverage_coordinate_eq_zero hd hc i (hp i)
  rw [heval, pi_eq_sum_univ' omega, map_sum]
  simp only [map_smul, hcoord, smul_zero, Finset.sum_const_zero]

/-- The derivative-average identity with the derivative supplied by `fderiv`. -/
theorem torusAverage_fderiv_eq_zero {f : (Fin n → ℝ) → F} (hf : ContDiff ℝ 1 f)
    (hp : ∀ (i : Fin n) x, f (x + Pi.single i 1) = f x) (omega : Fin n → ℝ) :
    torusAverage (fun x => fderiv ℝ f x omega) = 0 :=
  torusAverage_direction_eq_zero (fun x => (hf.differentiable one_ne_zero x).hasFDerivAt)
    (hf.continuous_fderiv one_ne_zero) hp omega

section Complex

variable [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F] [SecondCountableTopology F]

/-- Real points belong to every strip of positive width. -/
theorem ofReal_mem_complexStrip {ρ : ℝ} (hρ : 0 < ρ) (x : Fin n → ℝ) :
    (fun i => (x i : ℂ)) ∈ complexStrip n ρ := by
  intro i
  simpa using hρ

omit [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F] in
/-- The complex derivative is continuous along the real torus. -/
theorem continuous_fderiv_real_of_holomorphic {ρ : ℝ} (hρ : 0 < ρ)
    {f : (Fin n → ℂ) → F} (hf : DifferentiableOn ℂ f (complexStrip n ρ)) :
    Continuous (fun x : Fin n → ℝ => fderiv ℂ f (fun i => (x i : ℂ))) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  have hc := (differentiableOn_fderiv_of_isOpen_pi (isOpen_complexStrip n ρ) hf).continuousOn
  exact (hc.continuousAt ((isOpen_complexStrip n ρ).mem_nhds
    (ofReal_mem_complexStrip hρ x))).comp
      (continuous_pi (fun i => Complex.continuous_ofReal.comp (continuous_apply i))).continuousAt

/-- A coordinate derivative of a periodic holomorphic function has zero torus average.
Continuity of the derivative is proved from holomorphy, not assumed. -/
theorem torusAverage_complex_coordinate_eq_zero {ρ : ℝ} (hρ : 0 < ρ)
    {f : (Fin n → ℂ) → F} (hf : DifferentiableOn ℂ f (complexStrip n ρ)) (i : Fin n)
    (hp : ∀ z ∈ complexStrip n ρ, f (z + Pi.single i 1) = f z) :
    torusAverage (fun x : Fin n → ℝ =>
      fderiv ℂ f (fun j => (x j : ℂ)) (Pi.single i 1)) = 0 := by
  let L : (Fin n → ℝ) →L[ℝ] (Fin n → ℂ) :=
    ContinuousLinearMap.pi fun j => Complex.ofRealCLM.comp (ContinuousLinearMap.proj j)
  let g' := fun x => ((fderiv ℂ f (L x)).restrictScalars ℝ).comp L
  have hd : ∀ x, HasFDerivAt (fun y => f (L y)) (g' x) x := fun x =>
    ((hf.differentiableAt ((isOpen_complexStrip n ρ).mem_nhds
      (ofReal_mem_complexStrip hρ x))).hasFDerivAt.restrictScalars ℝ).comp x
        L.hasFDerivAt
  have hc : Continuous g' :=
    ((ContinuousLinearMap.isEmbedding_restrictScalars ℝ).continuous.comp
      (continuous_fderiv_real_of_holomorphic hρ hf)).clm_comp continuous_const
  have hperiod : ∀ x, f (L (x + Pi.single i 1)) = f (L x) := by
    intro x
    convert hp (L x) (ofReal_mem_complexStrip hρ x) using 2
    ext j
    by_cases hij : j = i <;> simp [L, hij]
  have hzero := torusAverage_coordinate_eq_zero hd hc i hperiod
  have hsingle : L (Pi.single i 1) = Pi.single i 1 := by
    ext j
    by_cases hij : j = i <;> simp [L, hij]
  simpa only [g', ContinuousLinearMap.comp_apply, hsingle] using! hzero

/-- Every constant complex direction has mean-zero derivative on the real torus. -/
theorem torusAverage_complex_direction_eq_zero {ρ : ℝ} (hρ : 0 < ρ)
    {f : (Fin n → ℂ) → F} (hf : DifferentiableOn ℂ f (complexStrip n ρ))
    (hp : ∀ (i : Fin n) z, z ∈ complexStrip n ρ → f (z + Pi.single i 1) = f z)
    (omega : Fin n → ℂ) :
    torusAverage (fun x : Fin n → ℝ => fderiv ℂ f (fun i => (x i : ℂ)) omega) = 0 := by
  let g := fun x : Fin n → ℝ => fderiv ℂ f (fun i => (x i : ℂ))
  have hi := integrableOn_unitCube_of_continuous
    (continuous_fderiv_real_of_holomorphic hρ hf)
  have heval : ∀ v, torusAverage (fun x => g x v) = torusAverage g v := fun v =>
    (ContinuousLinearMap.integral_apply hi v).symm
  have hcoord : ∀ i : Fin n, torusAverage g (Pi.single i 1) = 0 := by
    intro i
    rw [← heval]
    exact torusAverage_complex_coordinate_eq_zero hρ hf i (hp i)
  change torusAverage (fun x => g x omega) = 0
  rw [heval, pi_eq_sum_univ' omega, map_sum]
  simp only [map_smul, hcoord, smul_zero, Finset.sum_const_zero]

omit [CompleteSpace F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
  [SecondCountableTopology F] in
/-- Averaging a function obeys its strip sup-norm bound. -/
theorem norm_torusAverage_le_of_strip_bound {ρ A : ℝ} (hρ : 0 < ρ)
    {f : (Fin n → ℂ) → F} (hA : ∀ z ∈ complexStrip n ρ, ‖f z‖ ≤ A) :
    ‖torusAverage (fun x : Fin n → ℝ => f (fun i => (x i : ℂ)))‖ ≤ A :=
  norm_torusAverage_le (fun x _ => hA _ (ofReal_mem_complexStrip hρ x))

end Complex

end KAM

end
