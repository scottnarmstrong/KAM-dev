/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.Analysis.Analytic.CPolynomial
public import KAM.Wave.Normal.Analysis.CubicHeadline

/-!
# The cubic gradient as a continuous cubic polynomial on `ℓ²`
(blueprint `bpW:w0n:cubic-bound`, `stepW:w0n:analytic`)

Infrastructure used by several nodes; the dependency graph is still being built.

`KAM.Wave.waveCubicMultilinear` is the continuous trilinear map `T` in the weighted `ℓ²`
coordinates (`(T(y₁,y₂,y₃))_l = ω_{1,2}(l) T(q₁,q₂,q₃)_l`, `q_i = coeff y_i`), with norm
`≤ C_m` (`KAM.Wave.waveCubicMultilinear_norm_le`). Its diagonal `KAM.Wave.waveCubicLp` is real
analytic (`KAM.Wave.waveCubicLp_analyticOnNhd`) and gives the weighted coordinates of `𝒢(coeff y)`
(`KAM.Wave.waveCubicLp_apply`).
-/

@[expose] public noncomputable section

open Real
open scoped ENNReal

namespace KAM.Wave

lemma coeff_add (y z : lp (fun _ : ℕ+ => ℝ) 2) (j : ℕ+) :
    coeff (y + z) j = coeff y j + coeff z j := by
  simp [coeff, add_div]

lemma coeff_smul (c : ℝ) (y : lp (fun _ : ℕ+ => ℝ) 2) (j : ℕ+) :
    coeff (c • y) j = c * coeff y j := by
  simp [coeff, mul_div_assoc]

lemma wave_fin3_ne_01 : (0 : Fin 3) ≠ 1 := by decide

lemma wave_fin3_ne_02 : (0 : Fin 3) ≠ 2 := by decide

lemma wave_fin3_ne_10 : (1 : Fin 3) ≠ 0 := by decide

lemma wave_fin3_ne_12 : (1 : Fin 3) ≠ 2 := by decide

lemma wave_fin3_ne_20 : (2 : Fin 3) ≠ 0 := by decide

lemma wave_fin3_ne_21 : (2 : Fin 3) ≠ 1 := by decide

section Aux

variable (m : ℝ) (hm : 0 < m)

/-- The trilinear map `T` in `ℓ²` coordinates. -/
def waveCubicAux (y₁ y₂ y₃ : lp (fun _ : ℕ+ => ℝ) 2) : lp (fun _ : ℕ+ => ℝ) 2 :=
  ⟨fun l => ellWeight 1 2 l * waveTrilinear m hm (coeff y₁) (coeff y₂) (coeff y₃) l, by
    have h := (wave_trilinear_bound m hm zero_le_one (by norm_num) (waveEll_coeff y₁)
      (waveEll_coeff y₂) (waveEll_coeff y₃)).2.1
    have two : (1 : ℝ) + 1 = 2 := by norm_num
    rw [two] at h
    exact memℓp_two_of_waveEll h⟩

lemma waveCubicAux_apply (y₁ y₂ y₃ : lp (fun _ : ℕ+ => ℝ) 2) (l : ℕ+) :
    waveCubicAux m hm y₁ y₂ y₃ l =
      ellWeight 1 2 l * waveTrilinear m hm (coeff y₁) (coeff y₂) (coeff y₃) l := rfl

lemma coeff_add_fun (y z : lp (fun _ : ℕ+ => ℝ) 2) :
    coeff (y + z) = fun j => coeff y j + coeff z j := funext (coeff_add y z)

lemma coeff_smul_fun (c : ℝ) (y : lp (fun _ : ℕ+ => ℝ) 2) :
    coeff (c • y) = fun j => c * coeff y j := funext (coeff_smul c y)

theorem waveCubicAux_add_left (y z y₂ y₃ : lp (fun _ : ℕ+ => ℝ) 2) :
    waveCubicAux m hm (y + z) y₂ y₃ = waveCubicAux m hm y y₂ y₃ + waveCubicAux m hm z y₂ y₃ := by
  ext l
  simp only [lp.coeFn_add, Pi.add_apply, waveCubicAux_apply, coeff_add_fun]
  rw [waveTrilinear_add_left m hm zero_le_one (by norm_num) (waveEll_coeff y) (waveEll_coeff z)
    (waveEll_coeff y₂) (waveEll_coeff y₃)]
  ring

theorem waveCubicAux_add_mid (y y₂ z y₃ : lp (fun _ : ℕ+ => ℝ) 2) :
    waveCubicAux m hm y (y₂ + z) y₃ = waveCubicAux m hm y y₂ y₃ + waveCubicAux m hm y z y₃ := by
  ext l
  simp only [lp.coeFn_add, Pi.add_apply, waveCubicAux_apply, coeff_add_fun]
  rw [waveTrilinear_add_mid m hm zero_le_one (by norm_num) (waveEll_coeff y) (waveEll_coeff y₂)
    (waveEll_coeff z) (waveEll_coeff y₃)]
  ring

theorem waveCubicAux_add_right (y y₂ y₃ z : lp (fun _ : ℕ+ => ℝ) 2) :
    waveCubicAux m hm y y₂ (y₃ + z) = waveCubicAux m hm y y₂ y₃ + waveCubicAux m hm y y₂ z := by
  ext l
  simp only [lp.coeFn_add, Pi.add_apply, waveCubicAux_apply, coeff_add_fun]
  rw [waveTrilinear_add_right m hm zero_le_one (by norm_num) (waveEll_coeff y) (waveEll_coeff y₂)
    (waveEll_coeff y₃) (waveEll_coeff z)]
  ring

theorem waveCubicAux_smul_left (c : ℝ) (y y₂ y₃ : lp (fun _ : ℕ+ => ℝ) 2) :
    waveCubicAux m hm (c • y) y₂ y₃ = c • waveCubicAux m hm y y₂ y₃ := by
  ext l
  simp only [lp.coeFn_smul, Pi.smul_apply, waveCubicAux_apply, coeff_smul_fun,
    waveTrilinear_smul_left, smul_eq_mul]
  ring

theorem waveCubicAux_smul_mid (c : ℝ) (y y₂ y₃ : lp (fun _ : ℕ+ => ℝ) 2) :
    waveCubicAux m hm y (c • y₂) y₃ = c • waveCubicAux m hm y y₂ y₃ := by
  ext l
  simp only [lp.coeFn_smul, Pi.smul_apply, waveCubicAux_apply, coeff_smul_fun,
    waveTrilinear_smul_mid, smul_eq_mul]
  ring

theorem waveCubicAux_smul_right (c : ℝ) (y y₂ y₃ : lp (fun _ : ℕ+ => ℝ) 2) :
    waveCubicAux m hm y y₂ (c • y₃) = c • waveCubicAux m hm y y₂ y₃ := by
  ext l
  simp only [lp.coeFn_smul, Pi.smul_apply, waveCubicAux_apply, coeff_smul_fun,
    waveTrilinear_smul_right, smul_eq_mul]
  ring

theorem waveCubicAux_norm_le (y₁ y₂ y₃ : lp (fun _ : ℕ+ => ℝ) 2) :
    ‖waveCubicAux m hm y₁ y₂ y₃‖ ≤ waveCubicHeadlineConst * (‖y₁‖ * ‖y₂‖ * ‖y₃‖) := by
  have h := (wave_trilinear_bound m hm zero_le_one (by norm_num) (waveEll_coeff y₁)
    (waveEll_coeff y₂) (waveEll_coeff y₃)).2.2
  have two : (1 : ℝ) + 1 = 2 := by norm_num
  rw [two, waveCubicConst_one] at h
  rw [lp_norm_eq_sqrt, norm_eq_waveEllNorm_coeff, norm_eq_waveEllNorm_coeff,
    norm_eq_waveEllNorm_coeff]
  convert h using 2
  unfold waveEllNorm
  congr 1

end Aux

variable (m : ℝ) (hm : 0 < m)

/-- The continuous trilinear map `T` on `ℓ²` (weighted coordinates). -/
def waveCubicMultilinear :
    ContinuousMultilinearMap ℝ (fun _ : Fin 3 => lp (fun _ : ℕ+ => ℝ) 2)
      (lp (fun _ : ℕ+ => ℝ) 2) :=
  MultilinearMap.mkContinuous
    { toFun := fun v => waveCubicAux m hm (v 0) (v 1) (v 2)
      map_update_add' := fun v i x y => by
        match i with
        | 0 =>
          simp only [Function.update_self,
            Function.update_of_ne wave_fin3_ne_10,
            Function.update_of_ne wave_fin3_ne_20]
          exact waveCubicAux_add_left m hm x y (v 1) (v 2)
        | 1 =>
          simp only [Function.update_self,
            Function.update_of_ne wave_fin3_ne_01,
            Function.update_of_ne wave_fin3_ne_21]
          exact waveCubicAux_add_mid m hm (v 0) x y (v 2)
        | 2 =>
          simp only [Function.update_self,
            Function.update_of_ne wave_fin3_ne_02,
            Function.update_of_ne wave_fin3_ne_12]
          exact waveCubicAux_add_right m hm (v 0) (v 1) x y
      map_update_smul' := fun v i c x => by
        match i with
        | 0 =>
          simp only [Function.update_self,
            Function.update_of_ne wave_fin3_ne_10,
            Function.update_of_ne wave_fin3_ne_20]
          exact waveCubicAux_smul_left m hm c x (v 1) (v 2)
        | 1 =>
          simp only [Function.update_self,
            Function.update_of_ne wave_fin3_ne_01,
            Function.update_of_ne wave_fin3_ne_21]
          exact waveCubicAux_smul_mid m hm c (v 0) x (v 2)
        | 2 =>
          simp only [Function.update_self,
            Function.update_of_ne wave_fin3_ne_02,
            Function.update_of_ne wave_fin3_ne_12]
          exact waveCubicAux_smul_right m hm c (v 0) (v 1) x }
    waveCubicHeadlineConst (fun v => by
      simpa [Fin.prod_univ_three, mul_assoc] using waveCubicAux_norm_le m hm (v 0) (v 1) (v 2))

lemma waveCubicMultilinear_apply (v : Fin 3 → lp (fun _ : ℕ+ => ℝ) 2) :
    waveCubicMultilinear m hm v = waveCubicAux m hm (v 0) (v 1) (v 2) := rfl

lemma waveCubicHeadlineConst_nonneg : 0 ≤ waveCubicHeadlineConst := by
  unfold waveCubicHeadlineConst
  have : 0 ≤ ∑' n : ℕ+, ((n : ℝ) ^ 3)⁻¹ := tsum_nonneg fun n => by positivity
  positivity

theorem waveCubicMultilinear_norm_le : ‖waveCubicMultilinear m hm‖ ≤ waveCubicHeadlineConst :=
  MultilinearMap.mkContinuous_norm_le _ waveCubicHeadlineConst_nonneg _

/-- The diagonal `y ↦ T(y,y,y)`: the weighted coordinates of `𝒢(coeff y)`. -/
def waveCubicLp (y : lp (fun _ : ℕ+ => ℝ) 2) : lp (fun _ : ℕ+ => ℝ) 2 :=
  waveCubicMultilinear m hm fun _ => y

theorem waveCubicLp_apply (y : lp (fun _ : ℕ+ => ℝ) 2) (l : ℕ+) :
    waveCubicLp m hm y l = ellWeight 1 2 l * waveCubic m hm (coeff y) l := by
  have := waveCubic_eq_trilinear m hm one_pos (waveEll_coeff y) l
  simp [waveCubicLp, waveCubicMultilinear_apply, waveCubicAux_apply, this]

theorem waveCubicLp_norm_le (y : lp (fun _ : ℕ+ => ℝ) 2) :
    ‖waveCubicLp m hm y‖ ≤ waveCubicHeadlineConst * ‖y‖ ^ 3 := by
  simpa [waveCubicLp, waveCubicMultilinear_apply, pow_succ, mul_assoc] using
    waveCubicAux_norm_le m hm y y y

/-- `bpW:w0n:cubic-bound`: the cubic gradient is a real analytic (indeed a continuous cubic
polynomial) map `ℓ² → ℓ²` in the weighted coordinates. -/
theorem waveCubicLp_analyticOnNhd : AnalyticOnNhd ℝ (waveCubicLp m hm) Set.univ := by
  intro y _
  have hdiag : AnalyticAt ℝ (fun y : lp (fun _ : ℕ+ => ℝ) 2 => fun _ : Fin 3 => y) y :=
    (ContinuousLinearMap.pi fun _ : Fin 3 =>
      ContinuousLinearMap.id ℝ (lp (fun _ : ℕ+ => ℝ) 2)).analyticAt y
  have hM := ((waveCubicMultilinear m hm).cpolynomialAt (x := fun _ : Fin 3 => y)).analyticAt
  exact hM.comp hdiag

end KAM.Wave

end
