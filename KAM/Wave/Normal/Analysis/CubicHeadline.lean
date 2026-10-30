/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.Analysis.Analytic.CPolynomial
public import KAM.Wave.Normal.Analysis.CubicLinear

/-!
# The cubic gradient on `ℓ^{1,1}`: boundedness and analyticity
(blueprint `bpW:w0n:cubic-bound`, headline case `a = p = 1`)

Infrastructure used by several nodes; the dependency graph is still being built.

In the weighted `ℓ²` coordinates of `KAM.Wave.WaveSpace` (`q = coeff y`):

* `KAM.Wave.wave_cubic_bound`: `𝒢(q) ∈ ℓ^{1,2}` and `‖𝒢(q)‖_{1,2} ≤ C_m ‖q‖_{1,1}³`,
  `C_m = 8 (1 + 2ζ(3)) / π` (`KAM.Wave.waveCubicHeadlineConst`); the same for the frozen
  `KAM.Wave.cubicGrad` (`KAM.Wave.cubicGrad_mem_ell`, `KAM.Wave.cubicGrad_norm_le`);
* `KAM.Wave.waveCubicMultilinear`: the continuous trilinear map `T` in `ℓ²` coordinates and
  `KAM.Wave.waveCubicLp y = T(y,y,y)`, the weighted coordinates of `𝒢(coeff y)`
  (`KAM.Wave.waveCubicLp_apply`);
* `KAM.Wave.waveCubicLp_analyticOnNhd`: `y ↦ T(y,y,y)` is real analytic on `ℓ²`;
* `KAM.Wave.waveCubicLp_norm_le`: `‖T(y,y,y)‖ ≤ C_m ‖y‖³`.
-/

@[expose] public noncomputable section

open Real
open scoped ENNReal

namespace KAM.Wave

/-- The constant `C_m = 8 (1 + 2 ζ(3)) / π` of `bpW:w0n:cubic-bound` (independent of `m`),
with `ζ(3) = Σ_{n ≥ 1} n⁻³`. -/
def waveCubicHeadlineConst : ℝ := 8 * (1 + 2 * ∑' n : ℕ+, ((n : ℝ) ^ 3)⁻¹) / π

lemma waveAlgConst_three_halves_sq :
    w0aAlgConst (3 / 2) ^ 2 = 8 * (1 + 2 * ∑' n : ℕ+, ((n : ℝ) ^ 3)⁻¹) := by
  have hnn : 0 ≤ 1 + 2 * ∑' n : ℕ+, (n : ℝ) ^ (-(2 * (3 / 2 : ℝ))) :=
    by have : 0 ≤ ∑' n : ℕ+, (n : ℝ) ^ (-(2 * (3 / 2 : ℝ))) :=
         tsum_nonneg fun n => Real.rpow_nonneg (by positivity) _
       linarith
  have h1 : ∀ n : ℕ+, (n : ℝ) ^ (-(2 * (3 / 2 : ℝ))) = ((n : ℝ) ^ 3)⁻¹ := fun n => by
    have : -(2 * (3 / 2 : ℝ)) = -((3 : ℕ) : ℝ) := by norm_num
    rw [this, Real.rpow_neg (by positivity), Real.rpow_natCast]
  have h2 : ((2 : ℝ) ^ (3 / 2 : ℝ)) ^ 2 = 8 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num
  unfold w0aAlgConst
  rw [mul_pow, h2, Real.sq_sqrt hnn]
  simp only [h1]

lemma waveCubicConst_one : waveCubicConst 1 = waveCubicHeadlineConst := by
  unfold waveCubicConst waveCubicHeadlineConst
  have : (1 : ℝ) + 1 / 2 = 3 / 2 := by norm_num
  rw [this, waveAlgConst_three_halves_sq]

lemma waveEll_coeff (y : lp (fun _ : ℕ+ => ℝ) 2) : WaveEll 1 1 (coeff y) := by
  have h : ∀ j : ℕ+, ellWeight 1 1 j * coeff y j = y j := fun j => by
    have := (waveEllWeight_pos 1 1 j).ne'
    unfold coeff; field_simp
  unfold WaveEll
  simp only [h]
  simpa [Real.rpow_two] using (lp.memℓp y).summable (by simp : (0 : ℝ) < (2 : ℝ≥0∞).toReal)

lemma wave_lp_norm_eq_sqrt (y : lp (fun _ : ℕ+ => ℝ) 2) : ‖y‖ = Real.sqrt (∑' j, y j ^ 2) := by
  rw [lp.norm_eq_tsum_rpow (by simp) y, Real.sqrt_eq_rpow]
  simp [Real.rpow_two]

lemma norm_eq_waveEllNorm_coeff (y : lp (fun _ : ℕ+ => ℝ) 2) : ‖y‖ = waveEllNorm 1 1 (coeff y) := by
  have h : ∀ j : ℕ+, ellWeight 1 1 j * coeff y j = y j := fun j => by
    have := (waveEllWeight_pos 1 1 j).ne'
    unfold coeff; field_simp
  rw [wave_lp_norm_eq_sqrt]
  unfold waveEllNorm
  simp only [h]

/-- `bpW:w0n:cubic-bound` (headline): `𝒢(q) ∈ ℓ^{1,2}` and `‖𝒢(q)‖_{1,2} ≤ C_m ‖q‖_{1,1}³`
for `q = coeff y`, `y ∈ ℓ²`. -/
theorem wave_cubic_bound (m : ℝ) (hm : 0 < m) (y : lp (fun _ : ℕ+ => ℝ) 2) :
    WaveEll 1 2 (waveCubic m hm (coeff y)) ∧
      waveEllNorm 1 2 (waveCubic m hm (coeff y)) ≤
        waveCubicHeadlineConst * waveEllNorm 1 1 (coeff y) ^ 3 := by
  have hq := waveEll_coeff y
  have h := wave_trilinear_bound m hm (zero_le_one) (le_refl _ |>.trans' (by norm_num : (1 / 2 : ℝ) ≤ 1))
    hq hq hq
  have e : waveCubic m hm (coeff y) = waveTrilinear m hm (coeff y) (coeff y) (coeff y) :=
    funext fun l => waveCubic_eq_trilinear m hm one_pos hq l
  have two : (1 : ℝ) + 1 = 2 := by norm_num
  rw [e]
  rw [two] at h
  refine ⟨h.2.1, ?_⟩
  have := h.2.2
  rw [waveCubicConst_one] at this
  simpa [pow_succ, mul_assoc] using this

/-- The frozen `cubicGrad` lies in `ℓ^{1,2}` (`bpW:w0n:cubic-bound`). -/
theorem cubicGrad_mem_ell (m : ℝ) (hm : 0 < m) (y : lp (fun _ : ℕ+ => ℝ) 2) :
    WaveEll 1 2 (cubicGrad m hm y) := by
  have : cubicGrad m hm y = waveCubic m hm (coeff y) :=
    funext fun l => cubicGrad_eq_waveCubic m hm y l
  rw [this]; exact (wave_cubic_bound m hm y).1

/-- `bpW:w0n:cubic-bound`: `‖cubicGrad(y)‖_{1,2} ≤ C_m ‖y‖³`, with `C_m = 8(1 + 2ζ(3))/π`. -/
theorem cubicGrad_norm_le (m : ℝ) (hm : 0 < m) (y : lp (fun _ : ℕ+ => ℝ) 2) :
    waveEllNorm 1 2 (cubicGrad m hm y) ≤ waveCubicHeadlineConst * ‖y‖ ^ 3 := by
  have : cubicGrad m hm y = waveCubic m hm (coeff y) :=
    funext fun l => cubicGrad_eq_waveCubic m hm y l
  rw [this, norm_eq_waveEllNorm_coeff]
  exact (wave_cubic_bound m hm y).2

end KAM.Wave

end
