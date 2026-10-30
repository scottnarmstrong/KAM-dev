/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Normal.Analysis.CubicHeadline
public import KAM.Wave.Normal.Analysis.PdeBase
public import KAM.Wave.Recon.SineCompleteness

/-!
# The force identity (blueprint `bpW:w0n:pde-equiv`, equation `bpW:w0n:force`)

Infrastructure used by several nodes; the dependency graph is still being built.

For `q ∈ ℓ^{1,1}`: `U_m(q)(x)^3 = Σ_l √λ_l 𝒢(q)_l φ_l(x)` for `x ∈ [0, π]`
(`KAM.Wave.wave_force_identity`), proved from `∫ U³ φ_l = √λ_l 𝒢(q)_l` (`bpW:w0n:gradient`), the
bound `𝒢(q) ∈ ℓ^{1,2}` (`bpW:w0n:cubic-bound`) and the completeness of the sine system
(`bpW:w1:sine-completeness`). Also the second identity of `bpW:w0n:force`,
`KAM.Wave.waveSineSeries_two_eq`: `-∂_x² U + m U = U(λ² q)` in series form.
-/

@[expose] public noncomputable section

open Real
open scoped ENNReal

namespace KAM.Wave

lemma waveEll_mono {a p p' : ℝ} (h : p' ≤ p) {c : ℕ+ → ℝ} (hc : WaveEll a p c) :
    WaveEll a p' c := by
  refine Summable.of_nonneg_of_le (fun j => sq_nonneg _) (fun j => ?_) hc
  have hj : (1 : ℝ) ≤ j := by exact_mod_cast j.pos
  have h1 : ellWeight a p' j ≤ ellWeight a p j := by
    unfold ellWeight
    gcongr
  have h0 : 0 ≤ ellWeight a p' j := (waveEllWeight_pos a p' j).le
  rw [mul_pow, mul_pow]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ h0 h1 2) (sq_nonneg _)

lemma waveEll_sub {a p : ℝ} {c d : ℕ+ → ℝ} (hc : WaveEll a p c) (hd : WaveEll a p d) :
    WaveEll a p (fun j => c j - d j) := by
  have := waveEll_add hc (waveEll_smul (-1) hd)
  refine this.congr fun j => ?_
  ring

lemma abs_lam_le (m : ℝ) (hm : 0 < m) (j : ℕ+) : |lam m hm j| ≤ (1 + m) * (j : ℝ) ^ (1 : ℝ) := by
  rw [Real.rpow_one, abs_of_nonneg (lt_of_lt_of_le one_pos (one_le_lam m hm j)).le]
  exact lam_le m hm j

lemma abs_sqrt_lam_le (m : ℝ) (hm : 0 < m) (j : ℕ+) :
    |Real.sqrt (lam m hm j)| ≤ Real.sqrt (1 + m) * (j : ℝ) ^ (1 / 2 : ℝ) := by
  rw [abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_mul (by linarith)]
  exact Real.sqrt_le_sqrt (lam_le m hm j)

/-- Multiplication by `λ` maps `ℓ^{a,p}` to `ℓ^{a,p-1}`. -/
lemma waveEll_lam_mul (m : ℝ) (hm : 0 < m) {a p : ℝ} {c : ℕ+ → ℝ} (hc : WaveEll a p c) :
    WaveEll a (p - 1) (fun j => lam m hm j * c j) :=
  (waveEll_mul_poly (by linarith) (abs_lam_le m hm) hc).1

/-- Multiplication by `√λ` maps `ℓ^{a,p}` to `ℓ^{a,p-1/2}`. -/
lemma waveEll_sqrtLam_mul (m : ℝ) (hm : 0 < m) {a p : ℝ} {c : ℕ+ → ℝ} (hc : WaveEll a p c) :
    WaveEll a (p - 1 / 2) (fun j => Real.sqrt (lam m hm j) * c j) :=
  (waveEll_mul_poly (Real.sqrt_nonneg _) (abs_sqrt_lam_le m hm) hc).1

/-- `𝒢(q) ∈ ℓ^{1,2}` for `q ∈ ℓ^{1,1}`. -/
lemma waveEll_waveCubic (m : ℝ) (hm : 0 < m) {c : ℕ+ → ℝ} (hc : WaveEll 1 1 c) :
    WaveEll 1 2 (waveCubic m hm c) := by
  have h := (wave_trilinear_bound m hm zero_le_one (by norm_num) hc hc hc).2.1
  have e : waveCubic m hm c = waveTrilinear m hm c c c :=
    funext fun l => waveCubic_eq_trilinear m hm one_pos hc l
  have two : (1 : ℝ) + 1 = 2 := by norm_num
  rw [two] at h
  rw [e]; exact h

/-- `√λ 𝒢(q)` is absolutely summable (indeed in `ℓ^{1,3/2}`). -/
lemma summable_abs_sqrtLam_waveCubic (m : ℝ) (hm : 0 < m) {c : ℕ+ → ℝ} (hc : WaveEll 1 1 c) :
    Summable fun l : ℕ+ => |Real.sqrt (lam m hm l) * waveCubic m hm c l| := by
  have := waveEll_summable_pow_mul one_pos
    (waveEll_sqrtLam_mul m hm (waveEll_waveCubic m hm hc)) 0
  simpa using this

/-- The force identity `U_m(q)^3 = Σ_l √λ_l 𝒢(q)_l φ_l` on `[0, π]` (`bpW:w0n:force`). -/
theorem wave_force_identity (m : ℝ) (hm : 0 < m) {c : ℕ+ → ℝ} (hc : WaveEll 1 1 c) :
    ∀ x ∈ Set.Icc 0 π,
      waveU m hm c x ^ 3 =
        waveSineSeries 0 (fun l => Real.sqrt (lam m hm l) * waveCubic m hm c l) x := by
  have hpi := Real.pi_pos
  set cc : ℕ+ → ℝ := fun l => Real.sqrt (lam m hm l) * waveCubic m hm c l with hcc
  have hcc1 : Summable fun l => |cc l| := summable_abs_sqrtLam_waveCubic m hm hc
  have hh := summable_abs_waveHat m hm one_pos hc
  have hU : Continuous (waveU m hm c) := by
    rw [waveU_eq_series]; exact continuous_waveSineSeries_zero hh
  have hS : Continuous (waveSineSeries 0 cc) := continuous_waveSineSeries_zero hcc1
  set f : ℝ → ℝ := fun x => waveU m hm c x ^ 3 - waveSineSeries 0 cc x with hf
  have hfc : Continuous f := (hU.pow 3).sub hS
  have hint : ∀ l : ℕ+, ∫ x in (0 : ℝ)..π, f x * sineMode l x = 0 := by
    intro l
    have e : ∀ x, f x * sineMode l x =
        waveU m hm c x ^ 3 * sineMode l x - waveSineSeries 0 cc x * sineMode l x := fun x => by
      simp only [hf]; ring
    simp_rw [e]
    have i1 : IntervalIntegrable (fun x => waveU m hm c x ^ 3 * sineMode l x)
        MeasureTheory.volume 0 π :=
      (by have := continuous_sineMode l; fun_prop : Continuous fun x => waveU m hm c x ^ 3 * sineMode l x).intervalIntegrable _ _
    have i2 : IntervalIntegrable (fun x => waveSineSeries 0 cc x * sineMode l x)
        MeasureTheory.volume 0 π :=
      (by have := continuous_sineMode l; fun_prop : Continuous fun x => waveSineSeries 0 cc x * sineMode l x).intervalIntegrable _ _
    rw [intervalIntegral.integral_sub i1 i2,
      integral_waveU_cube_mul_sineMode, integral_waveSineSeries_mul_sineMode hcc1]
    simp [hcc]
  have hbd : ∃ C : ℝ, ∀ x, |f x| ≤ C := by
    refine ⟨(Real.sqrt (2 / π) * ∑' j, |waveHat m hm c j|) ^ 3 +
      Real.sqrt (2 / π) * ∑' j, |cc j|, fun x => ?_⟩
    have h1 := abs_waveSineSeries_zero_le hh x
    have h2 := abs_waveSineSeries_zero_le hcc1 x
    simp only [hf]
    rw [waveU_eq_series]
    calc |waveSineSeries 0 (waveHat m hm c) x ^ 3 - waveSineSeries 0 cc x|
        ≤ |waveSineSeries 0 (waveHat m hm c) x ^ 3| + |waveSineSeries 0 cc x| := abs_sub _ _
      _ ≤ _ := by
        rw [abs_pow]
        gcongr
  obtain ⟨C, hC⟩ := hbd
  have hmem : MeasureTheory.MemLp f 2 (MeasureTheory.volume.restrict (Set.Ioo 0 π)) :=
    MeasureTheory.MemLp.of_bound hfc.aestronglyMeasurable C
      (Filter.Eventually.of_forall fun x => by simpa using hC x)
  intro x hx
  have := eqOn_zero_of_integral_sineMode_eq_zero hmem hfc.continuousOn hint x hx
  have h0 : f x = 0 := this
  simp only [hf] at h0
  linarith

end KAM.Wave

end
