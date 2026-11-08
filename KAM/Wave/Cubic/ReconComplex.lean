/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Cubic.SelectionOneSided
public import KAM.Wave.Normal.Analysis.SineSeries

/-!
# Reconstruction for complex coefficient sequences (blueprint `bpW:w0n:recon-bounded`)

This is the complex-carrier clause of `bpW:w0n:recon-bounded`, assigned to
package W1-CUBIC by the scope ruling on W0-ANALYSIS; the statements are over any `RCLike` field `𝕜`
(so `ℝ` and `ℂ`).

For `c ∈ ℓ^{a,p}_𝕜` (`IsEll a p c`), `a > 0`, `k ∈ ℕ`:

* `KAM.Wave.waveEllK_tsum_pow_mul_le`: `Σ_j ‖c_j‖ j^k ≤ M_{a,p,k} ‖c‖_{a,p}`
  (`M = waveEllMajorant a p k`), the series being summable (`waveEllK_summable_pow_mul`);
* `KAM.Wave.waveSineSeriesK_norm_le`: `‖Σ c_j φ_j^{(k)}(x)‖ ≤ √(2/π) M_{a,p,k} ‖c‖_{a,p}` for
  all `x`;
* linearity (`waveSineSeriesK_add`, `waveSineSeriesK_smul`), uniform convergence
  (`waveSineSeriesK_tendstoUniformly`), termwise differentiation
  (`hasDerivAt_waveSineSeriesK`, `contDiff_waveSineSeriesK`, `iteratedDeriv_waveSineSeriesK`),
  vanishing at `0`, `π` (`waveSineSeriesK_zero_apply`, `waveSineSeriesK_pi`) and the coefficient
  formula `∫₀^π (Σ c_j φ_j) φ_l = c_l` (`integral_waveSineSeriesK_mul_sineMode`).
-/

@[expose] public noncomputable section

open Real

namespace KAM.Wave

variable {K : Type*} [RCLike K]

/-- The `k`-th derivative series `Σ_{j ≥ 1} c_j φ_j^{(k)}(x)` for `𝕜`-valued coefficients. -/
def waveSineSeriesK (k : ℕ) (c : ℕ+ → K) (x : ℝ) : K :=
  ∑' j : ℕ+, c j * ((sineModeIter k j x : ℝ) : K)

lemma waveSineSeriesK_term_le (k : ℕ) (c : ℕ+ → K) (j : ℕ+) (x : ℝ) :
    ‖c j * ((sineModeIter k j x : ℝ) : K)‖ ≤ Real.sqrt (2 / π) * (‖c j‖ * (j : ℝ) ^ k) := by
  rw [norm_mul, RCLike.norm_ofReal]
  calc ‖c j‖ * |sineModeIter k j x| ≤ ‖c j‖ * (Real.sqrt (2 / π) * (j : ℝ) ^ k) := by
        gcongr; exact wave_abs_sineModeIter_le k j x
    _ = _ := by ring

lemma waveSineSeriesK_summable_norm {c : ℕ+ → K} {k : ℕ}
    (hc : Summable fun j : ℕ+ => ‖c j‖ * (j : ℝ) ^ k) (x : ℝ) :
    Summable fun j : ℕ+ => ‖c j * ((sineModeIter k j x : ℝ) : K)‖ :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun j => waveSineSeriesK_term_le k c j x)
    (hc.mul_left _)

lemma waveEllK_real_norm {a p : ℝ} {c : ℕ+ → K} (hc : IsEll a p c) :
    WaveEll a p (fun j => ‖c j‖) := by
  unfold WaveEll
  have := (wave_isEll_iff_summable a p c).1 hc
  simpa only [abs_norm] using this

/-- `bpW:w0n:recon-bounded`, complex clause: `Σ_j ‖c_j‖ j^k` converges. -/
theorem waveEllK_summable_pow_mul {a p : ℝ} (ha : 0 < a) {c : ℕ+ → K} (hc : IsEll a p c) (k : ℕ) :
    Summable fun j : ℕ+ => ‖c j‖ * (j : ℝ) ^ k := by
  simpa only [abs_norm] using waveEll_summable_pow_mul ha (waveEllK_real_norm hc) k

/-- `bpW:w0n:recon-bounded`, complex clause: `Σ_j ‖c_j‖ j^k ≤ M_{a,p,k} ‖c‖_{a,p}`. -/
theorem waveEllK_tsum_pow_mul_le {a p : ℝ} (ha : 0 < a) {c : ℕ+ → K} (hc : IsEll a p c) (k : ℕ) :
    ∑' j : ℕ+, ‖c j‖ * (j : ℝ) ^ k ≤ waveEllMajorant a p k * ellTsumNorm a p c := by
  have h := waveEll_tsum_pow_mul_le ha (waveEllK_real_norm hc) k
  simp only [abs_norm] at h
  convert h using 2
  rw [wave_ellTsumNorm_eq]
  unfold waveEllNorm
  rfl

/-- Pointwise bound `‖S_k c (x)‖ ≤ √(2/π) M_{a,p,k} ‖c‖_{a,p}`: the series defines a bounded map
into the sup norm. -/
theorem waveSineSeriesK_norm_le {a p : ℝ} (ha : 0 < a) {c : ℕ+ → K} (hc : IsEll a p c) (k : ℕ)
    (x : ℝ) :
    ‖waveSineSeriesK k c x‖ ≤ Real.sqrt (2 / π) * (waveEllMajorant a p k * ellTsumNorm a p c) := by
  have hs := waveSineSeriesK_summable_norm (waveEllK_summable_pow_mul ha hc k) x
  unfold waveSineSeriesK
  calc ‖∑' j : ℕ+, c j * ((sineModeIter k j x : ℝ) : K)‖
      ≤ ∑' j : ℕ+, ‖c j * ((sineModeIter k j x : ℝ) : K)‖ := norm_tsum_le_tsum_norm hs
    _ ≤ ∑' j : ℕ+, Real.sqrt (2 / π) * (‖c j‖ * (j : ℝ) ^ k) :=
        Summable.tsum_le_tsum (fun j => waveSineSeriesK_term_le k c j x) hs
          ((waveEllK_summable_pow_mul ha hc k).mul_left _)
    _ = Real.sqrt (2 / π) * ∑' j : ℕ+, ‖c j‖ * (j : ℝ) ^ k := tsum_mul_left
    _ ≤ _ := by gcongr; exact waveEllK_tsum_pow_mul_le ha hc k

lemma waveSineSeriesK_summable {c : ℕ+ → K} {k : ℕ}
    (hc : Summable fun j : ℕ+ => ‖c j‖ * (j : ℝ) ^ k) (x : ℝ) :
    Summable fun j : ℕ+ => c j * ((sineModeIter k j x : ℝ) : K) :=
  (waveSineSeriesK_summable_norm hc x).of_norm

lemma waveSineSeriesK_add {c d : ℕ+ → K} {k : ℕ}
    (hc : Summable fun j : ℕ+ => ‖c j‖ * (j : ℝ) ^ k)
    (hd : Summable fun j : ℕ+ => ‖d j‖ * (j : ℝ) ^ k) (x : ℝ) :
    waveSineSeriesK k (fun j => c j + d j) x = waveSineSeriesK k c x + waveSineSeriesK k d x := by
  unfold waveSineSeriesK
  rw [← Summable.tsum_add (waveSineSeriesK_summable hc x) (waveSineSeriesK_summable hd x)]
  exact tsum_congr fun j => by ring

lemma waveSineSeriesK_smul (r : K) (c : ℕ+ → K) (k : ℕ) (x : ℝ) :
    waveSineSeriesK k (fun j => r * c j) x = r * waveSineSeriesK k c x := by
  unfold waveSineSeriesK
  rw [← tsum_mul_left]
  exact tsum_congr fun j => by ring

/-- Uniform convergence of the partial sums (Weierstrass M-test). -/
theorem waveSineSeriesK_tendstoUniformly {c : ℕ+ → K} {k : ℕ}
    (hc : Summable fun j : ℕ+ => ‖c j‖ * (j : ℝ) ^ k) :
    TendstoUniformly
      (fun (t : Finset ℕ+) (x : ℝ) => ∑ j ∈ t, c j * ((sineModeIter k j x : ℝ) : K))
      (waveSineSeriesK k c) Filter.atTop :=
  tendstoUniformly_tsum (hc.mul_left (Real.sqrt (2 / π)))
    (fun j x => waveSineSeriesK_term_le k c j x)

lemma wave_hasDerivAt_ofReal {f : ℝ → ℝ} {u x : ℝ} (hf : HasDerivAt f u x) :
    HasDerivAt (fun y => ((f y : ℝ) : K)) ((u : ℝ) : K) x := by
  exact (RCLike.ofRealCLM (K := K)).hasFDerivAt.comp_hasDerivAt x hf

lemma hasDerivAt_waveSineSeriesK {c : ℕ+ → K} {k : ℕ}
    (hc : Summable fun j : ℕ+ => ‖c j‖ * (j : ℝ) ^ (k + 1)) (x : ℝ) :
    HasDerivAt (waveSineSeriesK k c) (waveSineSeriesK (k + 1) c x) x := by
  have hu : Summable fun j : ℕ+ => Real.sqrt (2 / π) * (‖c j‖ * (j : ℝ) ^ (k + 1)) :=
    hc.mul_left _
  have hc' : Summable fun j : ℕ+ => ‖c j‖ * (j : ℝ) ^ k := by
    refine Summable.of_nonneg_of_le (fun j => by positivity) (fun j => ?_) hc
    have hj : (1 : ℝ) ≤ j := by exact_mod_cast j.pos
    calc ‖c j‖ * (j : ℝ) ^ k = ‖c j‖ * (j : ℝ) ^ k * 1 := (mul_one _).symm
      _ ≤ ‖c j‖ * (j : ℝ) ^ k * (j : ℝ) := by gcongr
      _ = _ := by ring
  have := hasDerivAt_tsum (g := fun (j : ℕ+) (y : ℝ) => c j * ((sineModeIter k j y : ℝ) : K))
    (g' := fun (j : ℕ+) (y : ℝ) => c j * ((sineModeIter (k + 1) j y : ℝ) : K)) (y₀ := 0) hu
    (fun j y => (wave_hasDerivAt_ofReal (hasDerivAt_sineModeIter k j y)).const_mul (c j))
    (fun j y => waveSineSeriesK_term_le (k + 1) c j y)
    (waveSineSeriesK_summable hc' 0) x
  exact this

/-- Termwise differentiation: `S_k c` is `C^r` for every `r`, when `c ∈ ℓ^{a,p}_𝕜`, `a > 0`. -/
theorem contDiff_waveSineSeriesK {a p : ℝ} (ha : 0 < a) {c : ℕ+ → K} (hc : IsEll a p c)
    (r k : ℕ) : ContDiff ℝ r (waveSineSeriesK k c) := by
  induction r generalizing k with
  | zero =>
    refine contDiff_zero.2 ?_
    exact (fun x => (hasDerivAt_waveSineSeriesK (waveEllK_summable_pow_mul ha hc (k + 1)) x)
      |>.continuousAt) |> continuous_iff_continuousAt.2
  | succ r ih =>
    rw [Nat.cast_succ, contDiff_succ_iff_deriv]
    refine ⟨fun x => (hasDerivAt_waveSineSeriesK (waveEllK_summable_pow_mul ha hc (k + 1)) x)
      |>.differentiableAt, by simp, ?_⟩
    have : deriv (waveSineSeriesK k c) = waveSineSeriesK (k + 1) c :=
      funext fun x =>
        (hasDerivAt_waveSineSeriesK (waveEllK_summable_pow_mul ha hc (k + 1)) x).deriv
    rw [this]
    exact ih (k + 1)

theorem iteratedDeriv_waveSineSeriesK {a p : ℝ} (ha : 0 < a) {c : ℕ+ → K} (hc : IsEll a p c)
    (r k : ℕ) : iteratedDeriv r (waveSineSeriesK k c) = waveSineSeriesK (k + r) c := by
  induction r generalizing k with
  | zero => simp
  | succ r ih =>
    have hd : deriv (waveSineSeriesK k c) = waveSineSeriesK (k + 1) c :=
      funext fun x =>
        (hasDerivAt_waveSineSeriesK (waveEllK_summable_pow_mul ha hc (k + 1)) x).deriv
    rw [iteratedDeriv_succ', hd, ih (k + 1)]
    congr 1; omega

lemma waveSineSeriesK_zero_eq (c : ℕ+ → K) (x : ℝ) :
    waveSineSeriesK 0 c x = ∑' j : ℕ+, c j * ((sineMode j x : ℝ) : K) := by
  unfold waveSineSeriesK
  exact tsum_congr fun j => by rw [sineModeIter_zero]

/-- `bpW:w0n:recon-bounded`: the value at `x = 0` vanishes. -/
theorem waveSineSeriesK_zero_apply (c : ℕ+ → K) : waveSineSeriesK 0 c 0 = 0 := by
  rw [waveSineSeriesK_zero_eq]
  simp [sineMode]

/-- `bpW:w0n:recon-bounded`: the value at `x = π` vanishes. -/
theorem waveSineSeriesK_pi (c : ℕ+ → K) : waveSineSeriesK 0 c π = 0 := by
  rw [waveSineSeriesK_zero_eq]
  have : ∀ j : ℕ+, sineMode j π = 0 := fun j => by
    have := Real.sin_nat_mul_pi (j : ℕ)
    simp [sineMode, this]
  simp [this]

/-- `bpW:w0n:recon-bounded`, complex clause: `∫₀^π (Σ_j c_j φ_j) φ_l = c_l`. -/
theorem integral_waveSineSeriesK_mul_sineMode {c : ℕ+ → K}
    (hc : Summable fun j : ℕ+ => ‖c j‖) (l : ℕ+) :
    ∫ x in (0 : ℝ)..π, waveSineSeriesK 0 c x * ((sineMode l x : ℝ) : K) = c l := by
  have hpi := Real.pi_pos
  have hφ : ∀ j x, |sineMode j x| ≤ Real.sqrt (2 / π) := fun j x => by
    have := wave_abs_sineModeIter_le 0 j x
    simpa [sineModeIter_zero] using this
  have hc0 : Summable fun j : ℕ+ => ‖c j‖ * (j : ℝ) ^ 0 := by simpa using hc
  have hsum : ∀ x, HasSum (fun j : ℕ+ => c j * ((sineMode j x : ℝ) : K) * ((sineMode l x : ℝ) : K))
      (waveSineSeriesK 0 c x * ((sineMode l x : ℝ) : K)) := by
    intro x
    rw [waveSineSeriesK_zero_eq]
    have := (waveSineSeriesK_summable hc0 x).hasSum
    simp only [sineModeIter_zero] at this
    exact this.mul_right _
  have hs := intervalIntegral.hasSum_integral_of_dominated_convergence
    (F := fun (j : ℕ+) x => c j * ((sineMode j x : ℝ) : K) * ((sineMode l x : ℝ) : K))
    (bound := fun (j : ℕ+) _ => ‖c j‖ * (Real.sqrt (2 / π) * Real.sqrt (2 / π)))
    (a := 0) (b := π)
    (fun j => (by unfold sineMode; fun_prop : Continuous fun x : ℝ =>
      c j * ((sineMode j x : ℝ) : K) * ((sineMode l x : ℝ) : K)).aestronglyMeasurable)
    (fun j => Filter.Eventually.of_forall fun x _ => by
      rw [norm_mul, norm_mul, RCLike.norm_ofReal, RCLike.norm_ofReal]
      have h1 := hφ j x
      have h2 := hφ l x
      calc ‖c j‖ * |sineMode j x| * |sineMode l x|
          ≤ ‖c j‖ * Real.sqrt (2 / π) * Real.sqrt (2 / π) := by gcongr
        _ = _ := by ring)
    (Filter.Eventually.of_forall fun x _ => hc.mul_right _)
    (intervalIntegrable_const (μ := MeasureTheory.volume))
    (Filter.Eventually.of_forall fun x _ => hsum x)
  have h2 : HasSum (fun j : ℕ+ => ∫ x in (0 : ℝ)..π,
      c j * ((sineMode j x : ℝ) : K) * ((sineMode l x : ℝ) : K)) (c l) := by
    have : ∀ j : ℕ+, ∫ x in (0 : ℝ)..π, c j * ((sineMode j x : ℝ) : K) * ((sineMode l x : ℝ) : K)
        = if j = l then c l else 0 := by
      intro j
      have e : ∀ x, c j * ((sineMode j x : ℝ) : K) * ((sineMode l x : ℝ) : K) =
          c j * ((sineMode j x * sineMode l x : ℝ) : K) := fun x => by push_cast; ring
      simp_rw [e]
      have hint : ∫ x in (0 : ℝ)..π, ((sineMode j x * sineMode l x : ℝ) : K) =
          (((∫ x in (0 : ℝ)..π, sineMode j x * sineMode l x : ℝ)) : K) := by
        have hcont : Continuous fun x : ℝ => sineMode j x * sineMode l x := by
          unfold sineMode; fun_prop
        have := (RCLike.ofRealCLM (K := K)).intervalIntegral_comp_comm
          (f := fun x : ℝ => sineMode j x * sineMode l x) (a := 0) (b := π)
          (μ := MeasureTheory.volume) (hcont.intervalIntegrable _ _)
        simpa using this
      rw [intervalIntegral.integral_const_mul, hint, wave_integral_sineMode_mul_sineMode]
      split_ifs with h <;> simp [h]
    simp_rw [this]
    exact hasSum_ite_eq l (c l)
  exact hs.unique h2

end KAM.Wave

end
