/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import KAM.Wave.Normal.Analysis.EllSeq
public import KAM.Wave.Recon.ReconAnalytic

/-!
# Sine series of weighted sequences (blueprint `bpW:w0n:recon-bounded`)

Infrastructure used by several nodes; the dependency graph is still being built.

For a real sequence `c` put `S_k c (x) = Σ_j c_j φ_j^{(k)}(x)` (`KAM.Wave.waveSineSeries`). For
`c ∈ ℓ^{a,p}` with `a > 0` (any `p`) the blueprint lemma `bpW:w0n:recon-bounded` is the following
list.

* `KAM.Wave.waveEll_summable_pow_mul`, `KAM.Wave.waveEll_tsum_pow_mul_le`: the estimate
  `Σ |c_j| j^k ≤ M_{a,p,k} ‖c‖_{a,p}` (module `EllSeq`);
* `KAM.Wave.waveSineSeries_abs_le`: `|S_k c (x)| ≤ √(2/π) M_{a,p,k} ‖c‖_{a,p}` for all real `x`
  (so `c ↦ S_k c` is bounded linear into the sup norm; linearity `KAM.Wave.waveSineSeries_add`,
  `KAM.Wave.waveSineSeries_smul`);
* `KAM.Wave.waveSineSeries_tendstoUniformly`: uniform convergence of the partial sums;
* `KAM.Wave.hasDerivAt_waveSineSeries`, `KAM.Wave.contDiff_waveSineSeries`,
  `KAM.Wave.iteratedDeriv_waveSineSeries`: termwise differentiation, `C^k` for every `k`;
* `KAM.Wave.waveSineSeries_zero_apply`, `KAM.Wave.waveSineSeries_pi`: vanishing at `0` and `π`;
* `KAM.Wave.integral_waveSineSeries_mul_sineMode`: `∫₀^π (Σ c_j φ_j) φ_l = c_l`.

The dominated convergence helper `KAM.Wave.waveHasSum_intervalIntegral` is reused downstream.
-/

@[expose] public noncomputable section

open Real

namespace KAM.Wave

/-- The `k`-th derivative series `Σ_{j ≥ 1} c_j φ_j^{(k)}(x)` (blueprint `bpW:w0n:recon-bounded`). -/
def waveSineSeries (k : ℕ) (c : ℕ+ → ℝ) (x : ℝ) : ℝ :=
  ∑' j : ℕ+, c j * sineModeIter k j x

lemma wave_abs_sineModeIter_le (k : ℕ) (j : ℕ+) (x : ℝ) :
    |sineModeIter k j x| ≤ Real.sqrt (2 / π) * (j : ℝ) ^ k := by
  unfold sineModeIter
  rw [abs_mul, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg (by positivity)]
  calc _ ≤ Real.sqrt (2 / π) * (j : ℝ) ^ k * 1 := by gcongr; exact Real.abs_sin_le_one _
    _ = _ := mul_one _

lemma wave_abs_mul_sineModeIter_le (k : ℕ) (c : ℕ+ → ℝ) (j : ℕ+) (x : ℝ) :
    |c j * sineModeIter k j x| ≤ Real.sqrt (2 / π) * (|c j| * (j : ℝ) ^ k) := by
  rw [abs_mul]
  calc |c j| * |sineModeIter k j x| ≤ |c j| * (Real.sqrt (2 / π) * (j : ℝ) ^ k) := by
        gcongr; exact wave_abs_sineModeIter_le k j x
    _ = _ := by ring

lemma summable_abs_waveSineSeries {c : ℕ+ → ℝ} {k : ℕ}
    (hc : Summable fun j : ℕ+ => |c j| * (j : ℝ) ^ k) (x : ℝ) :
    Summable fun j : ℕ+ => |c j * sineModeIter k j x| :=
  Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (fun j => wave_abs_mul_sineModeIter_le k c j x)
    (hc.mul_left _)

lemma summable_waveSineSeries {c : ℕ+ → ℝ} {k : ℕ}
    (hc : Summable fun j : ℕ+ => |c j| * (j : ℝ) ^ k) (x : ℝ) :
    Summable fun j : ℕ+ => c j * sineModeIter k j x :=
  (summable_abs_waveSineSeries hc x).of_abs

lemma waveSineSeries_abs_le_of_summable {c : ℕ+ → ℝ} {k : ℕ}
    (hc : Summable fun j : ℕ+ => |c j| * (j : ℝ) ^ k) (x : ℝ) :
    |waveSineSeries k c x| ≤ Real.sqrt (2 / π) * ∑' j : ℕ+, |c j| * (j : ℝ) ^ k := by
  unfold waveSineSeries
  have hs : Summable fun j : ℕ+ => ‖c j * sineModeIter k j x‖ := summable_abs_waveSineSeries hc x
  calc |∑' j : ℕ+, c j * sineModeIter k j x| ≤ ∑' j : ℕ+, |c j * sineModeIter k j x| := by
        simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hs
    _ ≤ ∑' j : ℕ+, Real.sqrt (2 / π) * (|c j| * (j : ℝ) ^ k) :=
        Summable.tsum_le_tsum (fun j => wave_abs_mul_sineModeIter_le k c j x)
          (summable_abs_waveSineSeries hc x) (hc.mul_left _)
    _ = _ := tsum_mul_left

/-- `bpW:w0n:recon-bounded`: `|Σ c_j φ_j^{(k)}(x)| ≤ √(2/π) M_{a,p,k} ‖c‖_{a,p}` for all `x`. -/
theorem waveSineSeries_abs_le {a p : ℝ} (ha : 0 < a) {c : ℕ+ → ℝ} (hc : WaveEll a p c) (k : ℕ)
    (x : ℝ) :
    |waveSineSeries k c x| ≤ Real.sqrt (2 / π) * (waveEllMajorant a p k * waveEllNorm a p c) :=
  (waveSineSeries_abs_le_of_summable (waveEll_summable_pow_mul ha hc k) x).trans
    (by gcongr; exact waveEll_tsum_pow_mul_le ha hc k)

lemma waveSineSeries_add {c d : ℕ+ → ℝ} {k : ℕ}
    (hc : Summable fun j : ℕ+ => |c j| * (j : ℝ) ^ k)
    (hd : Summable fun j : ℕ+ => |d j| * (j : ℝ) ^ k) (x : ℝ) :
    waveSineSeries k (fun j => c j + d j) x = waveSineSeries k c x + waveSineSeries k d x := by
  unfold waveSineSeries
  rw [← Summable.tsum_add (summable_waveSineSeries hc x) (summable_waveSineSeries hd x)]
  exact tsum_congr fun j => by ring

lemma waveSineSeries_smul (r : ℝ) (c : ℕ+ → ℝ) (k : ℕ) (x : ℝ) :
    waveSineSeries k (fun j => r * c j) x = r * waveSineSeries k c x := by
  unfold waveSineSeries
  rw [← tsum_mul_left]
  exact tsum_congr fun j => by ring

/-- Uniform convergence of the partial sums (Weierstrass M-test). -/
theorem waveSineSeries_tendstoUniformly {c : ℕ+ → ℝ} {k : ℕ}
    (hc : Summable fun j : ℕ+ => |c j| * (j : ℝ) ^ k) :
    TendstoUniformly (fun (t : Finset ℕ+) (x : ℝ) => ∑ j ∈ t, c j * sineModeIter k j x)
      (waveSineSeries k c) Filter.atTop :=
  tendstoUniformly_tsum (hc.mul_left (Real.sqrt (2 / π)))
    (fun j x => by simpa only [Real.norm_eq_abs] using wave_abs_mul_sineModeIter_le k c j x)

lemma hasDerivAt_waveSineSeries {c : ℕ+ → ℝ} {k : ℕ}
    (hc : Summable fun j : ℕ+ => |c j| * (j : ℝ) ^ (k + 1)) (x : ℝ) :
    HasDerivAt (waveSineSeries k c) (waveSineSeries (k + 1) c x) x := by
  have hu : Summable fun j : ℕ+ => Real.sqrt (2 / π) * (|c j| * (j : ℝ) ^ (k + 1)) :=
    hc.mul_left _
  have hc' : Summable fun j : ℕ+ => |c j| * (j : ℝ) ^ k := by
    refine Summable.of_nonneg_of_le (fun j => by positivity) (fun j => ?_) hc
    have hj : (1 : ℝ) ≤ j := by exact_mod_cast j.pos
    calc |c j| * (j : ℝ) ^ k = |c j| * (j : ℝ) ^ k * 1 := (mul_one _).symm
      _ ≤ |c j| * (j : ℝ) ^ k * (j : ℝ) := by gcongr
      _ = _ := by ring
  have := hasDerivAt_tsum (g := fun (j : ℕ+) (y : ℝ) => c j * sineModeIter k j y)
    (g' := fun (j : ℕ+) (y : ℝ) => c j * sineModeIter (k + 1) j y) (y₀ := 0) hu
    (fun j y => (hasDerivAt_sineModeIter k j y).const_mul (c j))
    (fun j y => by simpa only [Real.norm_eq_abs] using wave_abs_mul_sineModeIter_le (k + 1) c j y)
    (summable_waveSineSeries hc' 0) x
  exact this

/-- Termwise differentiation: `S_k c` is `C^r` for every `r`, when `c ∈ ℓ^{a,p}`, `a > 0`. -/
theorem contDiff_waveSineSeries {a p : ℝ} (ha : 0 < a) {c : ℕ+ → ℝ} (hc : WaveEll a p c)
    (r k : ℕ) : ContDiff ℝ r (waveSineSeries k c) := by
  induction r generalizing k with
  | zero =>
    refine contDiff_zero.2 ?_
    exact (fun x => (hasDerivAt_waveSineSeries (waveEll_summable_pow_mul ha hc (k + 1)) x)
      |>.continuousAt) |> continuous_iff_continuousAt.2
  | succ r ih =>
    rw [Nat.cast_succ, contDiff_succ_iff_deriv]
    refine ⟨fun x => (hasDerivAt_waveSineSeries (waveEll_summable_pow_mul ha hc (k + 1)) x)
      |>.differentiableAt, by simp, ?_⟩
    have : deriv (waveSineSeries k c) = waveSineSeries (k + 1) c :=
      funext fun x => (hasDerivAt_waveSineSeries (waveEll_summable_pow_mul ha hc (k + 1)) x).deriv
    rw [this]
    exact ih (k + 1)

theorem iteratedDeriv_waveSineSeries {a p : ℝ} (ha : 0 < a) {c : ℕ+ → ℝ} (hc : WaveEll a p c)
    (r k : ℕ) : iteratedDeriv r (waveSineSeries k c) = waveSineSeries (k + r) c := by
  induction r generalizing k with
  | zero => simp
  | succ r ih =>
    have hd : deriv (waveSineSeries k c) = waveSineSeries (k + 1) c :=
      funext fun x => (hasDerivAt_waveSineSeries (waveEll_summable_pow_mul ha hc (k + 1)) x).deriv
    rw [iteratedDeriv_succ', hd, ih (k + 1)]
    congr 1; omega

lemma waveSineSeries_zero_eq (c : ℕ+ → ℝ) (x : ℝ) :
    waveSineSeries 0 c x = ∑' j : ℕ+, c j * sineMode j x := by
  unfold waveSineSeries
  exact tsum_congr fun j => by rw [sineModeIter_zero]

/-- `bpW:w0n:recon-bounded`: the value at `x = 0` vanishes. -/
theorem waveSineSeries_zero_apply (c : ℕ+ → ℝ) : waveSineSeries 0 c 0 = 0 := by
  rw [waveSineSeries_zero_eq]
  simp [sineMode]

/-- `bpW:w0n:recon-bounded`: the value at `x = π` vanishes. -/
theorem waveSineSeries_pi (c : ℕ+ → ℝ) : waveSineSeries 0 c π = 0 := by
  rw [waveSineSeries_zero_eq]
  have : ∀ j : ℕ+, sineMode j π = 0 := fun j => by
    have := Real.sin_nat_mul_pi (j : ℕ)
    simp [sineMode, this]
  simp [this]

/-- Dominated convergence for interval integrals of series of continuous functions with a
summable uniform bound. -/
lemma waveHasSum_intervalIntegral {ι : Type*} [Countable ι] {F : ι → ℝ → ℝ} {f : ℝ → ℝ}
    {b : ι → ℝ} (a₀ b₀ : ℝ) (hF : ∀ n, Continuous (F n)) (hb : Summable b)
    (hbound : ∀ n x, |F n x| ≤ b n) (hsum : ∀ x, HasSum (fun n => F n x) (f x)) :
    HasSum (fun n => ∫ x in a₀..b₀, F n x) (∫ x in a₀..b₀, f x) := by
  refine intervalIntegral.hasSum_integral_of_dominated_convergence
    (fun n _ => b n) (fun n => (hF n).aestronglyMeasurable) ?_ ?_ ?_ ?_
  · exact fun n => Filter.Eventually.of_forall fun t _ => by simpa using hbound n t
  · exact Filter.Eventually.of_forall fun t _ => hb
  · exact intervalIntegrable_const
  · exact Filter.Eventually.of_forall fun t _ => hsum t

lemma wave_integral_cos_int_mul (n : ℤ) :
    ∫ x in (0 : ℝ)..π, Real.cos (n * x) = if n = 0 then π else 0 := by
  split_ifs with h
  · subst h; simp
  · have hn : (n : ℝ) ≠ 0 := by exact_mod_cast h
    rw [intervalIntegral.integral_comp_mul_left (fun x => Real.cos x) hn]
    simp [integral_cos, Real.sin_int_mul_pi]

/-- Orthonormality of the sine modes on `[0, π]`. -/
theorem wave_integral_sineMode_mul_sineMode (i j : ℕ+) :
    ∫ x in (0 : ℝ)..π, sineMode i x * sineMode j x = if i = j then 1 else 0 := by
  have hpi := Real.pi_pos
  have e : ∀ x : ℝ, sineMode i x * sineMode j x =
      (1 / π) * (Real.cos (((i : ℕ) - (j : ℕ) : ℤ) * x) - Real.cos (((i : ℕ) + (j : ℕ) : ℤ) * x)) := by
    intro x
    unfold sineMode
    have h2 := Real.two_mul_sin_mul_sin ((i : ℝ) * x) ((j : ℝ) * x)
    have hs : Real.sqrt (2 / π) * Real.sqrt (2 / π) = 2 / π :=
      Real.mul_self_sqrt (by positivity)
    have : ((((i : ℕ) - (j : ℕ) : ℤ) : ℝ)) * x = (i : ℝ) * x - (j : ℝ) * x := by push_cast; ring
    have h3 : ((((i : ℕ) + (j : ℕ) : ℤ) : ℝ)) * x = (i : ℝ) * x + (j : ℝ) * x := by push_cast; ring
    rw [this, h3]
    calc _ = (Real.sqrt (2 / π) * Real.sqrt (2 / π)) * (Real.sin (i * x) * Real.sin (j * x)) := by ring
      _ = (1 / π) * (2 * Real.sin (i * x) * Real.sin (j * x)) := by rw [hs]; field_simp
      _ = _ := by rw [h2]
  simp_rw [e]
  have hc1 : ∀ n : ℤ, IntervalIntegrable (fun x : ℝ => Real.cos (n * x)) MeasureTheory.volume 0 π :=
    fun n => (by fun_prop : Continuous fun x : ℝ => Real.cos (n * x)).intervalIntegrable _ _
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub (hc1 _) (hc1 _),
    wave_integral_cos_int_mul, wave_integral_cos_int_mul]
  have hne : ((i : ℕ) + (j : ℕ) : ℤ) ≠ 0 := by have := i.pos; have := j.pos; omega
  by_cases h : i = j
  · subst h; simp [hne]
  · have : ((i : ℕ) - (j : ℕ) : ℤ) ≠ 0 := by
      intro h0; exact h (PNat.coe_injective (by omega))
    simp [this, hne, h]

/-- `bpW:w0n:recon-bounded`: `∫₀^π (Σ_j c_j φ_j) φ_l = c_l`. -/
theorem integral_waveSineSeries_mul_sineMode {c : ℕ+ → ℝ}
    (hc : Summable fun j : ℕ+ => |c j|) (l : ℕ+) :
    ∫ x in (0 : ℝ)..π, waveSineSeries 0 c x * sineMode l x = c l := by
  have hpi := Real.pi_pos
  have hφ : ∀ j x, |sineMode j x| ≤ Real.sqrt (2 / π) := fun j x => by
    have := wave_abs_sineModeIter_le 0 j x
    simpa [sineModeIter_zero] using this
  have hc0 : Summable fun j : ℕ+ => |c j| * (j : ℝ) ^ 0 := by simpa using hc
  have hsum : ∀ x, HasSum (fun j : ℕ+ => c j * sineMode j x * sineMode l x)
      (waveSineSeries 0 c x * sineMode l x) := by
    intro x
    rw [waveSineSeries_zero_eq]
    have := (summable_waveSineSeries hc0 x).hasSum
    simp only [sineModeIter_zero] at this
    exact this.mul_right _
  have hs := waveHasSum_intervalIntegral (F := fun (j : ℕ+) x => c j * sineMode j x * sineMode l x)
    (b := fun j : ℕ+ => |c j| * (Real.sqrt (2 / π) * Real.sqrt (2 / π))) 0 π
    (fun j => by unfold sineMode; fun_prop) (hc.mul_right _)
    (fun j x => by
      rw [abs_mul, abs_mul]
      have h1 := hφ j x
      have h2 := hφ l x
      calc |c j| * |sineMode j x| * |sineMode l x|
          ≤ |c j| * Real.sqrt (2 / π) * Real.sqrt (2 / π) := by gcongr
        _ = _ := by ring)
    hsum
  have h2 : HasSum (fun j : ℕ+ => ∫ x in (0 : ℝ)..π, c j * sineMode j x * sineMode l x)
      (c l) := by
    have : ∀ j : ℕ+, ∫ x in (0 : ℝ)..π, c j * sineMode j x * sineMode l x
        = if j = l then c l else 0 := by
      intro j
      have : ∀ x, c j * sineMode j x * sineMode l x = c j * (sineMode j x * sineMode l x) :=
        fun x => by ring
      simp_rw [this]
      rw [intervalIntegral.integral_const_mul, wave_integral_sineMode_mul_sineMode]
      split_ifs with h <;> simp [h]
    simp_rw [this]
    exact hasSum_ite_eq l (c l)
  exact hs.unique h2

end KAM.Wave

end
