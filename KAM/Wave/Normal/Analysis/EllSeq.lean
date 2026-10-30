/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import KAM.Frozen.Wave.Defs.EllWeight
public import KAM.Wave.Recon.SineFeature

/-!
# Weighted sequence spaces `ℓ^{a,p}` and the Cauchy–Schwarz summation bound
(blueprint `bpW:w0n:recon-bounded`, first display)

Infrastructure used by several nodes; the dependency graph is still being built.

A real sequence `c : ℕ+ → ℝ` lies in `ℓ^{a,p}` when `Σ (ω_{a,p}(j) c_j)²` converges
(`KAM.Wave.WaveEll`), and `‖c‖_{a,p}` is `KAM.Wave.waveEllNorm`. For `a > 0` the Cauchy–Schwarz
estimate `Σ_j |c_j| j^k ≤ M_{a,p,k} ‖c‖_{a,p}` of the blueprint is
`KAM.Wave.waveEll_summable_pow_mul` / `KAM.Wave.waveEll_tsum_pow_mul_le`, with
`M_{a,p,k}² = Σ j^{2k-2p} e^{-2aj}` (`KAM.Wave.waveEllMajorant`).
Multiplication by a polynomially bounded sequence lowers `p` (`KAM.Wave.waveEll_mul_poly`).
-/

@[expose] public noncomputable section

open scoped ENNReal

namespace KAM.Wave

/-- `c ∈ ℓ^{a,p}`: `Σ_{j ≥ 1} (j^p e^{a j} c_j)²` converges (blueprint `bpW:w0:ellap`). -/
def WaveEll (a p : ℝ) (c : ℕ+ → ℝ) : Prop :=
  Summable fun j : ℕ+ => (ellWeight a p j * c j) ^ 2

/-- The norm `‖c‖_{a,p}` of `ℓ^{a,p}` (a junk value `0` off the space). -/
def waveEllNorm (a p : ℝ) (c : ℕ+ → ℝ) : ℝ :=
  Real.sqrt (∑' j : ℕ+, (ellWeight a p j * c j) ^ 2)

/-- The constant `M_{a,p,k} = (Σ_{j ≥ 1} j^{2k-2p} e^{-2aj})^{1/2}` of `bpW:w0n:recon-bounded`. -/
def waveEllMajorant (a p : ℝ) (k : ℕ) : ℝ :=
  Real.sqrt (∑' j : ℕ+, (j : ℝ) ^ (2 * (k : ℝ) - 2 * p) * Real.exp (-(2 * a) * j))

lemma waveEllWeight_pos (a p : ℝ) (j : ℕ+) : 0 < ellWeight a p j := by
  unfold ellWeight
  exact mul_pos (Real.rpow_pos_of_pos (by positivity) _) (Real.exp_pos _)

lemma waveEllNorm_nonneg (a p : ℝ) (c : ℕ+ → ℝ) : 0 ≤ waveEllNorm a p c := Real.sqrt_nonneg _

lemma waveEllMajorant_nonneg (a p : ℝ) (k : ℕ) : 0 ≤ waveEllMajorant a p k := Real.sqrt_nonneg _

/-- Cauchy–Schwarz for nonnegative square-summable families. -/
lemma waveCauchySchwarz_tsum {ι : Type*} {f g : ι → ℝ} (hf : ∀ i, 0 ≤ f i) (hg : ∀ i, 0 ≤ g i)
    (hf2 : Summable fun i => f i ^ 2) (hg2 : Summable fun i => g i ^ 2) :
    Summable (fun i => f i * g i) ∧
      ∑' i, f i * g i ≤ Real.sqrt (∑' i, f i ^ 2) * Real.sqrt (∑' i, g i ^ 2) := by
  have h := Real.summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg (p := 2) (q := 2)
    Real.HolderConjugate.two_two hf hg (by simpa using hf2) (by simpa using hg2)
  refine ⟨h.1, ?_⟩
  have e1 : ∀ i, f i ^ (2 : ℝ) = f i ^ 2 := fun i => by
    rw [← Real.rpow_natCast]; norm_num
  have e2 : ∀ i, g i ^ (2 : ℝ) = g i ^ 2 := fun i => by
    rw [← Real.rpow_natCast]; norm_num
  simp only [e1, e2, ← Real.sqrt_eq_rpow] at h
  exact h.2

lemma waveEllWeight_inv_sq (a p : ℝ) (k : ℕ) (j : ℕ+) :
    ((j : ℝ) ^ k / ellWeight a p j) ^ 2 =
      (j : ℝ) ^ (2 * (k : ℝ) - 2 * p) * Real.exp (-(2 * a) * j) := by
  have hj : (0 : ℝ) < j := by positivity
  have h1 : (j : ℝ) ^ (2 * (k : ℝ) - 2 * p) = ((j : ℝ) ^ k) ^ 2 / ((j : ℝ) ^ p) ^ 2 := by
    rw [Real.rpow_sub hj, ← Real.rpow_natCast ((j : ℝ) ^ k) 2, ← Real.rpow_natCast,
      ← Real.rpow_mul hj.le, ← Real.rpow_natCast ((j : ℝ) ^ p) 2, ← Real.rpow_mul hj.le]
    simp only [Nat.cast_ofNat]
    rw [mul_comm (2 : ℝ) p, mul_comm (2 : ℝ) (k : ℝ)]
  have h2 : Real.exp (-(2 * a) * j) = 1 / (Real.exp (a * j)) ^ 2 := by
    rw [← Real.exp_nat_mul, one_div, ← Real.exp_neg]
    congr 1; push_cast; ring
  rw [h1, h2]
  unfold ellWeight
  have : (0 : ℝ) < (j : ℝ) ^ p := Real.rpow_pos_of_pos hj _
  have : (0 : ℝ) < Real.exp (a * j) := Real.exp_pos _
  field_simp

lemma summable_waveEllMajorant (a p : ℝ) (k : ℕ) (ha : 0 < a) :
    Summable fun j : ℕ+ => (j : ℝ) ^ (2 * (k : ℝ) - 2 * p) * Real.exp (-(2 * a) * j) :=
  summable_rpow_mul_exp_neg _ (2 * a) (by linarith)

/-- The Cauchy–Schwarz estimate of `bpW:w0n:recon-bounded`: `Σ_j |c_j| j^k` converges. -/
theorem waveEll_summable_pow_mul {a p : ℝ} (ha : 0 < a) {c : ℕ+ → ℝ} (hc : WaveEll a p c) (k : ℕ) :
    Summable fun j : ℕ+ => |c j| * (j : ℝ) ^ k := by
  have hCS := waveCauchySchwarz_tsum
    (f := fun j : ℕ+ => ellWeight a p j * |c j|) (g := fun j : ℕ+ => (j : ℝ) ^ k / ellWeight a p j)
    (fun j => mul_nonneg (waveEllWeight_pos a p j).le (abs_nonneg _))
    (fun j => div_nonneg (by positivity) (waveEllWeight_pos a p j).le)
    ((show Summable _ from hc).congr fun j => by simp only [mul_pow, sq_abs])
    (by simpa only [waveEllWeight_inv_sq] using summable_waveEllMajorant a p k ha)
  refine hCS.1.congr fun j => ?_
  have := (waveEllWeight_pos a p j).ne'
  field_simp

/-- `bpW:w0n:recon-bounded`: `Σ_j |c_j| j^k ≤ M_{a,p,k} ‖c‖_{a,p}`. -/
theorem waveEll_tsum_pow_mul_le {a p : ℝ} (ha : 0 < a) {c : ℕ+ → ℝ} (hc : WaveEll a p c) (k : ℕ) :
    ∑' j : ℕ+, |c j| * (j : ℝ) ^ k ≤ waveEllMajorant a p k * waveEllNorm a p c := by
  have hCS := waveCauchySchwarz_tsum
    (f := fun j : ℕ+ => ellWeight a p j * |c j|) (g := fun j : ℕ+ => (j : ℝ) ^ k / ellWeight a p j)
    (fun j => mul_nonneg (waveEllWeight_pos a p j).le (abs_nonneg _))
    (fun j => div_nonneg (by positivity) (waveEllWeight_pos a p j).le)
    ((show Summable _ from hc).congr fun j => by simp only [mul_pow, sq_abs])
    (by simpa only [waveEllWeight_inv_sq] using summable_waveEllMajorant a p k ha)
  have e1 : ∑' j : ℕ+, |c j| * (j : ℝ) ^ k
      = ∑' j : ℕ+, (ellWeight a p j * |c j|) * ((j : ℝ) ^ k / ellWeight a p j) := by
    refine tsum_congr fun j => ?_
    have := (waveEllWeight_pos a p j).ne'
    field_simp
  rw [e1]
  refine hCS.2.trans ?_
  simp only [waveEllMajorant, waveEllNorm, mul_pow, sq_abs, waveEllWeight_inv_sq]
  rw [mul_comm]

/-- Multiplication by a polynomially bounded sequence lowers the Sobolev index
(`bpW:w0n:recon-bounded`, last sentence). -/
theorem waveEll_mul_poly {a p : ℝ} {c β : ℕ+ → ℝ} {B ν : ℝ} (hB : 0 ≤ B)
    (hβ : ∀ j : ℕ+, |β j| ≤ B * (j : ℝ) ^ ν) (hc : WaveEll a p c) :
    WaveEll a (p - ν) (fun j => β j * c j) ∧
      waveEllNorm a (p - ν) (fun j => β j * c j) ≤ B * waveEllNorm a p c := by
  have key : ∀ j : ℕ+, (ellWeight a (p - ν) j * (β j * c j)) ^ 2 ≤
      B ^ 2 * (ellWeight a p j * c j) ^ 2 := by
    intro j
    have hj : (0 : ℝ) < j := by positivity
    have hw : ellWeight a (p - ν) j * |β j| ≤ B * ellWeight a p j := by
      unfold ellWeight
      rw [Real.rpow_sub hj]
      have h1 : 0 < (j : ℝ) ^ ν := Real.rpow_pos_of_pos hj _
      have h2 : 0 < (j : ℝ) ^ p := Real.rpow_pos_of_pos hj _
      calc (j : ℝ) ^ p / (j : ℝ) ^ ν * Real.exp (a * j) * |β j|
          ≤ (j : ℝ) ^ p / (j : ℝ) ^ ν * Real.exp (a * j) * (B * (j : ℝ) ^ ν) := by
            gcongr; exact hβ j
        _ = B * ((j : ℝ) ^ p * Real.exp (a * j)) := by field_simp
    have hsq : (ellWeight a (p - ν) j * |β j|) ^ 2 ≤ (B * ellWeight a p j) ^ 2 :=
      pow_le_pow_left₀ (by have := waveEllWeight_pos a (p - ν) j; positivity) hw 2
    calc (ellWeight a (p - ν) j * (β j * c j)) ^ 2
        = (ellWeight a (p - ν) j * |β j|) ^ 2 * c j ^ 2 := by
          simp only [mul_pow, sq_abs]; ring
      _ ≤ (B * ellWeight a p j) ^ 2 * c j ^ 2 := by gcongr
      _ = B ^ 2 * (ellWeight a p j * c j) ^ 2 := by ring
  have hs : Summable fun j : ℕ+ => (ellWeight a (p - ν) j * (β j * c j)) ^ 2 :=
    Summable.of_nonneg_of_le (fun j => sq_nonneg _) key (hc.mul_left (B ^ 2))
  refine ⟨hs, ?_⟩
  unfold waveEllNorm
  have : ∑' j : ℕ+, (ellWeight a (p - ν) j * (β j * c j)) ^ 2 ≤
      B ^ 2 * ∑' j : ℕ+, (ellWeight a p j * c j) ^ 2 := by
    rw [← tsum_mul_left]
    exact Summable.tsum_le_tsum key hs (hc.mul_left _)
  calc _ ≤ Real.sqrt (B ^ 2 * ∑' j : ℕ+, (ellWeight a p j * c j) ^ 2) := Real.sqrt_le_sqrt this
    _ = B * Real.sqrt (∑' j : ℕ+, (ellWeight a p j * c j) ^ 2) := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hB]

/-- The weighted coordinates `ω_{a,p}(j) c_j` of `c ∈ ℓ^{a,p}` are in `ℓ²`. -/
lemma memℓp_two_of_waveEll {a p : ℝ} {c : ℕ+ → ℝ} (h : WaveEll a p c) :
    Memℓp (fun j => ellWeight a p j * c j) 2 := by
  refine memℓp_gen ?_
  refine (show Summable fun j => (ellWeight a p j * c j) ^ 2 from h).congr fun j => ?_
  rw [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs]

end KAM.Wave

end
