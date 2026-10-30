/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Normal.Analysis.Gradient
public import KAM.Wave.Normal.Analysis.EvenMajorant

/-!
# Weighted majorants for `bpW:w0n:cubic-bound`

Infrastructure used by several nodes; the dependency graph is still being built.

* `KAM.Wave.wave_summable_of_weighted`: a nonnegative two-sided sequence in `ℓ^{a,s}_b`, `s ≥ 1`,
  is summable;
* `KAM.Wave.waveEvenAbs_weighted`: for `q ∈ ℓ^{a,p}`, the even majorant `x_i = |q_{|i|}|/√λ_{|i|}`
  lies in `ℓ^{a,p+1/2}_b` with norm `≤ √2 ‖q‖_{a,p}` (`stepW:w0n:majorant`).
-/

@[expose] public noncomputable section

namespace KAM.Wave

lemma waveW2_mul_jap_neg (a s : ℝ) (i : ℤ) :
    w0aW2 a s i * w0aJap i ^ (-s) = Real.exp (a * |(i : ℝ)|) := by
  have hj : 0 < w0aJap i := lt_of_lt_of_le one_pos (w0a_one_le_jap i)
  have h1 : w0aJap i ^ s * w0aJap i ^ (-s) = 1 := by
    rw [← Real.rpow_add hj]; simp
  unfold w0aW2
  calc w0aJap i ^ s * Real.exp (a * |(i : ℝ)|) * w0aJap i ^ (-s)
      = (w0aJap i ^ s * w0aJap i ^ (-s)) * Real.exp (a * |(i : ℝ)|) := by ring
    _ = _ := by rw [h1, one_mul]

lemma wave_summable_of_weighted {a s : ℝ} (ha : 0 ≤ a) (hs : 1 ≤ s) {x : ℤ → ℝ}
    (hx0 : ∀ i, 0 ≤ x i) (hx : Summable fun i => (w0aW2 a s i * x i) ^ 2) : Summable x := by
  have hD0 : ∀ i, 0 ≤ w0aW2 a s i * x i := fun i => mul_nonneg (w0aW2_pos s i).le (hx0 i)
  have h := (w0a_tsum_jap_mul_le hs hD0 hx).1
  refine Summable.of_nonneg_of_le hx0 (fun i => ?_) h
  have hE : 1 ≤ Real.exp (a * |(i : ℝ)|) := Real.one_le_exp (by positivity)
  calc x i = x i * 1 := (mul_one _).symm
    _ ≤ x i * Real.exp (a * |(i : ℝ)|) := mul_le_mul_of_nonneg_left hE (hx0 i)
    _ = w0aW2 a s i * x i * w0aJap i ^ (-s) := by
        rw [← waveW2_mul_jap_neg a s i]; ring

lemma wave_pnat_le_lam (m : ℝ) (hm : 0 < m) (n : ℕ+) : ((n : ℕ+) : ℝ) ≤ lam m hm n := by
  unfold lam
  apply Real.le_sqrt_of_sq_le
  linarith

lemma wave_ellWeight_add_half (a p : ℝ) (n : ℕ+) :
    ellWeight a (p + 1 / 2) n = ellWeight a p n * Real.sqrt n := by
  unfold ellWeight
  have hn : (0 : ℝ) < n := by positivity
  rw [Real.rpow_add hn, Real.sqrt_eq_rpow]
  ring

lemma wave_ellWeight_sq_div_lam_le (m : ℝ) (hm : 0 < m) (a p : ℝ) (n : ℕ+) :
    ellWeight a (p + 1 / 2) n ^ 2 * (n : ℝ) / lam m hm n ≤ ellWeight a (p + 1 / 2) n ^ 2 := by
  have hl : 0 < lam m hm n := lt_of_lt_of_le (by positivity) (wave_pnat_le_lam m hm n)
  rw [div_le_iff₀ hl]
  have := waveEllWeight_pos a (p + 1 / 2) n
  nlinarith [wave_pnat_le_lam m hm n, sq_nonneg (ellWeight a (p + 1 / 2) n)]

/-- `stepW:w0n:majorant`: the even majorant of `q/√λ` lies in `ℓ^{a,p+1/2}_b`, with norm at most
`√2 ‖q‖_{a,p}`. -/
theorem waveEvenAbs_weighted (m : ℝ) (hm : 0 < m) {a p : ℝ} {q : ℕ+ → ℝ} (hq : WaveEll a p q) :
    Summable (fun i : ℤ =>
        (w0aW2 a (p + 1 / 2) i * waveEvenAbs (waveHat m hm q) i) ^ 2) ∧
      w0aL2 (fun i : ℤ => w0aW2 a (p + 1 / 2) i * waveEvenAbs (waveHat m hm q) i)
        ≤ Real.sqrt 2 * waveEllNorm a p q := by
  set f : ℤ → ℝ := fun i => (w0aW2 a (p + 1 / 2) i * waveEvenAbs (waveHat m hm q) i) ^ 2 with hf
  have hev : ∀ i, f (-i) = f i := fun i => by simp [hf, w0aW2_neg, waveEvenAbs_neg]
  have h0 : f 0 = 0 := by simp [hf, waveEvenAbs_zero]
  have hg : ∀ n : ℕ+, f ((n : ℕ) : ℤ) = (ellWeight a (p + 1 / 2) n * |waveHat m hm q n|) ^ 2 := by
    intro n
    simp only [hf, w0aW2_pnat, waveEvenAbs_pnat]
  have hle : ∀ n : ℕ+, f ((n : ℕ) : ℤ) ≤ (ellWeight a p n * q n) ^ 2 := by
    intro n
    rw [hg n]
    have hl : 0 < lam m hm n := lt_of_lt_of_le (by positivity) (wave_pnat_le_lam m hm n)
    have hn : (0 : ℝ) < n := by positivity
    have hs2 : ellWeight a (p + 1 / 2) n ^ 2 = ellWeight a p n ^ 2 * n := by
      rw [wave_ellWeight_add_half, mul_pow, Real.sq_sqrt hn.le]
    have hh2 : (waveHat m hm q n) ^ 2 = q n ^ 2 / lam m hm n := by
      unfold waveHat; rw [div_pow, Real.sq_sqrt hl.le]
    have hdiv : (n : ℝ) / lam m hm n ≤ 1 := (div_le_one hl).2 (wave_pnat_le_lam m hm n)
    rw [mul_pow, sq_abs, hs2, hh2]
    calc ellWeight a p n ^ 2 * n * (q n ^ 2 / lam m hm n)
        = ellWeight a p n ^ 2 * q n ^ 2 * ((n : ℝ) / lam m hm n) := by ring
      _ ≤ ellWeight a p n ^ 2 * q n ^ 2 * 1 := by gcongr
      _ = (ellWeight a p n * q n) ^ 2 := by ring
  have hgsum : Summable fun n : ℕ+ => f ((n : ℕ) : ℤ) :=
    Summable.of_nonneg_of_le (fun n => by simp only [hf]; exact sq_nonneg _) hle hq
  have hS := w0aHasSum_int_even_pnat hev h0 hgsum.hasSum
  refine ⟨hS.summable, ?_⟩
  have hbound : ∑' n : ℕ+, f ((n : ℕ) : ℤ) ≤ ∑' n : ℕ+, (ellWeight a p n * q n) ^ 2 :=
    Summable.tsum_le_tsum hle hgsum hq
  unfold w0aL2 waveEllNorm
  have hL : ∑' i : ℤ, (w0aW2 a (p + 1 / 2) i * waveEvenAbs (waveHat m hm q) i) ^ 2 =
      2 * ∑' n : ℕ+, f ((n : ℕ) : ℤ) := hS.tsum_eq
  rw [hL, ← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  exact Real.sqrt_le_sqrt (by linarith)

end KAM.Wave

end
