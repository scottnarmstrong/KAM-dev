/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Algebra.TwoSided

/-!
# The weighted convolution algebra (blueprint `bpW:w1:algebra`, `bpW:w0n:algebra`)

Infrastructure used by several nodes; the dependency graph is still being built.

For `a ≥ 0`, `s ≥ 1` and `c, d ∈ ℓ^{a,s}_b`:
`‖c * d‖_{a,s} ≤ K_s ‖c‖_{a,s} ‖d‖_{a,s}` with `K_s = 2^s (1 + 2ζ(2s))^{1/2}`, every convolution sum
converging absolutely.

* `KAM.Wave.wave_weight_ineq` : Step `stepW:w0n:weight`;
* `KAM.Wave.wave_algebra` : the lemma (blueprint `bpW:w1:algebra`);
* `KAM.Wave.wave_algebra_three` : the three-factor form.
-/

@[expose] public noncomputable section

namespace KAM.Wave

/-- `(x + y)^s ≤ 2^{s-1}(x^s + y^s)` for `s ≥ 1` (Step `stepW:w0n:weight`). -/
theorem wave_add_rpow_le {x y s : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hs : 1 ≤ s) :
    (x + y) ^ s ≤ 2 ^ (s - 1) * (x ^ s + y ^ s) := by
  lift x to NNReal using hx
  lift y to NNReal using hy
  exact_mod_cast NNReal.rpow_add_le_mul_rpow_add_rpow x y hs

/-- `⟨l⟩ ≤ ⟨i⟩ + ⟨l - i⟩` (Step `stepW:w0n:weight`). -/
theorem waveJap_sub_le (l i : ℤ) : waveJap l ≤ waveJap i + waveJap (l - i) := by
  have h1 := le_max_left (1 : ℝ) |(i : ℝ)|
  have h2 := le_max_left (1 : ℝ) |((l - i : ℤ) : ℝ)|
  have h3 : |(l : ℝ)| ≤ |(i : ℝ)| + |((l - i : ℤ) : ℝ)| := by
    have := abs_add_le (i : ℝ) ((l - i : ℤ) : ℝ)
    simpa using this
  have h4 := le_max_right (1 : ℝ) |(i : ℝ)|
  have h5 := le_max_right (1 : ℝ) |((l - i : ℤ) : ℝ)|
  exact max_le (by simp only [waveJap]; linarith) (by simp only [waveJap]; linarith)

/-- The weight inequality `ω_{a,s}(l) ≤ 2^{s-1}(ω_{a,s}(i) e^{a|l-i|} + ω_{a,s}(l-i) e^{a|i|})`
(Step `stepW:w0n:weight`). -/
theorem wave_weight_ineq {a s : ℝ} (ha : 0 ≤ a) (hs : 1 ≤ s) (l i : ℤ) :
    waveTwoWeight a s l ≤ 2 ^ (s - 1) *
      (waveTwoWeight a s i * Real.exp (a * |((l - i : ℤ) : ℝ)|) +
        waveTwoWeight a s (l - i) * Real.exp (a * |(i : ℝ)|)) := by
  have hE : Real.exp (a * |(l : ℝ)|) ≤
      Real.exp (a * |(i : ℝ)|) * Real.exp (a * |((l - i : ℤ) : ℝ)|) := by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have := abs_add_le (i : ℝ) ((l - i : ℤ) : ℝ)
    have h3 : |(l : ℝ)| ≤ |(i : ℝ)| + |((l - i : ℤ) : ℝ)| := by simpa using this
    nlinarith
  have hJ : waveJap l ^ s ≤ 2 ^ (s - 1) * (waveJap i ^ s + waveJap (l - i) ^ s) :=
    (Real.rpow_le_rpow (waveJap_pos l).le (waveJap_sub_le l i) (by linarith)).trans
      (wave_add_rpow_le (waveJap_pos i).le (waveJap_pos _).le hs)
  have h2 : (0 : ℝ) ≤ 2 ^ (s - 1) := by positivity
  calc waveTwoWeight a s l = waveJap l ^ s * Real.exp (a * |(l : ℝ)|) := rfl
    _ ≤ (2 ^ (s - 1) * (waveJap i ^ s + waveJap (l - i) ^ s)) *
        (Real.exp (a * |(i : ℝ)|) * Real.exp (a * |((l - i : ℤ) : ℝ)|)) :=
      mul_le_mul hJ hE (Real.exp_pos _).le
        (mul_nonneg h2 (add_nonneg (Real.rpow_nonneg (waveJap_pos i).le _)
          (Real.rpow_nonneg (waveJap_pos _).le _)))
    _ = _ := by simp only [waveTwoWeight]; ring

/-- Scaling of an `ℓ²` norm on `ℤ`. -/
theorem wave_sqrt_tsum_smul {f : ℤ → ℝ} {k : ℝ} (hk : 0 ≤ k) (hf : Summable fun i => f i ^ 2) :
    Summable (fun i => (k * f i) ^ 2) ∧ √(∑' i, (k * f i) ^ 2) = k * √(∑' i, f i ^ 2) := by
  have e : ∀ i, (k * f i) ^ 2 = k ^ 2 * f i ^ 2 := fun i => by ring
  simp only [e]
  refine ⟨hf.mul_left _, ?_⟩
  rw [tsum_mul_left, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hk]

/-- The convolution algebra (blueprint `bpW:w1:algebra`, `bpW:w0n:algebra`): for `a ≥ 0`, `s ≥ 1`
and `c, d ∈ ℓ^{a,s}_b`, every convolution sum converges absolutely, `c * d ∈ ℓ^{a,s}_b` and
`‖c * d‖_{a,s} ≤ K_s ‖c‖_{a,s} ‖d‖_{a,s}`, `K_s = 2^s (1 + 2ζ(2s))^{1/2}`. -/
theorem wave_algebra {a s : ℝ} (ha : 0 ≤ a) (hs : 1 ≤ s) {c d : ℤ → ℂ}
    (hc : WaveTwoMem a s c) (hd : WaveTwoMem a s d) :
    (∀ l, Summable fun i => ‖c i‖ * ‖d (l - i)‖) ∧ WaveTwoMem a s (waveConv c d) ∧
    waveTwoNorm a s (waveConv c d) ≤ waveAlgConst s * waveTwoNorm a s c * waveTwoNorm a s d := by
  have hs' : 1 / 2 < s := by linarith
  set k : ℝ := 2 ^ (s - 1) with hk
  have hk0 : 0 ≤ k := by positivity
  obtain ⟨hCp1, hCp⟩ := wave_expl1_le hs' hc
  obtain ⟨hDp1, hDp⟩ := wave_expl1_le hs' hd
  have hnn : ∀ (e : ℤ → ℂ) (i : ℤ), 0 ≤ waveTwoWeight a s i * ‖e i‖ := fun e (i : ℤ) =>
    mul_nonneg (waveTwoWeight_pos a s i).le (norm_nonneg _)
  have hnE : ∀ (e : ℤ → ℂ) (i : ℤ), 0 ≤ Real.exp (a * |(i : ℝ)|) * ‖e i‖ := fun e (i : ℤ) =>
    mul_nonneg (Real.exp_pos _).le (norm_nonneg _)
  obtain ⟨hP1, hP2, hP3⟩ := wave_young_real (hnn c) (hnE d) hc hDp1
  obtain ⟨hQ1, hQ2, hQ3⟩ := wave_young_real (hnn d) (hnE c) hd hCp1
  -- pointwise bound
  have hpt : ∀ l i : ℤ, waveTwoWeight a s l * (‖c i‖ * ‖d (l - i)‖) ≤
      k * ((waveTwoWeight a s i * ‖c i‖) * (Real.exp (a * |((l - i : ℤ) : ℝ)|) * ‖d (l - i)‖) +
        (Real.exp (a * |(i : ℝ)|) * ‖c i‖) * (waveTwoWeight a s (l - i) * ‖d (l - i)‖)) :=
    fun l i => by
      have := mul_le_mul_of_nonneg_right (wave_weight_ineq ha hs l i)
        (mul_nonneg (norm_nonneg (c i)) (norm_nonneg (d (l - i))))
      calc _ ≤ _ := this
        _ = _ := by ring
  have hQ1' : ∀ l : ℤ, Summable fun i : ℤ => (Real.exp (a * |(i : ℝ)|) * ‖c i‖) *
      (waveTwoWeight a s (l - i) * ‖d (l - i)‖) := fun l =>
    waveConv_summable_comm (c := fun i : ℤ => waveTwoWeight a s i * ‖d i‖)
      (d := fun i : ℤ => Real.exp (a * |(i : ℝ)|) * ‖c i‖) (hQ1 l)
  have hT : ∀ l : ℤ, Summable fun i : ℤ => ‖c i‖ * ‖d (l - i)‖ := fun l => by
    have hb : Summable fun i : ℤ => waveTwoWeight a s l * (‖c i‖ * ‖d (l - i)‖) :=
      Summable.of_nonneg_of_le
        (fun i => mul_nonneg (waveTwoWeight_pos a s l).le
          (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
        (hpt l) (((hP1 l).add (hQ1' l)).mul_left k)
    have := hb.mul_left (waveTwoWeight a s l)⁻¹
    refine this.congr fun i => ?_
    field_simp [(waveTwoWeight_pos a s l).ne']
  -- bound for the weighted conv
  set P : ℤ → ℝ := waveConv (fun i => waveTwoWeight a s i * ‖c i‖)
    (fun i => Real.exp (a * |(i : ℝ)|) * ‖d i‖) with hPdef
  set Q : ℤ → ℝ := waveConv (fun i => waveTwoWeight a s i * ‖d i‖)
    (fun i => Real.exp (a * |(i : ℝ)|) * ‖c i‖) with hQdef
  have hbound : ∀ l : ℤ, waveTwoWeight a s l * ‖waveConv c d l‖ ≤ k * P l + k * Q l := fun l => by
    have h1 := norm_waveConv_le (c := c) (d := d) l (hT l)
    have h2 : waveTwoWeight a s l * ∑' i, ‖c i‖ * ‖d (l - i)‖ ≤ k * (P l + Q l) := by
      rw [← tsum_mul_left]
      have := ((hP1 l).add (hQ1' l)).mul_left k
      calc _ ≤ ∑' i, k * ((waveTwoWeight a s i * ‖c i‖) *
            (Real.exp (a * |((l - i : ℤ) : ℝ)|) * ‖d (l - i)‖) +
            (Real.exp (a * |(i : ℝ)|) * ‖c i‖) * (waveTwoWeight a s (l - i) * ‖d (l - i)‖)) :=
            ((hT l).mul_left _).tsum_le_tsum (hpt l) this
        _ = k * (P l + Q l) := by
          rw [tsum_mul_left, ((hP1 l).tsum_add (hQ1' l)), hPdef, hQdef]
          congr 2
          exact waveConv_comm (fun i : ℤ => Real.exp (a * |(i : ℝ)|) * ‖c i‖)
            (fun i : ℤ => waveTwoWeight a s i * ‖d i‖) l
    have h3 := mul_le_mul_of_nonneg_left h1 (waveTwoWeight_pos a s l).le
    calc _ ≤ waveTwoWeight a s l * ∑' i, ‖c i‖ * ‖d (l - i)‖ := h3
      _ ≤ k * (P l + Q l) := h2
      _ = _ := by ring
  have hP0 : ∀ l, 0 ≤ P l := fun l => tsum_nonneg fun i =>
    mul_nonneg (hnn c i) (mul_nonneg (Real.exp_pos _).le (norm_nonneg _))
  have hQ0 : ∀ l, 0 ≤ Q l := fun l => tsum_nonneg fun i =>
    mul_nonneg (hnn d i) (mul_nonneg (Real.exp_pos _).le (norm_nonneg _))
  obtain ⟨hf2, hfs⟩ := wave_sqrt_tsum_smul hk0 hP2
  obtain ⟨hg2, hgs⟩ := wave_sqrt_tsum_smul hk0 hQ2
  obtain ⟨hsum, hmink⟩ := wave_l2_add (f := fun l => k * P l) (g := fun l => k * Q l)
    (fun l => mul_nonneg hk0 (hP0 l)) (fun l => mul_nonneg hk0 (hQ0 l)) hf2 hg2
  have hsq : ∀ l : ℤ, (waveTwoWeight a s l * ‖waveConv c d l‖) ^ 2 ≤ (k * P l + k * Q l) ^ 2 :=
    fun l => pow_le_pow_left₀ (mul_nonneg (waveTwoWeight_pos a s l).le (norm_nonneg _)) (hbound l) 2
  have hmem : WaveTwoMem a s (waveConv c d) :=
    Summable.of_nonneg_of_le (fun _ => sq_nonneg _) hsq hsum
  refine ⟨hT, hmem, ?_⟩
  have hDs : 0 ≤ ∑' i : ℤ, Real.exp (a * |(i : ℝ)|) * ‖d i‖ := tsum_nonneg fun i => hnE d i
  have hCs : 0 ≤ ∑' i : ℤ, Real.exp (a * |(i : ℝ)|) * ‖c i‖ := tsum_nonneg fun i => hnE c i
  have hPs : √(∑' l, P l ^ 2) ≤
      (∑' i : ℤ, Real.exp (a * |(i : ℝ)|) * ‖d i‖) * waveTwoNorm a s c := by
    calc _ ≤ √((∑' i : ℤ, Real.exp (a * |(i : ℝ)|) * ‖d i‖) ^ 2 *
          ∑' i : ℤ, (waveTwoWeight a s i * ‖c i‖) ^ 2) := Real.sqrt_le_sqrt hP3
      _ = _ := by rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hDs]; rfl
  have hQs : √(∑' l, Q l ^ 2) ≤
      (∑' i : ℤ, Real.exp (a * |(i : ℝ)|) * ‖c i‖) * waveTwoNorm a s d := by
    calc _ ≤ √((∑' i : ℤ, Real.exp (a * |(i : ℝ)|) * ‖c i‖) ^ 2 *
          ∑' i : ℤ, (waveTwoWeight a s i * ‖d i‖) ^ 2) := Real.sqrt_le_sqrt hQ3
      _ = _ := by rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hCs]; rfl
  have hnorm : waveTwoNorm a s (waveConv c d) ≤
      √(∑' l, (k * P l) ^ 2) + √(∑' l, (k * Q l) ^ 2) := by
    refine le_trans (Real.sqrt_le_sqrt ?_) hmink
    refine hmem.tsum_le_tsum ?_ hsum
    intro l
    have := hsq l
    simpa [add_comm] using this
  have e2 : waveAlgConst s = 2 * k * √(1 + 2 * (riemannZeta ((2 * s : ℝ) : ℂ)).re) := by
    have : (2 : ℝ) ^ s = 2 * k := by
      rw [hk, Real.rpow_sub two_pos, Real.rpow_one]; ring
    rw [waveAlgConst, this]
  have hNc := waveTwoNorm_nonneg a s c
  have hNd := waveTwoNorm_nonneg a s d
  have t1 : k * ((∑' i : ℤ, Real.exp (a * |(i : ℝ)|) * ‖d i‖) * waveTwoNorm a s c) ≤
      k * (√(1 + 2 * (riemannZeta ((2 * s : ℝ) : ℂ)).re) * waveTwoNorm a s d * waveTwoNorm a s c) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hDp hNc) hk0
  have t2 : k * ((∑' i : ℤ, Real.exp (a * |(i : ℝ)|) * ‖c i‖) * waveTwoNorm a s d) ≤
      k * (√(1 + 2 * (riemannZeta ((2 * s : ℝ) : ℂ)).re) * waveTwoNorm a s c * waveTwoNorm a s d) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hCp hNd) hk0
  rw [hfs, hgs] at hnorm
  rw [e2]
  nlinarith [mul_le_mul_of_nonneg_left hPs hk0, mul_le_mul_of_nonneg_left hQs hk0]

/-- The three-factor convolution algebra bound (blueprint `bpW:w1:algebra`):
`‖c * d * e‖_{a,s} ≤ K_s² ‖c‖ ‖d‖ ‖e‖`, with `c * d * e = (c * d) * e`. -/
theorem wave_algebra_three {a s : ℝ} (ha : 0 ≤ a) (hs : 1 ≤ s) {c d e : ℤ → ℂ}
    (hc : WaveTwoMem a s c) (hd : WaveTwoMem a s d) (he : WaveTwoMem a s e) :
    WaveTwoMem a s (waveConv (waveConv c d) e) ∧
    waveTwoNorm a s (waveConv (waveConv c d) e) ≤
      waveAlgConst s ^ 2 * waveTwoNorm a s c * waveTwoNorm a s d * waveTwoNorm a s e := by
  obtain ⟨-, h1, h2⟩ := wave_algebra ha hs hc hd
  obtain ⟨-, h3, h4⟩ := wave_algebra ha hs h1 he
  refine ⟨h3, h4.trans ?_⟩
  have hK := waveAlgConst_nonneg s
  have := mul_le_mul_of_nonneg_left h2 hK
  have hNe := waveTwoNorm_nonneg a s e
  nlinarith [mul_le_mul_of_nonneg_right this hNe]

end KAM.Wave

end
