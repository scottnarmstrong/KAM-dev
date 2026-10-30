/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.Analysis.PSeries
public import KAM.Wave.Algebra.Young

/-!
# Two-sided weighted spaces (blueprint `bpW:w1:twosided-transport`, `bpW:w0:twosided`)

Infrastructure used by several nodes; the dependency graph is still being built.

For `a ≥ 0`, `s ∈ ℝ` the space `ℓ^{a,s}_b` of complex sequences `c : ℤ → ℂ` with
`∑_l (⟨l⟩^s e^{a|l|} |c_l|)² < ∞` is the predicate `WaveTwoMem a s c`, with norm
`waveTwoNorm a s c`.
It is transported isometrically to `lp (fun _ : ℤ => ℂ) 2` by `c ↦ (ω_{a,s}(l) c_l)_l`
(`waveTwoToLp`, `waveTwoToLp_norm`, `waveTwoOfLp`).

* `KAM.Wave.waveJap`, `KAM.Wave.waveTwoWeight` : `⟨l⟩` and `ω^b_{a,s}(l) = ⟨l⟩^s e^{a|l|}`;
* `KAM.Wave.wave_jap_hasSum` : `∑_l ⟨l⟩^{-σ} = 1 + 2 ∑_{k ≥ 1} k^{-σ}`;
* `KAM.Wave.waveAlgConst` : `K_s = 2^s (1 + 2 ζ(2s))^{1/2}`;
* `KAM.Wave.wave_l1_le_of_mem` : `ℓ¹` control by the weighted `ℓ²` norm
  (blueprint `bpW:w1:young` (ii)).
-/

@[expose] public noncomputable section

namespace KAM.Wave

/-- The Japanese bracket `⟨l⟩ = max 1 |l|` (blueprint `bpW:w0:twosided`). -/
def waveJap (l : ℤ) : ℝ := max 1 |(l : ℝ)|

theorem waveJap_pos (l : ℤ) : 0 < waveJap l := lt_max_of_lt_left one_pos

theorem one_le_waveJap (l : ℤ) : 1 ≤ waveJap l := le_max_left _ _

theorem waveJap_neg (l : ℤ) : waveJap (-l) = waveJap l := by simp [waveJap]

theorem waveJap_nat_succ (n : ℕ) : waveJap ((n : ℤ) + 1) = (n : ℝ) + 1 := by
  have h : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
  simp only [waveJap]
  push_cast
  rw [abs_of_nonneg h, max_eq_right (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])]

theorem waveJap_neg_nat_succ (n : ℕ) : waveJap (-((n : ℤ) + 1)) = (n : ℝ) + 1 := by
  rw [waveJap_neg, waveJap_nat_succ]

theorem waveJap_zero : waveJap 0 = 1 := by simp [waveJap]

/-- `∑_{l ∈ ℤ} ⟨l⟩^{-σ} = 1 + 2 ∑_{k ≥ 1} k^{-σ}` (blueprint `bpW:w1:young` (ii)). -/
theorem wave_jap_hasSum {σ : ℝ} (hσ : 1 < σ) :
    HasSum (fun l : ℤ => waveJap l ^ (-σ))
      (1 + 2 * ∑' n : ℕ, ((n : ℝ) + 1) ^ (-σ)) := by
  have hn : Summable fun n : ℕ => ((n : ℝ) + 1) ^ (-σ) := by
    have := (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr (show -σ < -1 by linarith))
    simpa using this
  have e1 : (fun n : ℕ => waveJap (((n + 1 : ℕ) : ℤ)) ^ (-σ)) = fun n : ℕ => ((n : ℝ) + 1) ^ (-σ) :=
    funext fun n => by rw [Nat.cast_succ, waveJap_nat_succ]
  have e2 : (fun n : ℕ => waveJap (-((n : ℤ) + 1)) ^ (-σ)) = fun n : ℕ => ((n : ℝ) + 1) ^ (-σ) :=
    funext fun n => by rw [waveJap_neg_nat_succ]
  have h1 : HasSum (fun n : ℕ => waveJap ((n : ℤ)) ^ (-σ))
      (∑' n : ℕ, ((n : ℝ) + 1) ^ (-σ) + 1) := by
    have h := (hasSum_nat_add_iff (f := fun n : ℕ => waveJap ((n : ℤ)) ^ (-σ)) 1).mp
      (by rw [e1]; exact hn.hasSum)
    simpa [waveJap_zero] using h
  have h2 : HasSum (fun n : ℕ => waveJap (-((n : ℤ) + 1)) ^ (-σ))
      (∑' n : ℕ, ((n : ℝ) + 1) ^ (-σ)) := by
    rw [e2]; exact hn.hasSum
  have h3 := HasSum.of_nat_of_neg_add_one (f := fun l : ℤ => waveJap l ^ (-σ)) h1 h2
  have e : (∑' n : ℕ, ((n : ℝ) + 1) ^ (-σ) + 1) + ∑' n : ℕ, ((n : ℝ) + 1) ^ (-σ) =
      1 + 2 * ∑' n : ℕ, ((n : ℝ) + 1) ^ (-σ) := by ring
  rwa [e] at h3


/-- The weight `ω^b_{a,s}(l) = ⟨l⟩^s e^{a|l|}` of `ℓ^{a,s}_b`
(blueprint `bpW:w1:twosided-transport`). -/
def waveTwoWeight (a s : ℝ) (l : ℤ) : ℝ :=
  waveJap l ^ s * Real.exp (a * |(l : ℝ)|)

theorem waveTwoWeight_pos (a s : ℝ) (l : ℤ) : 0 < waveTwoWeight a s l :=
  mul_pos (Real.rpow_pos_of_pos (waveJap_pos l) s) (Real.exp_pos _)

theorem one_le_waveTwoWeight {a s : ℝ} (ha : 0 ≤ a) (hs : 0 ≤ s) (l : ℤ) :
    1 ≤ waveTwoWeight a s l :=
  one_le_mul_of_one_le_of_one_le (Real.one_le_rpow (one_le_waveJap l) hs)
    (Real.one_le_exp (mul_nonneg ha (abs_nonneg _)))

/-- Membership in `ℓ^{a,s}_b` (blueprint `bpW:w0:twosided`): `∑_l (ω_{a,s}(l) |c_l|)² < ∞`. -/
def WaveTwoMem (a s : ℝ) (c : ℤ → ℂ) : Prop :=
  Summable fun l => (waveTwoWeight a s l * ‖c l‖) ^ 2

/-- The norm `‖c‖_{a,s}` of `ℓ^{a,s}_b` (meaningful when `WaveTwoMem a s c`). -/
def waveTwoNorm (a s : ℝ) (c : ℤ → ℂ) : ℝ :=
  √(∑' l, (waveTwoWeight a s l * ‖c l‖) ^ 2)

theorem waveTwoNorm_nonneg (a s : ℝ) (c : ℤ → ℂ) : 0 ≤ waveTwoNorm a s c := Real.sqrt_nonneg _

theorem waveTwoNorm_sq (a s : ℝ) (c : ℤ → ℂ) :
    waveTwoNorm a s c ^ 2 = ∑' l, (waveTwoWeight a s l * ‖c l‖) ^ 2 :=
  Real.sq_sqrt (tsum_nonneg fun _ => sq_nonneg _)

theorem waveTwoMemlp {a s : ℝ} {c : ℤ → ℂ} (h : WaveTwoMem a s c) :
    Memℓp (fun l => (waveTwoWeight a s l : ℂ) * c l) 2 := by
  rw [memℓp_gen_iff (by norm_num)]
  unfold WaveTwoMem at h
  simpa [norm_mul, abs_of_pos (waveTwoWeight_pos a s _), Real.rpow_two] using h

/-- The transport `c ↦ (ω_{a,s}(l) c_l)_l` into `ℓ²(ℤ; ℂ)`
(blueprint `bpW:w1:twosided-transport`). -/
def waveTwoToLp {a s : ℝ} {c : ℤ → ℂ} (h : WaveTwoMem a s c) : lp (fun _ : ℤ => ℂ) 2 :=
  ⟨fun l => (waveTwoWeight a s l : ℂ) * c l, waveTwoMemlp h⟩

/-- The transport is an isometry (blueprint `bpW:w1:twosided-transport`). -/
theorem waveTwoToLp_norm {a s : ℝ} {c : ℤ → ℂ} (h : WaveTwoMem a s c) :
    ‖waveTwoToLp h‖ = waveTwoNorm a s c := by
  rw [lp.norm_eq_tsum_rpow (by norm_num)]
  simp only [waveTwoToLp, waveTwoNorm, ENNReal.toReal_ofNat, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (waveTwoWeight_pos a s _), Real.rpow_two, one_div,
    Real.sqrt_eq_rpow]

/-- The inverse transport: an `ℓ²` element `f` gives the sequence `c_l = f_l / ω_{a,s}(l)`. -/
theorem waveTwoMem_of_lp (a s : ℝ) (f : lp (fun _ : ℤ => ℂ) 2) :
    WaveTwoMem a s (fun l => f l / (waveTwoWeight a s l : ℂ)) := by
  have h := (memℓp_gen_iff (p := 2) (by norm_num)).mp f.2
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at h
  have e : ∀ l, waveTwoWeight a s l * ‖f l / (waveTwoWeight a s l : ℂ)‖ = ‖f l‖ := fun l => by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (waveTwoWeight_pos a s l)]
    field_simp [(waveTwoWeight_pos a s l).ne']
  unfold WaveTwoMem
  exact h.congr fun l => by rw [e]

/-- `∑_{l ∈ ℤ} ⟨l⟩^{-2s} = 1 + 2 ζ(2s)` for `s > 1/2` (blueprint `bpW:w1:young` (ii)). -/
theorem wave_jap_hasSum_zeta {s : ℝ} (hs : 1 / 2 < s) :
    HasSum (fun l : ℤ => waveJap l ^ (-(2 * s)))
      (1 + 2 * (riemannZeta ((2 * s : ℝ) : ℂ)).re) := by
  have h1 : 1 < 2 * s := by linarith
  have h := wave_jap_hasSum h1
  have hz := zeta_eq_tsum_one_div_nat_add_one_cpow (s := ((2 * s : ℝ) : ℂ)) (by simpa using h1)
  have e : riemannZeta ((2 * s : ℝ) : ℂ) = ((∑' n : ℕ, ((n : ℝ) + 1) ^ (-(2 * s)) : ℝ) : ℂ) := by
    rw [hz, Complex.ofReal_tsum]
    refine tsum_congr fun n => ?_
    have hn : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
    rw [Real.rpow_neg hn, Complex.ofReal_inv, Complex.ofReal_cpow hn, one_div]
    push_cast
    rfl
  rwa [e, Complex.ofReal_re]

/-- The algebra constant `K_s = 2^s (1 + 2 ζ(2s))^{1/2}` (blueprint `bpW:w1:algebra`). -/
def waveAlgConst (s : ℝ) : ℝ :=
  2 ^ s * √(1 + 2 * (riemannZeta ((2 * s : ℝ) : ℂ)).re)

theorem waveAlgConst_nonneg (s : ℝ) : 0 ≤ waveAlgConst s :=
  mul_nonneg (Real.rpow_nonneg (by norm_num) s) (Real.sqrt_nonneg _)

theorem waveTwoWeight_zero_left (s : ℝ) (l : ℤ) : waveTwoWeight 0 s l = waveJap l ^ s := by
  simp [waveTwoWeight]

theorem waveTwoWeight_mono {a b : ℝ} (hab : a ≤ b) (s : ℝ) (l : ℤ) :
    waveTwoWeight a s l ≤ waveTwoWeight b s l :=
  mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hab (abs_nonneg _)))
    (Real.rpow_nonneg (waveJap_pos l).le s)

theorem WaveTwoMem.of_weight_le {a b s : ℝ} (hab : a ≤ b) {c : ℤ → ℂ} (h : WaveTwoMem b s c) :
    WaveTwoMem a s c :=
  Summable.of_nonneg_of_le (fun _ => sq_nonneg _)
    (fun l => pow_le_pow_left₀
      (mul_nonneg (waveTwoWeight_pos a s l).le (norm_nonneg _))
      (mul_le_mul_of_nonneg_right (waveTwoWeight_mono hab s l) (norm_nonneg _)) 2) h

theorem waveTwoNorm_mono {a b s : ℝ} (hab : a ≤ b) {c : ℤ → ℂ} (h : WaveTwoMem b s c) :
    waveTwoNorm a s c ≤ waveTwoNorm b s c :=
  Real.sqrt_le_sqrt
    ((h.of_weight_le hab).tsum_le_tsum
      (fun l => pow_le_pow_left₀
        (mul_nonneg (waveTwoWeight_pos a s l).le (norm_nonneg _))
        (mul_le_mul_of_nonneg_right (waveTwoWeight_mono hab s l) (norm_nonneg _)) 2) h)

/-- Weighted `ℓ¹` control: for `s > 1/2`, `a ≥ 0`, `Y ∈ ℓ^{a,s}_b` the sequence `e^{a|l|} |Y_l|` is
in `ℓ¹` with `∑ e^{a|l|}|Y_l| ≤ (1 + 2ζ(2s))^{1/2} ‖Y‖_{a,s}` (Cauchy–Schwarz against `⟨l⟩^{-s}`,
blueprint `bpW:w1:young` (ii) and Step `stepW:w0n:young`). -/
theorem wave_expl1_le {a s : ℝ} (hs : 1 / 2 < s) {Y : ℤ → ℂ} (hY : WaveTwoMem a s Y) :
    Summable (fun l : ℤ => Real.exp (a * |(l : ℝ)|) * ‖Y l‖) ∧
    ∑' l : ℤ, Real.exp (a * |(l : ℝ)|) * ‖Y l‖ ≤
      √(1 + 2 * (riemannZeta ((2 * s : ℝ) : ℂ)).re) * waveTwoNorm a s Y := by
  have hv : Summable fun l : ℤ => (waveJap l ^ (-s)) ^ 2 := by
    have := (wave_jap_hasSum_zeta hs).summable
    refine this.congr fun l => ?_
    rw [← Real.rpow_natCast, ← Real.rpow_mul (waveJap_pos l).le]
    congr 1
    push_cast
    ring
  have hvs : ∑' l : ℤ, (waveJap l ^ (-s)) ^ 2 = 1 + 2 * (riemannZeta ((2 * s : ℝ) : ℂ)).re := by
    rw [← (wave_jap_hasSum_zeta hs).tsum_eq]
    refine tsum_congr fun l => ?_
    rw [← Real.rpow_natCast, ← Real.rpow_mul (waveJap_pos l).le]
    congr 1
    push_cast
    ring
  have hu : ∀ l, waveTwoWeight a s l * ‖Y l‖ * waveJap l ^ (-s) =
      Real.exp (a * |(l : ℝ)|) * ‖Y l‖ := fun l => by
    simp only [waveTwoWeight]
    calc waveJap l ^ s * Real.exp (a * |(l : ℝ)|) * ‖Y l‖ * waveJap l ^ (-s)
        = (waveJap l ^ s * waveJap l ^ (-s)) * (Real.exp (a * |(l : ℝ)|) * ‖Y l‖) := by ring
      _ = _ := by
        rw [← Real.rpow_add (waveJap_pos l), add_neg_cancel, Real.rpow_zero, one_mul]
  obtain ⟨hsum, hcs⟩ := wave_tsum_mul_sq_le (u := fun l => waveTwoWeight a s l * ‖Y l‖)
    (v := fun l => waveJap l ^ (-s))
    (fun l => mul_nonneg (waveTwoWeight_pos a s l).le (norm_nonneg _))
    (fun l => Real.rpow_nonneg (waveJap_pos l).le _) hY hv
  simp only [hu] at hsum hcs
  have hN := waveTwoNorm_sq a s Y
  rw [hvs, ← hN] at hcs
  have hZ : 0 ≤ 1 + 2 * (riemannZeta ((2 * s : ℝ) : ℂ)).re := by
    rw [← (wave_jap_hasSum_zeta hs).tsum_eq]
    exact tsum_nonneg fun l => Real.rpow_nonneg (waveJap_pos l).le _
  refine ⟨hsum, ?_⟩
  have := abs_le_of_sq_le_sq' (a := ∑' l : ℤ, Real.exp (a * |(l : ℝ)|) * ‖Y l‖)
    (b := √(1 + 2 * (riemannZeta ((2 * s : ℝ) : ℂ)).re) * waveTwoNorm a s Y)
    (by rw [mul_pow, Real.sq_sqrt hZ]; linarith)
    (mul_nonneg (Real.sqrt_nonneg _) (waveTwoNorm_nonneg _ _ _))
  exact this.2

/-- `ℓ¹` control (blueprint `bpW:w1:young` (ii)): for `s > 1/2`, `a ≥ 0`, `Y ∈ ℓ^{a,s}_b`,
`‖Y‖_{ℓ¹} ≤ (1 + 2ζ(2s))^{1/2} ‖Y‖_{0,s} ≤ (1 + 2ζ(2s))^{1/2} ‖Y‖_{a,s}`. -/
theorem wave_l1_le_of_mem {a s : ℝ} (ha : 0 ≤ a) (hs : 1 / 2 < s) {Y : ℤ → ℂ}
    (hY : WaveTwoMem a s Y) :
    Summable (fun l => ‖Y l‖) ∧
    ∑' l, ‖Y l‖ ≤ √(1 + 2 * (riemannZeta ((2 * s : ℝ) : ℂ)).re) * waveTwoNorm 0 s Y ∧
    √(1 + 2 * (riemannZeta ((2 * s : ℝ) : ℂ)).re) * waveTwoNorm 0 s Y ≤
      √(1 + 2 * (riemannZeta ((2 * s : ℝ) : ℂ)).re) * waveTwoNorm a s Y := by
  obtain ⟨h1, h2⟩ := wave_expl1_le hs (hY.of_weight_le ha)
  simp only [zero_mul, Real.exp_zero, one_mul] at h1 h2
  exact ⟨h1, h2, mul_le_mul_of_nonneg_left (waveTwoNorm_mono ha hY) (Real.sqrt_nonneg _)⟩

/-- For `a, s ≥ 0` a member of `ℓ^{a,s}_b` is square-summable with `‖c‖_{ℓ²} ≤ ‖c‖_{a,s}`
(blueprint `bpW:w0:twosided`). -/
theorem WaveTwoMem.summable_sq {a s : ℝ} (ha : 0 ≤ a) (hs : 0 ≤ s) {c : ℤ → ℂ}
    (hc : WaveTwoMem a s c) : Summable fun l => ‖c l‖ ^ 2 :=
  Summable.of_nonneg_of_le (fun _ => sq_nonneg _)
    (fun l => pow_le_pow_left₀ (norm_nonneg _)
      (le_mul_of_one_le_left (norm_nonneg _) (one_le_waveTwoWeight ha hs l)) 2) hc

/-- The convolution of two members of `ℓ^{a,s}_b`, `a, s ≥ 0`, converges absolutely for every `l`
(blueprint `bpW:w0:twosided`, by Cauchy–Schwarz and `‖·‖_{ℓ²} ≤ ‖·‖_{a,s}`). -/
theorem wave_conv_summable {a s : ℝ} (ha : 0 ≤ a) (hs : 0 ≤ s) {c d : ℤ → ℂ}
    (hc : WaveTwoMem a s c) (hd : WaveTwoMem a s d) (l : ℤ) :
    Summable fun i => ‖c i‖ * ‖d (l - i)‖ := by
  have hd2 : Summable fun i => ‖d (l - i)‖ ^ 2 :=
    ((hd.summable_sq ha hs).comp_injective
      (sub_right_injective : Function.Injective fun i : ℤ => l - i))
  exact (wave_tsum_mul_sq_le (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
    (hc.summable_sq ha hs) hd2).1

/-- Associativity of the convolution on `ℓ^{0,s}_b`, `s > 1/2` (blueprint `bpW:w1:young` (iii)). -/
theorem wave_conv_assoc_of_mem {s : ℝ} (hs : 1 / 2 < s) {c d e : ℤ → ℂ}
    (hc : WaveTwoMem 0 s c) (hd : WaveTwoMem 0 s d) (he : WaveTwoMem 0 s e) (l : ℤ) :
    waveConv (waveConv c d) e l = waveConv c (waveConv d e) l :=
  waveConv_assoc_l1 (wave_l1_le_of_mem le_rfl hs hc).1 (wave_l1_le_of_mem le_rfl hs hd).1
    (wave_l1_le_of_mem le_rfl hs he).1 l

end KAM.Wave
